(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec - tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(*
  Invariants:
  -----------
  
    - object lengths should be updated as early as possible to prevent unsoundness, 
      as it may be that
      (cast) (x + y) != (cast) x + (cast) y
      
      For concrete cases this might not be too important, as we get the final value
      by constant propagation, but we don't know whether we are having a constant when
      applying an operation, so best is to record lengths properly, it's not that hard after all.
       
*)

open Str
open List
open Int64

open Types
open Utils
open Solver

(******************************************************************)
(** {1 Symbolic Arithmetic Expression Manipulation}               *)
(******************************************************************)

(* FIXME: we loose precision, forced by the ocaml Int64 ugliness. *)
let rec getIntVal : exp -> int option = fun e -> match arithFold e with
  | Int (ival, _) -> Some (Int64.to_int ival)
  | Range (e', _, _, _) -> getIntVal e'
  | _ -> None

let op : string -> exp -> exp -> exp = fun op a b ->
  (* debug ("op, op: " ^ op);
  debug ("op, a: " ^ dump a);
  debug ("op, b: " ^ dump b); *)
  if isSpecialLen a b then Unknown else
    (* fail ("op: special values not allowed: " ^ dump a ^ ", " ^ dump b); *)
  arithSimplify (Sym ((op, Infix), [a; b], Unknown, freshDet ()))

let addLen : len -> len -> len = fun a b ->
  match (a, b) with
    | (Unknown, _) | (_, Unknown) -> Unknown
    | (All, _) | (_, All) -> Unknown
    | (x, y) -> op "+" x y

let ptrLen = Sym (("ptrLen", Prefix), [], Unknown, freshDet ())

let rec getLen : exp -> len = fun e -> 
  (* debug ("getLen, e = " ^ dump e); *)
  match e with
    | Int (_, len) -> len
    | String s -> Int (Int64.of_int (String.length s / 2), Unknown)
    (* | Sym (_, _, Unknown, _) -> Unknown *)
    (* | Sym (_, _, l, _) when isConcrete l -> l *) 
    | Sym (_, _, _, _) -> Sym (("len", Prefix), [e], Unknown, freshDet ())
    | Range (_, _, All, _) -> Unknown (* FIXME: Shouldn't this be flagged in the first place? *)
    | Range (_, _, len, _) -> len 
    | Concat (es, _) ->
        let lens = map getLen es in
        fold_left addLen zero lens
    | Struct (_, _, l, _) -> l
    | Array (_, l, _) -> l
    | Ptr (_, _) -> ptrLen
    | _ -> fail ("getLen: unexpected expression: " ^ dump e)

let getLenLen : exp -> len = fun e ->
  match getLen e with
    | Unknown -> Unknown
    | l -> getLen l

(* 
  Used in several places:
  
  - to give lengths to formal arguments in [Transform], there we need to strip it all 
  - in [mkVar]
*)
let getRealLen = function
  | Sym(_, _, l, _) -> l
  | e -> getLen e

let getRealLenLen e = match getRealLen e with
  | Unknown -> fail "getRealLenLen: unknown length"
  | l -> getRealLen l

let setLen : exp -> exp -> exp = fun e l -> 
  match e with
      | Int (ival, Unknown) -> Int (ival, l)
      (* | String _ as s -> Range (s, zero, l) *)
      | Sym (sym, args, Unknown, tag) -> Sym (sym, args, l, tag)
      (* | Range (e, f, _) -> Range (e, f, l) *)
      | Struct (fields, attrs, Unknown, e_old) -> Struct (fields, attrs, l, e_old)
      | Array (elems, Unknown, eltSize) -> Array (elems, l, eltSize)
        (* | Ptr _ as p -> p (* silently ignoring pointer lengths *) 
      | Concat _ as e -> e (* silently ignore *) *) 
        (* | _ -> fail "setLen: unexpected expression on stack" *)
      | e -> e (* silently ignoring concats, pointers and expressions that already have length *)


let getStep : offset list -> exp = comp snd last

let equalOffset : offset -> offset -> pbool = function (oVal1, step1) -> function (oVal2, step2) ->
  let eqVal = match oVal1, oVal2 with
    | Index i, Index j -> i = j
    | Flat a, Flat b -> equalLen a b
    | Field f, Field g -> f = g
    | Attr f, Attr g -> f = g
    | _ -> false
  in
  eqVal && equalLen step1 step2

let isZeroOffsetVal : offsetVal -> bool = function
	| Index 0 -> true
	| Flat z when equal zero z -> true
  | _ -> false

let isZeroOffset : offset -> bool = function (ov, _) -> isZeroOffsetVal ov

let isFieldOffsetVal : offsetVal -> bool = function
  | Field _ -> true
  | _ -> false

(*
  We copy the tag id, but change all tags to deterministic, by the logic that variable references are deterministic.
*)
let mkVar : string -> exp -> exp = fun s e ->
  match getTag e with
    | NoTag -> Sym (("var", Prefix), [String s], getRealLen e, freshDet ())
    | tag   -> Sym (("var", Prefix), [String s], getRealLen e, Det (tagNum tag))

let mkLet : exp -> exp -> exp = fun pat e ->
  Sym (("let", Prefix), [pat; e], Unknown, freshDet ())

(*************************************************)
(** {1 Simplification} *)
(*************************************************)

(**
  Simplifies an expression. 
  Currently following transformations types are performed, given suitable conditions:
  - [Range(String) -> String]
  - [Range(Range(X)) -> Range(X)]
  - [Range(X) -> X]
  - [Concat(Range(X), Range(X)) -> Range(X)]
  - [Concat(String, String) -> String]
  - [Range(Concat(X, Y)) -> Concat(X)]
    
  Assumes that all subexpressions have already been simplified.
  
  Accepts ranges that do not fulfill the invariant. The behaviour then is as follows: if length is not [All],
  the parts of the range that are outside of the expression are filled with [undef]. If length is [All] and position
  is not within the expression, an empty expression is returned.
*)
let rec simplify : exp -> exp =

  let mkConcat : tag -> exp list -> exp = fun tag -> function
    | [e] -> e
    | es -> Concat (es, tag)
  in
  
  (* don't think this can be optimised much *)
  let rec concat : exp list -> exp list = function
      (* Concat nesting might give useful hints about message formats, but for now we flatten all concats *)
    | Concat (es', _) :: es -> concat (es' @ es)
    | Range (e1, pos1, len1, _) :: Range (e2, pos2, len2, _) :: es
        when equalLen pos2 (addLen pos1 len1) && e1 = e2 ->
      concat (simplify (Range (e1, pos1, addLen len1 len2, freshDet ())) :: es)
    (* FIXME: return string concatenation when you also do corresponding arithmetic simplifications for lengths *) 
    (* | String s1 :: String s2 :: es -> concat (String (s1 ^ s2) :: es) *)
    | e :: es when equalLen (getLen e) zero -> concat es
    | e :: es -> e :: concat es
    | [] -> []

  (* don't think this can be optmised much *)
  and cut : len -> exp list -> (exp list * exp list) option = fun pos es ->
    (* debug ("cut, pos: " ^ dumpLen pos);
    debug ("cut, es: " ^ dump (Concat es)); *)
    match pos with
	    | All -> Some (es, [])
	    | pos -> match es with
          (* in case the range extends beyond the end of the expression, we add an undefined chunk *)
        | [] -> Some ((if equal pos zero then [] else [undef pos]), [])
        | e :: es -> 
          match getLen e with
              | Unknown -> None
              | l ->
                match greaterEqualLenAnswer l pos with (* Old: using length comparison for positivity assumption. *)
                | Yes ->
                    Some ([simplify (Range (e, zero, pos, freshDet ()))], simplify (Range (e, pos, All, freshDet ())) :: es)
                | Maybe -> None
                | No -> 
                    let pos' = op "-" pos l in
                    match cut pos' es with
                      | Some (es1, es2) -> Some (e :: es1, es2)
                      | None -> None
  
  and cutLeft : len -> exp list -> exp list option = fun pos es ->
    match cut pos es with
        | Some (left, _) -> Some (concat left)
        | None -> None
  
  and cutRight : len -> exp list -> exp list option = fun pos es ->
    match cut pos es with
        | Some (_, right) -> Some (concat right)
        | None -> None

  and addPI : exp -> pos -> pos = fun a -> function
    | [Flat b, step] -> [(Flat (op "+" b (op "*" step a)), step)]
    | [Index i, step] -> 
      begin match getIntVal a with
        | Some j -> [Index (i + j), step]
        | None -> addPI a [Flat (op "*" step (mkInt i)), step]
                    (* fail "addPI: only concrete integers can be added to index offsets" *)
      end
    | [(o, step)] -> [(o, step); (Flat a, step)] (* FIXME: actually need an index here *)
    | o :: os -> o :: addPI a os
    | [] -> fail "addPI: pointer has no offsets"

  and skipZeros : pos -> pos = function
    | [os] -> [os]
    | os :: pos' when isZeroOffset os -> skipZeros pos'
    | pos -> pos

  and flattenIndex : pos -> pos = function
    | (Index i, step) :: pos' -> (Flat (op "*" step (mkInt i)), step) :: pos'
    | pos -> pos

  and subtractPP : pos -> pos -> exp = fun pos1 pos2 ->
    match skipZeros pos1, skipZeros pos2 with
      | [Index i, step1], [Index j, step2] ->
        (* 
	        The pointer difference type is ptrdiff_t, which is implementation - dependent.
	        For now, the right thing might be to insert explicit casts during the instrumentation. 
        *)
        if equalLen step1 step2 then Int (Int64.of_int (i - j), Unknown) 
        else fail "subtractPP: pointers have different steps (1)"
        
      | pos1', pos2' -> 
        match flattenIndex pos1', flattenIndex pos2' with
		      | [Flat a, step1], [Flat b, step2] ->
		        if equalLen step1 step2 then op "-" a b 
		        else fail "subtractPP: pointers have different steps (2)" 
        
		      | os1 :: pos1'', os2 :: pos2'' -> 
		        if equalOffset os1 os2 then subtractPP pos1'' pos2''
		        else fail "subtractPP: pointers have incompatible offsets (1)"
         
          | _ -> fail "subtractPP: pointers have incompatible offsets (2)"
  
  and stripIntCast : exp -> exp = function
    | Sym (("castToInt", _), [e; _], _, _) -> stripIntCast e
    | e -> e

  in function e_orig -> 
  (* debug ("simplify: " ^ dumpLen e_orig); *)
  match e_orig with
   
  | Sym (("castToPtr", _), [e; _], _, _) ->
    begin 
    match stripIntCast e with
      | Ptr (b, pos) -> Ptr (b, rev ((Index 0, Unknown) :: ((rev pos))))
      | _ -> fail "simplify: cast to pointer of non-zero expression"
    end

  | Sym (("castToInt", _), [e; _], l, _) when equalLen l (getLen e) -> e
 
  | Sym (("PlusPI", _), [Ptr (b, pos); offset], _, _) -> Ptr (b, addPI offset pos)

  | Sym (("MinusPP", _), [Ptr (b1, pos1); Ptr (b2, pos2)], _, _) -> 
    if b1 <> b2 then
      fail "simplify: trying to subtract pointers with different bases";
    subtractPP pos1 pos2

  | Sym (("len", _), [e], l, _) -> setLen (getLen e) l

  | _ when isArithmetic e_orig -> arithSimplify e_orig

  | Range (e, pos, len, tag) -> 
    begin
      let e_len = getLen e in
      let new_len = if len = All then op "-" e_len pos else len in
      let e_new = Range (e, pos, new_len, tag) in
      (* debug ("simplify: e_len = " ^ dumpLen e_len);
      debug ("simplify: new_len = " ^ dumpLen new_len); *)
      match e with
          (* OLD?: unfortunately e_len is not always known, so we need the disjunction *)
        | e when equalLen zero pos && (len = All || equalLen len e_len) -> e (* e when greaterEqualLen new_len e_len -> e *)
        | e when greaterEqualLen zero new_len -> Concat ([], tag)
        | String s -> 
          begin
            match (getIntVal pos, getIntVal new_len) with
              | (Some pos_val, Some len_val) ->
                let s_len_val = String.length s / 2 in
                if pos_val + len_val <= s_len_val then
                  String (String.sub s (2 * pos_val) (2 * len_val))
                else 
                  Concat ([String (String.sub s (2 * pos_val) (String.length s - 2 * pos_val)); 
                          undef (mkInt (len_val + pos_val - s_len_val))], tag)
              | _ -> e_new
          end
        | Concat (es, _) -> 
          begin
            match cutRight pos es with
              | None -> e_new
              | Some es1 ->
                (* debug ("cutRight result: " ^ dump (Concat es1)); *)
                match cutLeft len es1 with
                  | Some es2 -> 
                    (* debug ("cutLeft result:" ^ dump (Concat es2)); *) 
                    mkConcat tag es2
                  | None -> Range (mkConcat (freshDet ()) es1, zero, new_len, tag)
          end
        (* | Range (_, _, len') when len' <> All && len = All -> 
          fail "simplify: e{pos1, l}{pos2, All} with l <> All and pos2 <> 0 is considered suspicious" *)
          (* FIXME: still need to check that new_len is smaller than len' *)
        | Range (e', pos', _, _) -> simplify (Range (e', addLen pos' pos, new_len, tag)) 
        (* | Range (e', pos', _) -> simplify (Range (e', addLen pos' pos, len)) *)
        
          (* FIXME: need to check that we don't cut the boundary if e_byte has length > 1 *)
        | Sym (("replicate", fixity), [e_byte], _, _) -> Sym (("replicate", fixity), [e_byte], new_len, tag)
        | _ -> e_new 
        (* | _ -> e_orig *) 
    end

  | Concat (es, tag) -> mkConcat tag (concat es)

  | e -> e

(* let deepSimplify : exp -> exp = visitExpPost simplify *)

(*************************************************)
(** {1 Process Meta} *)
(*************************************************)

(** 
  Meta information assigned to expressions.
*)
type meta =
{
  mutable name: string;
  
  mutable refs: int;
  (** The number of other expressions referring to this one.
      This is used for deciding whether to inline this expression during output.
   *)
  
  mutable defined: bool;
  (** Is the variable that has the name of this expression introduced somewhere? *)
} 

(** 
  Meta information for expressions.
  Transient, nothing can be assumed between function calls.
*)
let meta: meta IntMap.t ref = ref IntMap.empty

(** 
  The tags used for names.
  Volatile, nothing can be assumed between function calls.
*)
let nameTags : int StrMap.t ref = ref StrMap.empty

(**
  An environment that records names given to expressions in a process.
*)
type pMeta = meta IntMap.t * int StrMap.t

type process = exp list * pMeta

let resetRefs : unit -> unit = fun () ->
  let reset : meta -> meta = fun m -> { m with refs = 0 } in
  meta := IntMap.map reset !meta

(*
let resetNames : unit -> unit = fun () ->
  let reset : meta -> meta = fun m -> { m with name = "" } in
  meta := IntMap.map reset !meta;
  nameTags := StrMap.empty
*)

let emptyMeta: unit -> pMeta = fun () -> (IntMap.empty, StrMap.empty)

let setActiveMeta: pMeta -> unit = fun (m, n) ->
  meta := m;
  nameTags := n

let resetMeta: unit -> unit = fun () -> setActiveMeta (emptyMeta ())
  
let getActiveMeta: unit -> pMeta = fun () -> (!meta, !nameTags)   

let getMeta : exp -> meta = fun e ->
  let id = expId e in
  (* debug ("getMeta, id = " ^ string_of_int id ^ ", e = " ^ dump e); *)
  try IntMap.find id !meta
  with Not_found -> 
    let m = { name = ""; refs = 0; defined = false } in
    meta := IntMap.add id m !meta;
    m

let giveName : exp -> string = fun e ->
  let m = getMeta e in
  let hint = getHint e in
  if m.name = "" then
  begin
    let h = if hint = "" then "var" else hint in
    let tag = try StrMap.find h !nameTags with Not_found -> 1 in
    m.name <- h ^ (string_of_int tag);
    nameTags := StrMap.add h (tag + 1) !nameTags;
    (* debug ("giveName: h = " ^ h ^ ", tag = " ^ string_of_int tag); *) 
  end;
  (*
  debug ("giveName: name = " ^ m.name ^ ", e = " ^ dump e); 
  *)
  m.name

(*************************************************)
(** {1 Transformations} *)
(*************************************************)


let inlineAll = ref false

let showLens = ref false

(**
  Does an expression need a bracket in context?
  
  In expressions "|" binds less tightly than any infix operator.
*)
let needsBracket : exp -> bool = function
  | Concat _ -> true
  | Sym ((_, Infix), _, _, _) -> true
  | _ -> false

let mustInline : exp -> bool = 
    let isShort : exp -> bool = function 
      | Int _ -> true
      | Ptr _ -> true
    | e when isArithmetic e -> true
      | e -> match getIntVal (getLen e) with Some l_val -> l_val < 30 | _ -> false
  in
  function
    | All | Unknown -> true
    | Sym ((("var" | "len" | "lenvar" | "field_offset"), _), _, _, _) -> true
    | e -> isConcrete e && isShort e


(* FIXME: remove later, see splitByType *)    
let isIMLAction : exp -> bool = function
  | Sym ((("read" | "new" | "newT"), _), _, _, _) -> true
  | _ -> false


let rec markOffset : offset -> unit = function
  | (Flat e, _) -> markExp e
  | _ -> ()

and markExp : exp -> unit = fun e ->
  let m = getMeta e in
  m.refs <- m.refs + 1;
  if m.refs = 1 then match e with
    | Sym (_, es, l, _) -> (iter markExp es; markExp l)
    | Range (e', f, l, _) -> (markExp e'; markExp f; markExp l)
    | Concat (es, _) -> iter markExp es
    | Struct (fields, _, l, _) -> (StrMap.iter (fun _ e' -> markExp e') fields; markExp l)
    | Array (cells, l, _) -> (IntMap.iter (fun _ e' -> markExp e') cells; markExp l)
    | Ptr (_, pos) -> iter markOffset pos
    | _ -> ()

(**
  Records for each expression, how often it is referenced by other expressions.
  Call this with the same list that you intend to output.
*)
let markExps : exp list -> unit = fun es -> resetRefs (); iter markExp es


(*
(*
    Whether to exhaustively eliminate common subexpressions is a matter of taste:
    with splitByType you get
        let dsa_sig_r1 = dsa_sig_r(sk(keyseed1), hash4) in
        let dsa_sig_s1 = dsa_sig_s(sk(keyseed1), hash4) in
    and with 
        let skey1 = sk(keyseed1) in
            let dsa_sig_r1 = dsa_sig_r(skey1, hash4) in
            let dsa_sig_s1 = dsa_sig_s(skey1, hash4) in
*)
let elimCommonSubs : exp list -> exp list = fun es ->

    let rec elimSubs : exp -> exp list = fun e ->
      
      (* this is constructed in reverse order, reverse once before returning *)
      let subs : exp list ref = ref [] in

      let elim : exp -> exp = fun e ->
          let m = getMeta e in
          (* already defined before, just replace by the name *)
          if m.printed then 
            mkVar m.name e
          (* inline expressions that are only referenced once or are short concrete values *)
          else if !inlineAll || (mustInline e) || (not (isIMLAction e) && (m.refs = 1)) then
          e
          (* not inlined, output as separate definition *)
          else 
          begin
          let name = giveName e in
            m.printed <- true;
          subs := (if isIMLAction e then e else mkLet e) :: !subs;
          mkVar name e
          end
      in
      
      let e' = visitExpPost elim e in
      rev (e' :: !subs)
    
  in
  markExps es;
  let result = List.concat (map elimSubs es) in
  resetMeta ();
  result
*)

(*
  The types form a lattice
  
  Top
  \/
  {Conc, Parse, Crypt, Formula}
  \/
  Bot
  
  Such that an expression of type t' should be inlined in an expression of type t whenever t' <= t.
*)
type expType = Conc | Parse | Crypt | Formula | Top | Bot

(*
  Idempotent, if started with same meta as returned.
*)
let splitByType : process -> process = fun (es, meta) ->
	
		let splitExpByType : exp -> exp list = fun e ->
		
		let subs : exp list ref = ref [] in
		
		let mustMoveOut : exp -> bool = fun e ->
		  let m = getMeta e in
		  (isIMLAction e) || (isNondet e && m.refs > 1)
		in
		
	  let moveOut : expType -> expType -> exp -> exp = fun t t' e ->
	  let inline = 
	    if mustMoveOut e then false
	    else if mustInline e then true
	    else if t = Top || t = t' then true
	    else false 
	  in
	  if inline then e else
	    let m = getMeta e in
      let v = mkVar (giveName e) e in
	    if m.defined then v
	    else begin
			  m.defined <- true;
		    let e_def = match e with
		      | Sym ((s, fixity), [], len, tag) when List.mem s ["read"; "new"] -> 
		        Sym ((s, fixity), [v], len, tag)
          | Sym (("newT", fixity), [String t], len, tag) ->
            Sym (("newT", fixity), [v; String t], len, tag) 
		      | e -> mkLet v e
	      in
	      subs := e_def :: !subs;
	      v
	    end 
	  in
	
	  let rec split : expType -> exp -> exp = fun t e -> 
	    match e with
      | Int _ -> e
      | String _ -> e
      | Sym ((s, fixity), es, l, tag) ->
        let t' = 
  	      if List.mem s ["len"; "+"; "-"; "!"; "&&"; "||"; "LOR"; "<"; ">"; "<="; ">="] then 
	          if List.mem t [Parse; Conc; Top] then t else Parse
          (* else if List.mem s ["!"; "&&"; "||"; "LOR"; "<"; ">"; "<="; ">="] then Formula *)
   	      else Crypt
        in
        let e' = Sym ((s, fixity), map (split t') es, split t' l, tag) in
        moveOut t t' e'
      | Range (e1, pos, len, tag) -> 
        let e' = Range (split Parse e1, split Parse pos, split Parse len, tag) in
        moveOut t Parse e'
      | Concat (es, tag) -> 
        let e' = Concat (map (split Conc) es, tag) in
        moveOut t Conc e'
	    | Struct (fields, attrs, len, default) ->
	      let e' = Struct (StrMap.map (split Top) fields, attrs, len, default) in
	      moveOut t Bot e'
	    | e -> e
	  in
	  
	  let e' = match e with
	  | Sym ((("IfEq"), fixity), [e1; e2], l, det) ->
	    let (e1', e2') = 
	      if isAuxiliaryIf e 
	      then (split Top e1, split Top e2)
	      else (split Bot e1, split Bot e2)
	    in 
	    Sym (("IfEq", fixity), [e1'; e2'], l, det)
    | Sym (("If", fixity), [e], l, det) -> 
      Sym (("If", fixity), [split Top e], l, det)
	    (* | Sym ((("branchT"), fixity), [e], l, det) -> Sym (("branchT", fixity), [split Top e], l, det) *)
	  | Sym (("write", fixity), [e], l, tag) -> Sym (("write", fixity), [split Bot e], l, tag)
	    (* making sure top-level reads don't get moved out *)
	  | Sym (("read", _), _, _, _) -> e
	  | Sym (("let", _), [_; _], _, _) ->
      (* this info should already be contained in pMeta *)
	    (* let m = getMeta rhs in m.printed <- true; *)
	    split Top e
	    (* We want event to stay top: "event e(x);", not "let y = e(x) in event y;" *)
      (* FIXME: this only happens because event is Crypto and its parameters as well! *)
	  | e -> split Top e
	  in
	  rev (e' :: !subs)

  in
  setActiveMeta meta;
  markExps es;
  let es' = List.concat (map splitExpByType es) in
  es', getActiveMeta ()

(*************************************************)
(** {1 Output} *)
(*************************************************)

  
let showTag : tag -> string = function
  | NoTag -> "NoTag"
  | Det i -> "0"
  | Nondet i -> string_of_int i

let isFreeLen : len -> bool = function
  | Unknown -> true
  | Sym (("lenvar", _), _, _, _) -> true
  | _ -> false

let rec showIExpBody : exp -> string = function 
  | Int (ival, len) -> "i" ^ Int64.to_string ival
  | String s -> s
  | Sym ((s, Prefix), es, len, tag) -> 
      let bodies = map (showIExp) es in
      let len_body = showLen len in
      let id_part = if !inlineAll then "[" ^ showTag tag ^ "]" else "" in
      let body = if (isFreeLen len) || (getIntVal len = Some 0) then
                      s ^ id_part ^ "(" ^ String.concat ", " bodies ^ ")"
                 else s ^ id_part ^ "(" ^ String.concat ", " bodies ^ ")" ^ "<" ^ len_body ^ ">"
      in body
  | Sym ((s, Infix), es, len, tag) -> 
      let len_body = showLen len in
      let bodies = map (showIExp ~bracket: true) es in
      let body = if isFreeLen len && s = "castToInt" then
                      String.concat (" " ^ s ^ " ") bodies ^ "<" ^ len_body ^ ">"
                 else String.concat (" " ^ s ^ " ") bodies
      in body
  | Range (e, f, l, _) ->
      let body = showIExp ~bracket: true e in
      let f_body = showLen f in
      let l_body = showLen l in
      body ^ "{" ^ f_body ^ ", " ^ l_body ^ "}"
  | Concat (es, _) -> 
      let bodies = map showIExp es in
      let body = String.concat "|" bodies
      in body
  | Ptr (b, pos) -> 
      let pos_bodies = map (showOffset) pos in
      (* let (step_defs, step_body) = showLen step in *)
      let body = "<<" ^ dumpBase b ^ "; " ^ String.concat ", " pos_bodies ^ ">>"
      in body
  | Struct (fields, _, _, _) ->
      let showField name e = 
        let field_body = showIExp e in
        name ^ ": " ^ field_body
      in
      let field_bodies = fold2list StrMap.fold showField fields in
      "<{" ^ String.concat "; " field_bodies ^ "}>"
  | Array (cells, len, _) -> 
      let showCell (i, e) = 
        let cell_body = showIExp e in
        string_of_int i ^ " ~> " ^ cell_body
      in
      begin
      match fold2list IntMap.fold (fun i e -> (i, e)) cells with
        | [0, e] -> showIExp e
        | cells -> 
          let cell_bodies = map showCell cells in
          "<{" ^ String.concat "; " cell_bodies ^ "}>"
           (* ^ "<" ^ dumpLen len ^ ">" *)
      end
          
  | e -> fail ("showIExpBody: length expressions are only allowed in length fields: " ^ dump e)

and showLen : len -> string = function
  | Unknown -> "?"
  | All -> "+"
  | Int (ival, _) -> Int64.to_string ival
  | e -> showIExp e

and showOffset : offset -> string = function (os, step) -> 
  let os_body = showOffsetVal os in
  let step_body = showIExp step in
  os_body ^ "(" ^ step_body ^ ")"

and showOffsetVal : offsetVal -> string = function
  | Field s -> "field " ^ s
  | Attr s -> "attr " ^ s
  | Index i -> "index " ^ (string_of_int i)
  | Flat e -> showIExp e

and showIExp : ?bracket: bool -> exp -> string = fun ?(bracket = false) e ->
  match e with
    | Sym (("var", _), [String s], _, _) -> s
    | e ->
		  if bracket && (needsBracket e) then "(" ^ showIExpBody e ^ ")"
		  else showIExpBody e

let showInVar : exp -> string = function
  | Sym (("var", _), [String name], l, _) -> name ^ "<" ^ showLen l ^ ">"
  | _ -> failwith "showInVar: not a var"

let showIExpTop : exp -> string = fun e ->
  match e with
    | Sym (("read", _), [v], _, _) -> 
      "in(c, " ^ showInVar v ^ ");";

		| Sym (("read", _), vs, _, _) -> 
		  "in(c, (" ^ String.concat ", " (map showInVar vs) ^ "));";
		
		| Sym (("new", _), [v], _, _) -> 
		  "new " ^ showInVar v ^ ";";

    | Sym (("newT", _), [v; String t], _, _) -> 
      "new " ^ showInVar v ^ ": " ^ t ^ ";";

    | Sym (("write", _), [e'], _, _) -> 
      "out(c, " ^ showIExp e' ^ ");";

		| Sym (("write", _), es, _, _) -> 
		  "out(c, (" ^ String.concat ", " (map showIExp es) ^ "));";
		
		| Sym ((("IfEq"), _), [e1; e2], _, _) ->
		  "if " ^ showIExp e1 ^ " = " ^ showIExp e2 ^ " then "

    | Sym ((("If"), _), [e], _, _) ->
      "if " ^ showIExp e ^ " then "
        		
		| Sym ((("event"), _), [e], _, _) -> 
		  "event " ^ showIExp e ^ ";"
		
		| Sym ((("let"), _), [pat; rhs], _, _) ->
		  "let " ^ showIExp pat ^ " = " ^ showIExp rhs ^ " in"
		  
		| _ -> fail ("showIExpTop: unexpected top value: " ^ dump e)


(**
  Only for IML processes that don't contain let expressions,
  and where inputs and restrictions are still inlined. 
*)
let showSimpleIMLRaw : exp list -> string = fun es ->
  resetMeta ();
  let result = String.concat "\n" (map showIExp es) ^ "\n" in
  result

(**
  Only for IML processes that don't contain let expressions,
  and where inputs and restrictions are still inlined. 
*)
let showSimpleIML : exp list -> string = fun es ->
  let es', _ = splitByType (es, emptyMeta ()) in
  String.concat "\n" (map showIExpTop es') ^ "\n" 

(**
  Outputs the process as is, does not do any rewriting 
*)
let showStructuredIML : exp list -> pMeta -> string = fun es meta ->
  setActiveMeta meta;
  String.concat "\n" (map showIExpTop es) ^ "\n" 

let dumpIML: exp list -> string = fun es -> String.concat "\n" (map dump es) ^ "\n"

(*************************************************)
(** {1 Filtering} *)
(*************************************************)

(*
  Right now the preprocessed form uses If and IfEq, but see what becomes more comfortable. 
*)
let preprocess : exp -> exp = function
  | Sym ((("branchF"), _), [Sym (("!=", _), args, _, _)], _, tag) ->
    Sym ((("IfEq"), Prefix), args, Unknown, tag)

  | Sym ((("branchT"), _), [Sym (("==", _), args, _, _)], _, tag) ->
    Sym ((("IfEq"), Prefix), args, Unknown, tag)

  | Sym ((("branchF"), _), [Sym (("cmp", _), args, _, _)], _, tag) ->
    Sym ((("IfEq"), Prefix), args, Unknown, tag)

  | Sym ((("branchT"), _), [e], _, tag) ->
    Sym ((("If"), Prefix), [e], Unknown, tag)

  | Sym ((("branchF"), _), [e], _, tag) ->
    Sym ((("If"), Prefix), [Sym (("!", Prefix), [e], Unknown, freshDet ())], Unknown, tag)

  | Sym (("==", _), [Sym (("cmp", _), [e1; e2], _, _); z], _, tag) when equal z zero ->
    Sym (("==", Infix), [e1; e2], Unknown, tag)

  | e -> e

let rec containsPtr : exp -> bool = function
  | Int _ -> false
  | String _ -> false
  | Range (e, _, _, _) -> containsPtr e
  | Sym (_, es, _, _) -> exists containsPtr es
  | Ptr _ -> true
  | _ -> false

(*
  The heuristic is to leave the comparisons that mention ranges, concats, vars, or lens in the top-level arithmetic expression,
  hoping that those will be enough to prove the parsing safety.
  
  We also keep mentions of environment vars at top level.

  The heuristic doesn't distinguish in NSL/server.c between the useless
  !(len(inverse_injbot(D(msg2, skB)))<8> > decrypt_len()<8>)
  and the useful 
  !(i32 >= len(inverse_injbot(D(msg2, skB)))<8>)
  
  If you really want to get rid of the former, you could check that decrypt_len()<8>
  is not mentioned anywhere else.
*)
let isBoringComparison : exp -> bool = 

  let rec interesting : exp -> bool = function
	  | Range _ -> true
	  | Concat _ -> true
    | Sym ((("var" | "len"), _), _, _, _) -> true
	  | Sym ((s, _), es, _, _) when List.mem s ["len"; "+"; "-"; "!"; "&&"; "||"; "LOR"; "<"; ">"; "<="; ">="; "castToInt"] -> 
	    exists interesting es
	  | _ -> false
  in  
  
  function
  | Sym (("If", _), [e], _, _) when isComparison e || isLogical e -> not (interesting e) 
  | _ -> false

let isCastEq : exp -> bool = 
  
  let rec stripCast : exp -> exp = function
    | Sym (("castToInt", _), [a; _], _, _) -> stripCast a
    | e -> e
  in
  
  function
      | Sym (("IfEq", _), [e1; e2], _, _) -> structEq (stripCast e1) (stripCast e2)
      | _ -> false

let boringEvent : exp -> bool = fun e -> containsPtr e || isBoringComparison e || isCastEq e

let interestingEvent : exp -> bool = fun e -> not (boringEvent e)

let procAndFilter es = filter interestingEvent (map (visitExpPost preprocess) es)
