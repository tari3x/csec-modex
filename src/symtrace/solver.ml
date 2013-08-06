(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Sym.Op.T
open Iml.Exp.T

module E = struct 
  include Iml.Exp
  include Iml.Exp.T
end

(*************************************************)
(** {1 Types} *)
(*************************************************)

type answer = Yes | No | Maybe

(**
    [true] means definitely true, [false] means we don't know.
*)
type pbool = bool

type fact = exp

(*************************************************)
(** {1 State} *)
(*************************************************)

let ctx : Yices.context = Yices.mk_context ()

let cache : pbool IntMap.t ref = ref IntMap.empty

(* accelerated cache for eq queries *)
module IntPair =
struct
  type t = int * int
  let compare = Pervasives.compare
end
module PairMap = Map.Make (IntPair) 
let eqCache: pbool PairMap.t ref = ref PairMap.empty 

let warnCache = ref E.Set.empty

(*************************************************)
(** {1 Naming} *)
(*************************************************)

(*
  The naming should be separate from the naming used by output routines,
  we want the names to persist continuously, no reset.
  
  At the same time this ending may, if necessary, be made to respect
  output names when they are availablE.
*)

let mkExpName e id = 
  match e with
    | Var v -> "var_" ^ v
    | _ -> "var" ^ (string_of_int id)

(*************************************************)
(** {1 Yices theory} *)
(*************************************************)

(* 
  TODO: at some point check which ones are really necessary.
*)
let theory = 
"
(define-type bitstringbot)
(define bottom:: bitstringbot)
(define-type bitstring (subtype (x::bitstringbot) (/= x bottom)))

; These correspond to val and bs functions in the paper
(define value_unsigned:: (-> bitstringbot nat))
(define value_signed::   (-> bitstringbot int))
(define bs_unsigned::    (-> int nat bitstringbot))
(define bs_signed::      (-> int nat bitstringbot))

(define truth:: (-> bitstringbot bool))

; The length of bottom is arbitrary.
(define len::   (-> bitstringbot nat)) 
(define range:: (-> bitstringbot nat nat bitstringbot))

(define defined:: (-> bitstringbot bool))
"
(*
(define ptr::   (-> nat nat nat))
(assert
(forall (base1::nat offset1::nat base2::nat offset2::nat)
        (=> (/= base1 base2)
            (/= (ptr base1 offset1) (ptr base2 offset2)))))
*)
        
;;
Yices.parse_command ctx theory 
;;

let range () = 
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "range") 

let len () = 
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "len") 

let value = function
  | IntType.Unsigned -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "value_unsigned") 
  | IntType.Signed -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "value_signed")

let bs = function
  |  IntType.Unsigned -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_unsigned") 
  |  IntType.Signed -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_signed")

let truth () = 
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "truth") 
      
let bottom () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bottom")
    
(*
let ptr () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "ptr")
*)
    
let defined () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "defined")

(*************************************************)
(** {1 Building facts} *)
(*************************************************)

let eqBitstring es = Sym (BsEq, es)
let eqInt es = Sym (EqInt, es)
let notE e = Sym (Not, [e])
let gt a b = Sym (GtInt, [a; b])
let ge a b = Sym (GeInt, [a; b])

let trueFact: fact = Sym (True, [])

let isDefined e = Sym (Defined, [e])
    
let rec inType e t =
  let module T = Iml.Type.T in
  match t with
    | T.Bitstringbot -> trueFact
    | T.Bitstring    -> isDefined e
    | T.Fixed n      -> eqInt [E.int n; Len e]
    | T.Bounded n    -> ge (E.int n) (Len e)
    | T.Bool | T.Int | T.BsInt _ | T.Ptr -> 
      begin match e with
        | Sym (sym, _) when Sym.resultType sym = t -> isDefined e
        | e -> Sym (InType t, [e])
          (* fail "%s" (E.toString (Sym (InType t, [e]))) *)
       end
    | T.Named (name, Some t) -> inType e t 
    | T.Named (name, None) -> Sym (InType t, [e])

(*************************************************)
(** {1 Debug} *)
(*************************************************)

let debug_expr ?(raise_by = 0) s e =
  debug_depth := !debug_depth - raise_by;
  if debugEnabled () then begin 
    prerr_string (decorateDebug s); flush stderr; Yices.pp_expr e; prerr_endline ""; flush stderr;
  end;
  debug_depth := !debug_depth + raise_by

(*************************************************)
(** {1 Checking facts} *)
(*************************************************)

;;
Yices.enable_type_checker true
;;


let addFactRaw: Yices.expr -> unit = fun y_e ->
  debug_expr "asserting_y " y_e;
  Yices.assert_simple ctx y_e;
    
  if Yices.inconsistent ctx = 1 then
  begin
    (* dump_context ctx; *)
    debug_expr "addFact: the context has become inconsistent: " y_e;
    fail "inconsistent context";
  end


let rec rewritePtr e = 
  (* 
    To deal with 
      <<stack nullPtr; index 0(i8), index 0(i1)>> == <<stack nullPtr; index 0(i1)>>
  *)
  let notZero = function
    | (Flat (E.Int 0L), _) -> false
    | (Index 0, _) -> false
    | _ -> true
  in  
  
  match e with
  | Ptr (pb, eo) -> Var ("ptr_" ^ E.toString (Ptr (pb, List.filter notZero eo)))
  | e -> E.descend rewritePtr e


let rewrite es: fact list * fact list =
  (*
    We don't represent integer ranges directly because they are too big for OCaml int64.
  *)
  let module Range = struct
    type t = IntType.t 
    
    (* Don't raise to the power explicitly, to avoid overflow *)
    let pow a n =
      if n = 0 then E.one else  
      E.prod (replicate n (E.int a))
      
    let contains (sd, w) e =
      match E.typeOf e with 
      | BsInt (sd', w') when sd = sd' && w' <= w -> [trueFact]
      | _ ->  
        let a, b = match sd with
          | IntType.Unsigned -> E.zero,                          Sym (MinusInt, [pow 256 w;       E.int 1])
          | IntType.Signed   -> Sym (NegInt, [pow 256 (w - 1)]), Sym (MinusInt, [pow 256 (w - 1); E.int 1])
        in
        [Sym (GeInt, [e; a]); Sym (LeInt, [e; b])]
        
    let subset (sd, w) (sd', w') = (sd = sd') && w <= w'
  end in

  let seen = ref [] in
  
  let rewriteOnce e =
    let conds = ref [] in

    let rec collect e =  
      let facts, e' =
        let eTop = e in
        debug "collect: e = %s" (E.toString e); 
        match e with 
        
        (* 
          Rewriting of binary arithmetic to integer arithmetic.
        *)
        | Sym ((Op (op, ([BsInt t1; BsInt t2], _))) as sym, [e1; e2]) when Sym.isBinaryComparison sym ->
          let sym' = 
            begin match op with
              | Eq -> EqInt
              | Ne -> NeInt
              | Ge -> GeInt
              | Gt -> GtInt
              | Le -> LeInt
              | Lt -> LtInt
              | _ -> fail "impossible: binary comparsion %s" (E.toString e)
            end
          in
          [isDefined e1; isDefined e2],
          Sym (sym', [Val (e1, t1); Val (e2, t2)]) |> collect
          
        | Val ((Sym (sym, [e1; e2])) as e, itype) when Sym.isBinaryArithmetic sym ->
          let sym' = 
            begin match sym with
              | Op (PlusA, _) -> PlusInt 2
              | Op (MinusA, _) -> MinusInt
              | Op (Mult, _) -> MultInt 2
              | Op (Div, _) -> fail "solver: support for division not activated: %s" (E.toString e)
              | _ -> fail "unexpected binary arithmetic %s" (Sym.toString sym)
            end
          in
          let e'= Sym (sym', [Val (e1, itype); Val (e2, itype)]) in 
          isDefined e :: Range.contains itype e', collect e'

        | Val ((Sym (Op (CastToInt, ([BsInt itype_from], BsInt itype_to)), [e])) as cast_e, itype_to') ->
          if itype_to <> itype_to' then
            fail "itype of Val not the same as itype of cast: %s" (E.toString eTop);
          let e' = Val (e, itype_from) in
          let range_cond = 
            if Range.subset itype_from itype_to then [] 
            else Range.contains itype_to e' 
          in  
          isDefined cast_e :: range_cond, collect e' 
           
        | Val (BS (e, itype) as e_bs, itype') ->
          if itype <> itype' then
            fail "incompatible Val of BS: %s" (E.toString eTop);
          [isDefined e_bs], collect e

        | BS (Val (e, itype), itype') as e_bs ->
          if itype <> itype' then
            fail "incompatible BS of Val: %s" (E.toString eTop);
          [isDefined e_bs], collect e

        (* 
          Rewriting of lengths. 
        *)
        
        | Len (BS (_, (_, w)) as e_bs) ->
          [isDefined e_bs], collect (E.int w)

        | Len (Sym (Op (_, (_, BsInt (_, w))), _) as e_bin) ->
          [isDefined e_bin], collect (E.int w)

        | Len (Concat es) ->
          [], collect (E.sum (List.map (fun e -> Len e) es))

        | Len (Range (e, p, l)) as eTop -> 
          [isDefined eTop], collect l

        | Len (String b) ->
          [], E.int (String.length b)

          (* This will become unnecessary once pointers are rewritten into vanilla expressions, as per thesis *)          
        | Len (Ptr _) ->
          [isDefined eTop], Sym (PtrLen, [])

        (* 
          Rewriting of defined(...) expressions. 
        *)

          (* Here and below we do not list defined() conditions because those are implied by
             the comparison operators *) 
        | Sym (Defined, [Range (e, p, l)]) ->
          [], E.conj [ge (Len e) (E.sum [p; l]);
                      ge p E.zero;
                      ge l E.zero;] |> collect

        | Sym (Defined, [BS (e, itype)]) ->
          [], E.conj (Range.contains itype e) |> collect

        | Sym (Defined, [Val (e, itype)]) ->
          [], E.conj (Range.contains itype e) |> collect

        | Sym (Defined, [Sym (Op (_, (ts, _)), es)]) ->
          let conds =
            List.combine ts es
            |> List2.filter_map (function
              | BsInt (_, w), e -> Some (eqInt [E.int w; E.len e])
              | Type.Ptr, Ptr _ -> None
              | t, e -> fail "unexpected type of op argument: %s: %s" (E.toString e) (Type.toString t)) 
          in
          [], E.conj conds |> collect

        | Sym (Defined, [Sym (sym, es)]) ->
          if Sym.neverFails sym then
            [], trueFact
          else if not (Sym.mayFail sym) then
            [], E.conj (List.map isDefined es) |> collect
          else 
            let e' = Sym (Defined, [Sym (sym, es) |> collect]) in
            [], E.conj (e' :: List.map collect (List.map isDefined es)) 
          
        | Sym (Defined, [Len e]) ->
          [], Sym (Defined, [e]) |> collect
          
        | Sym (Defined, [Int _ | String _ | Concat []]) -> 
          [], trueFact

        | Sym (Defined, [Concat es]) ->
          [], E.conj (List.map isDefined es) |> collect

          (* This will become unnecessary once pointers are rewritten into vanilla expressions, as per thesis *)          
        | Sym (Defined, [Ptr (_, pos)]) ->
          let definedOffset (offset, _) = 
            match offset with
            | Flat e -> Some (isDefined e)
            | Index _ | Attr _ | Field _ -> None
          in 
          [], E.conj (List2.filter_map definedOffset pos) |> collect 

        | Sym (Defined, [Struct (fields, _, _, e)]) ->
          [], E.conj (List.map isDefined (isDefined e :: StrMap.values fields)) |> collect 

        (* 
          Replacing vals and lens by their Yices versions.
        *)
        | Val (e, itype) -> 
          [isDefined e], Sym (ValY itype, [e]) |> collect 

        | Len e -> 
          [isDefined e], Sym (LenY, [e]) |> collect

        (* 
          Falling through or turning into opaque.
        *)

        | Sym (Defined, [e]) -> 
          [], Sym (Defined, [collect e])

          (* I suppose everything of type bitstringbot can be turned into opaque here. *)          
        | Sym ((Fun _ | NondetFun _ | Ztp | ZtpSafe | Undef _ | Cmp), _)
        | Sym (Op _, _)    
        | BS _
        | Struct _ | Array _ 
        | Concat _ ->
          [], Sym (Opaque, [e]) 

        | e -> [], E.descend collect e
      in
      conds := facts @ !conds;
      e'
    in
    
    let e = collect e in
    let conds = List2.diff !conds !seen |> List2.nub in
    seen := conds @ !seen; 
    e, conds
  in

  let rec splitAnd = function
    | Sym (And _, es) -> List2.concat_map splitAnd es
    | e -> [e]
  in

  let rec rewriteDeep e = 
    let e, es = rewriteOnce e in
    splitAnd e @ List2.concat_map rewriteDeep es 
  in

  debug "rewriting %s" (E.listToString es);
  increase_debug_depth ();
  let es, conds = List.map rewriteOnce es |> List.split in
  let conds = 
    conds 
    |> List.concat 
    |> List2.concat_map rewriteDeep 
    |> List2.nub 
    |> List.map rewritePtr 
  in
  let es = 
    es 
    |> List2.concat_map splitAnd 
    |> List2.nub 
    |> List.map rewritePtr 
  in
  decrease_debug_depth ();
  debug "resulting es = %s" (E.listToString es);
  debug "resulting conds = %s" (E.listToString conds);
  es, conds


module Type = struct
  include Type
  
  let toYicesType = function
    | Bitstringbot   -> Yices.mk_type ctx "bitstringbot"
    | Bitstring      -> Yices.mk_type ctx "bitstring"
    | BsInt _        -> Yices.mk_type ctx "bitstring"
    | Type.T.Int     -> Yices.mk_type ctx Yices.int_type_name
    | Bool           -> Yices.mk_type ctx Yices.bool_type_name
    | t              -> fail "toYicesType: unexpected type: %s" (toString t)
end  

    
let translate: exp -> Yices.expr = fun eTop ->

  let module A = Array in
                      
  let getDecl t name =
    try Yices.get_var_decl_from_name ctx name 
    with Failure _ -> Yices.mk_var_decl ctx name (Type.toYicesType t)
  in
  
  let mkVar t e =
    let id = E.id e in
    Yices.mk_var_from_decl ctx (getDecl t (mkExpName e id))
  in

  let mkString s =
    Yices.mk_var_from_decl ctx (getDecl Bitstring ("string_" ^ s))
  in
  
  let rec tr t e =
    debug "translating %s" (E.dump e);
    match e, t with
      | Int i,                   Type.Int       -> Yices.mk_num ctx (Int64.to_int i)
      | String s,                Bitstringbot   -> mkString s
      | Var _,                   Bitstringbot   -> mkVar Bitstringbot e
      (* TODO: mkVar Bool *)
      (* | Var _,                   Bool           -> Yices.mk_app ctx (truth ()) [| tr Bitstringbot e |] *)          
      | Sym (sym, es), Bool ->
        begin
        match sym, es with
          | (True, [])        -> Yices.mk_true ctx
          | (Not, [a])        -> Yices.mk_not ctx (tr Bool a)
          | (And _, [])       -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump eTop)
          | (And _, es)       -> Yices.mk_and ctx (A.map (tr Bool) (A.of_list es))
          | (Or _, [])        -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump eTop)
          | (Or _, es)        -> Yices.mk_or  ctx (A.map (tr Bool) (A.of_list es))
          | (Implies, [a; b]) -> Yices.mk_ite ctx (tr Bool a) (tr Bool b) (Yices.mk_true ctx)
          | (EqInt, [a; b])   -> Yices.mk_eq ctx (tr Type.Int a) (tr Type.Int b)
          | (NeInt, [a; b])   -> Yices.mk_diseq ctx (tr Type.Int a) (tr Type.Int b)
          | (GtInt, [a; b])   -> Yices.mk_gt ctx (tr Type.Int a) (tr Type.Int b)
          | (GeInt, [a; b])   -> Yices.mk_ge ctx (tr Type.Int a) (tr Type.Int b)
          | (LtInt, [a; b])   -> Yices.mk_lt ctx (tr Type.Int a) (tr Type.Int b)
          | (LeInt, [a; b])   -> Yices.mk_le ctx (tr Type.Int a) (tr Type.Int b)
            
          | (BsEq, [a; b])    ->
                Yices.mk_eq ctx (tr Bitstringbot a) (tr Bitstringbot b)
            
          | (Defined, [e])    -> Yices.mk_app ctx (defined ()) [| tr Bitstringbot e |]
          | (InType _, _)     -> mkVar Type.Bool e
         
          | (Truth, [e])      -> Yices.mk_app ctx (truth ())   [| mkVar Bitstringbot e |]
                 
          | _ -> 
            fail "Solver.translate: unexpected type %s of expression %s in fact %s" (Type.toString t) (E.dump e) (E.dump eTop)
        end  
        
      | Sym (sym, es), Type.Int ->
        begin
        match sym, es with
          | NegInt, [a]          -> Yices.mk_sub ctx [| Yices.mk_num ctx 0; tr Type.Int a |] 
          | (MinusInt), [e1; e2] -> Yices.mk_sub ctx [| tr Type.Int e1; tr Type.Int e2 |]
          | (MinusInt), _        -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump eTop)
          | (PlusInt _), []      -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump eTop)
          | (PlusInt _), es      -> Yices.mk_sum ctx (A.map (tr Type.Int) (A.of_list es))
          | (MultInt _), []      -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump eTop)
          | (MultInt _), es      -> Yices.mk_mul ctx (A.map (tr Type.Int) (A.of_list es))
          | PtrLen, []           -> mkVar Type.Int e 
            
          | LenY, [e]            -> Yices.mk_app ctx (len ())   [| tr Bitstringbot e |]
           (* Not sure this is necessary, perhaps could just make it opaque. *)
          | ValY (s, _), [e]     -> Yices.mk_app ctx (value s)  [| tr Bitstringbot e |] 
            
          | _ -> 
            fail "Solver.translate: unexpected type %s of expression %s in fact %s" (Type.toString t) (E.dump e) (E.dump eTop)            
        end   
        
      | Range (e, pos, len),     Bitstringbot -> Yices.mk_app ctx (range ()) [| tr Bitstringbot e; 
                                                                                tr Type.Int pos; tr Type.Int len |]
      | Sym (Opaque, [_]),       Bitstringbot -> mkVar Bitstringbot e

      | Annotation(_, e),        t            -> tr t e
        
      | e, t -> 
        fail "Solver.translate: unexpected type %s of expression %s in fact %s" (Type.toString t) (E.dump e) (E.dump eTop)

  in 
  E.typecheck Bool eTop;
  tr Bool eTop


let isTrueRaw : exp -> pbool = fun e ->
  (* get id before adding extra clauses *)
  let id = E.id e in
  let result = 
    try 
      let result = IntMap.find id !cache in
      (* This debug is 25 % performance penalty: *)
      debug "checking %s, result = %s" (E.toString e) (string_of_bool result);
      result
    with Not_found -> 
      debug ~raise_by:0 "checking (with auxiliary facts) %s" (E.toString e);
      increase_debug_depth ();
      let ye = translate (notE e) in
      decrease_debug_depth ();
      debug_expr ~raise_by:0 "checking (yices expression)" ye;
      Yices.push ctx;
      Yices.assert_simple ctx ye;
      let result = match Yices.check ctx with
        | Yices.False -> true
        | Yices.Undef -> false
        | Yices.True  -> false
      in
      Yices.pop ctx;
      debug ~raise_by:0 "check result = %s" (string_of_bool result);
      result
  in
  cache := IntMap.add id result !cache;
  result

let warnIfFalse eTop e =
  if not (E.Set.mem e !warnCache) && not (isTrueRaw e) then
  begin
    warn "cannot prove auxiliary fact %s arising from fact %s" (E.toString e) (E.toString eTop);
    (*
      Returns NULL model:
      push ctx;
      assert_simple ctx (silent translate (notE e));
      let model = get_model ctx in
      display_model model;
      pop ctx; 
    *)
    warnCache := E.Set.add e !warnCache;
  end

let rec simplifyBool = 
  let isTrue = function
    | Sym (And _, []) | Sym (True, []) -> true
    | _ -> false
  in 
  function
  | Sym (Implies, [e1; e2]) when isTrue e1 -> simplifyBool e2 
  | Sym (And _, [e]) -> simplifyBool e
  | Sym (sym, _) as e when Sym.isLogical sym -> E.descend simplifyBool e
  | e -> e

let addFact : exp -> unit = fun e ->
  increase_debug_depth (); 
  let defined_facts, defined_conds = rewrite [isDefined e] in
  let es', e_conds = rewrite [e] in
  let conds = defined_conds @ e_conds in
  List.iter (silent (warnIfFalse e)) conds;
  let e = Sym (Implies, [E.conj conds; E.conj (defined_facts @ es')] ) |> simplifyBool in
  decrease_debug_depth (); 
  debug "asserting %s" (E.toString e);
  addFactRaw (translate e)

let isTrue e: pbool =
  debug "checking (before rewriting): %s" (E.toString e);
  increase_debug_depth (); 
  let defined_facts, defined_conds = rewrite [isDefined e] in
  let es', e_conds = rewrite [e] in
  let conds = defined_facts @ defined_conds @ e_conds in
  List.iter (warnIfFalse e) conds;
  let e = E.conj (List2.nub (es' @ conds)) |> simplifyBool in
  let result = isTrueRaw e in
  decrease_debug_depth ();
  result


let implies facts hypotheses =

  debug "checking implication: \n  %s\n  =>\n  %s" (E.listToString facts) (E.listToString hypotheses);

  increase_debug_depth ();
  Yices.push ctx;
  List.iter addFact facts;
  let result = List.for_all (isTrue) hypotheses in
  Yices.pop ctx;
  decrease_debug_depth ();
  
  debug "implication result: %b" result;
  
  result
        
(* TODO: change back to equal when it stabilizes *)
let equalBitstring : exp -> exp -> pbool = fun a b -> 
  if a = Unknown || b = Unknown then 
    fail "equal: trying to apply to special length values (Unknown or All)";
  let aId, bId = E.id a, E.id b in
  try PairMap.find (aId, bId) !eqCache 
  with Not_found ->
    let result = isTrue (eqBitstring [a; b]) in
    eqCache := PairMap.add (aId, bId) result !eqCache;
    result

let notEqualBitstring : exp -> exp -> pbool = fun a b -> 
  isTrue (notE (eqBitstring [a; b]))

let greaterEqual : exp -> exp -> pbool = fun a b -> 
  isTrue (ge a b)

let equalInt ?(facts = []) a b =
  if facts = [] then isTrue (eqInt [a; b]) 
  else implies facts [eqInt [a; b]]

let greaterEqualLen : exp -> exp -> pbool = fun a b ->
  greaterEqual a b
  (* match (a, b) with
    | (All, _) -> true
    | (_, All) -> false
    | (Unknown, _) | (_, Unknown) -> false
    | (x, y) -> greaterEqual x y *)

let greaterEqualLenAnswer : len -> len -> answer = fun a b ->
  if greaterEqualLen a b then
    Yes
  else if greaterEqualLen b a then
    No
  else
    Maybe
  
let resetFacts : unit -> unit = fun () -> 
  Yices.reset ctx;
  Yices.parse_command ctx theory; 
  cache := IntMap.empty;
  eqCache := PairMap.empty

let not = notE

(*************************************************)
(** {1 Evaluation.} *)
(*************************************************)

(*
let eval e =
  increase_debug_depth (); 
  
  let es, conds = rewrite [e] in
  let es', e_conds = rewrite [e] in
  let conds = defined_conds @ e_conds in
  List.iter (silent (warnIfFalse e)) conds;
  let e = Sym (Implies, [E.conj conds; E.conj (defined_facts @ es')] ) |> simplifyBool in
  decrease_debug_depth (); 
  debug "asserting %s" (E.toString e);
  addFactRaw (translate e)
*)
  
(* 640 lines *)
