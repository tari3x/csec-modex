(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec - tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Str
open Int64

open Common
open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Sym.Op.T
open Iml.Exp.T

module E = Iml.Exp
module S = Solver

(******************************************************************)
(** {1 Symbolic Arithmetic Expression Manipulation}               *)
(******************************************************************)


let arithSimplifyEq eq wantFold e  =

    let simplifySums = function
      | Sym ((PlusInt _ | MinusInt), es) as e ->
    
        let elimZero : exp list -> exp list = fun es -> filter_out (eq E.zero) es in
        
        (* The proper way is to make the SMT solver perform the operation *)
        let mkOp : int64 -> (int * exp) -> int64 = fun n -> function
          | (sign, Int m) -> Int64.add n (Int64.mul (Int64.of_int sign) m)
          | _             -> fail "mkOp: not an integer"
        in
  
        let rec signs : int -> exp -> (int * exp) list = fun sign -> function
          | Sym (PlusInt _, es)    -> concat_map (signs sign) es
          | Sym (MinusInt, [a; b]) -> (signs sign a) @ (signs (-1 * sign) b)
          | e -> [(sign, e)]
        in

        let split : exp -> exp list * exp list = fun e ->
          let es = signs 1 e in
          let (eInt, eSym) = if wantFold then List.partition (function (_, e) -> E.isInteger e) es 
                                         else ([], es) in 
          let (ePos, eNeg) = List.partition (function (sign, _) -> sign = 1) eSym in
          let cInt = List.fold_left mkOp 0L eInt in
          ((if cInt = 0L then [] else [Int cInt]) @ List.map snd ePos, List.map snd eNeg)
        in
        
        let (ePos, eNeg) = split e in
        begin
          match (elimZero (multidiff eq ePos eNeg), elimZero (multidiff eq eNeg ePos)) with
            | (ePos', [])    -> E.sum ePos'
            | (ePos', eNeg') -> Sym (MinusInt, [E.sum ePos'; E.sum eNeg'])
        end
    
      | e -> e
  in  

  (* TODO: deal with it like you deal with addition *)  
  let elimOne : exp -> exp = function
    | Sym (MultInt _, es) ->
      E.prod (filter_out (eq E.one) es)
      
    | e -> e
  in

  debug "arithSimplify: %s" (E.dump e);
  e (* |> simplifySums PlusA MinusA  *) |> simplifySums |> elimOne 

(* Not using equalInt as equality, in order not to trigger extra warnings *)
let arithSimplify : exp -> exp = arithSimplifyEq (=) false
let arithFold     : exp -> exp = arithSimplifyEq (=) true

let op s es =
  arithSimplify (Sym (s, es))

let minus e1 e2 = op MinusInt [e1; e2]
let sum es = E.sum es |> arithSimplify
let prod es = E.prod es |> arithSimplify

let equalOffset : offset -> offset -> S.pbool = function (oVal1, step1) -> function (oVal2, step2) ->
  let eqVal = match oVal1, oVal2 with
    | Index i, Index j -> i = j
    | Flat a, Flat b -> S.equalInt a b
    | Field f, Field g -> f = g
    | Attr f, Attr g -> f = g
    | _ -> false
  in
  eqVal && S.equalInt step1 step2

let isZeroOffsetVal : offsetVal -> bool = function
  | Index 0 -> true
  | Flat z when S.equalInt E.zero z -> true
  | _ -> false

let isZeroOffset : offset -> bool = function (ov, _) -> isZeroOffsetVal ov

let isFieldOffsetVal : offsetVal -> bool = function
  | Field _ -> true
  | _ -> false
    
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

  let undef l =
    let e = Sym (Undef (Var.freshId "undef"), []) in 
    S.addFact (S.eqInt [Len e; l]);
    e
  in

  let mkConcat : exp list -> exp = function
    | [e] -> e
    | es -> Concat es
  in
  
  (* don't think this can be optimised much *)
  let rec concat : exp list -> exp list = function
      (* Concat nesting might give useful hints about message formats, but for now we flatten all concats *)
    | Concat es' :: es -> concat (es' @ es)
    | Range (e1, pos1, len1) :: Range (e2, pos2, len2) :: es
        when S.equalInt pos2 (sum [pos1; len1]) && e1 = e2 ->
      concat (simplify (Range (e1, pos1, sum [len1; len2])) :: es)
    (* FIXME: return string concatenation when you also do corresponding arithmetic simplifications for lengths *) 
    (* | String s1 :: String s2 :: es -> concat (String (s1 ^ s2) :: es) *)
    | e :: es when S.equalInt (Len e) E.zero -> concat es
    | e :: es -> e :: concat es
    | [] -> []

  (* don't think this can be optmised much *)
  and cut : len -> exp list -> (exp list * exp list) option = fun pos es ->
    (* debug ("cut, pos: " ^ E.dump pos);
    debug ("cut, es: " ^ E.dump (Concat es)); *)
    match es with
        (* in case the range extends beyond the end of the expression, we add an undefined chunk *)
      | [] -> Some ((if S.equalInt pos E.zero then [] else [undef pos]), [])
      | e :: es ->
        let l = Len e in 
        match S.greaterEqualLenAnswer l pos with
        | S.Yes ->
            Some ([simplify (Range (e, E.zero, pos))], 
                   simplify (Range (e, pos, op MinusInt [l; pos])) :: es)
        | S.Maybe -> None
        | S.No -> 
            let pos' = op MinusInt [pos; l] in
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

  and addPI e_o pos =
    match pos with
    | [Flat b, step] -> [(Flat (sum [b; (prod [step; e_o])]), step)]
    | [Index i, step] -> 
      (* Should not be too eager to concretise because in the parser we may not
         be able to restore the correct general form again. *)
      (* TODO: this should not actually affect parser correctness, think more about this. *)
      let int_value = if E.isConcrete e_o then S.eval e_o else None in 
      begin match int_value with
        | Some j -> [Index (i + j), step]
        | None -> addPI e_o [Flat (prod [step; (E.int i)]), step]
                    (* fail "addPI: only concrete integers can be added to index offsets" *)
      end
    | [(o, step)] -> [(o, step); (Flat e_o, step)] (* FIXME: actually need an index here *)
    | o :: os -> o :: addPI e_o os
    | [] -> fail "addPI: pointer has no offsets"

  and skipZeros : pos -> pos = function
    | [os] -> [os]
    | os :: pos' when isZeroOffset os -> skipZeros pos'
    | pos -> pos

  and flattenIndex : pos -> pos = function
    | (Index i, step) :: pos' -> (Flat (prod [step; (E.int i)]), step) :: pos'
    | pos -> pos

  and subtractPP : pos -> pos -> exp = fun pos1 pos2 ->
    match skipZeros pos1, skipZeros pos2 with
      | [Index i, step1], [Index j, step2] ->
        (* 
	        The pointer difference type is ptrdiff_t, which is implementation - dependent.
	        For now, the right thing might be to insert explicit casts during the instrumentation. 
        *)
        if S.equalInt step1 step2 then E.int (i - j) 
        else fail "subtractPP: pointers have different steps (1)"
        
      | pos1', pos2' -> 
        match flattenIndex pos1', flattenIndex pos2' with
		      | [Flat a, step1], [Flat b, step2] ->
		        if S.equalInt step1 step2 then op MinusInt [a; b] 
		        else fail "subtractPP: pointers have different steps (2)" 
        
		      | os1 :: pos1'', os2 :: pos2'' -> 
		        if equalOffset os1 os2 then subtractPP pos1'' pos2''
		        else fail "subtractPP: pointers have incompatible offsets (1)"
         
          | _ -> fail "subtractPP: pointers have incompatible offsets (2)"
  
  and stripIntCast : exp -> exp = function
    | Sym (Op (CastToInt, _), [e]) -> stripIntCast e
    | e -> e
  in 

  (* TODO: lot of this could be merged with a rewriting step in the solver. *)
  let simplify e_orig =
    match e_orig with
     
    | Sym (Op (CastToPtr, _), [e]) ->
      begin 
      match stripIntCast e with
        | Ptr (b, pos) -> Ptr (b, pos @ [Index 0, Unknown])
        | Int i   -> Ptr (Abs i, [Index 0, Unknown])
        | _ -> fail "simplify: cast to pointer of non-zero expression: %s" (E.toString e)
      end

    | Sym (Op (CastToInt, ([t2], t3)), [e2]) ->
      let contains t e =
        match t with
        | BsInt itype -> 
          List.for_all S.isTrue (S.Range.contains itype e)
        | _ -> assert false
      in 
      if t2 = t3 then simplify e2 else
      begin match e2 with 
        | Sym (Op (CastToInt, ([BsInt t1],  t2')), [e1]) ->
          assert (t2 = t2');
          if contains t2 (Val (e1, t1)) 
          then Sym (Op (CastToInt, ([BsInt t1], t3)), [e1]) |> simplify
          else e_orig
        | BS (e1, t) ->
          assert (t2 = BsInt t);
          if contains t2 e1 
          then begin
            match t3 with
            | BsInt t3 -> BS (e1, t3) |> simplify
            | _ -> assert false
          end
          else e_orig
        | _ -> e_orig
      end
   
    | Val (e2, itype) ->
      begin match e2 with
        | Sym (Op (CastToInt, ([BsInt t1], (BsInt t2))), [e1]) when S.Range.subset t1 t2 ->
          assert (itype = t2);
          Val (e1, t1) |> simplify
        | BS (e1, itype) when List.for_all S.isTrue (S.Range.contains itype e1) -> e1
        | _ -> e_orig
      end
  
    | Sym (Op (PlusPI,  ([_; BsInt itype], _)), [Ptr (b, pos); e_o]) ->
      let shift = simplify (Val (e_o, itype)) in
      Ptr (b, addPI shift pos)
      
    | Sym (Op (MinusPI, ([_; BsInt itype], _)), [Ptr (b, pos); e_o]) -> 
      let shift = simplify (Val (e_o, itype)) in
      Ptr (b, addPI (op MinusInt [E.zero; shift]) pos)
  
    | Sym (Op (MinusPP, _), [Ptr (b1, pos1); Ptr (b2, pos2)]) -> 
      if b1 <> b2 then
        fail "simplify: trying to subtract pointers with different bases";
      subtractPP pos1 pos2
  
    | Sym (sym, _) when Sym.isArithmetic sym -> arithSimplify e_orig
      
    | Sym (Ztp, [Concat es]) ->
      let rec applyZtp acc = function
        | e :: es when S.equalBitstring e (E.zeroByte IntType.Signed) -> 
          Sym (ZtpSafe, acc) |> simplify
        | e :: es -> applyZtp (acc @ [e]) es
        | [] -> e_orig
      in
      applyZtp [] es
    
    | Sym (ZtpSafe, [e]) when S.equalBitstring e_orig e -> e 
  
    | Range (e, pos, len) -> 
      begin
        let e_len = Len e in
        let new_len = arithSimplify len in
        let e_new = Range (e, pos, new_len) in
        debug "simplify: e_len = %s" (E.dump e_len);
        debug "simplify: new_len = %s" (E.dump new_len);
        match e with
            (* OLD?: unfortunately e_len is not always known, so we need the disjunction *)
            (* e when S.greaterEqualLen new_len e_len -> e *)
          | e when S.equalInt E.zero pos && S.equalInt len e_len -> e 
          | e when S.greaterEqualLen E.zero new_len -> Concat []
          | String s -> 
            begin
              match (S.eval pos, S.eval new_len) with
                | (Some pos_val, Some len_val) ->
                  let s_len_val = String.length s / 2 in
                  if pos_val + len_val <= s_len_val then
                    String (String.sub s (2 * pos_val) (2 * len_val))
                  else 
                    Concat [String (String.sub s (2 * pos_val) (String.length s - 2 * pos_val)); 
                            undef (E.int (len_val + pos_val - s_len_val))]
                | _ -> e_new
            end
          | Concat es -> 
            begin
              match cutRight pos es with
                | None -> e_new
                | Some es1 ->
                  (* debug ("cutRight result: " ^ E.dump (Concat es1)); *)
                  match cutLeft len es1 with
                    | Some es2 -> 
                      (* debug ("cutLeft result:" ^ E.dump (Concat es2)); *) 
                      mkConcat es2
                    | None -> Range (mkConcat es1, E.zero, new_len)
            end
          (* | Range (_, _, len') when len' <> All && len = All -> 
            fail "simplify: e{pos1, l}{pos2, All} with l <> All and pos2 <> 0 is considered suspicious" *)
            (* FIXME: still need to check that new_len is smaller than len' *)
          | Range (e', pos', _) -> simplify (Range (e', sum [pos'; pos], new_len)) 
          (* | Range (e', pos', _) -> simplify (Range (e', L.addLen pos' pos, len)) *)
          
            (* FIXME: need to check that we don't cut the boundary if e_byte has length > 1 *)
          | Sym (Replicate, [e_byte]) -> Sym (Replicate, [e_byte])
          | _ -> e_new 
          (* | _ -> e_orig *) 
      end
  
    | Concat es -> mkConcat (concat es)
  
    | e -> e
  in
  
  fun e -> 
    debug "simplify: %s" (E.dump e);
    increase_debug_depth ();
    let e = simplify e in
    decrease_debug_depth ();
    debug "simplify result: %s" (E.dump e);
    e
  

let rec deepSimplify e = simplify (E.descend deepSimplify e) 


(* 280 lines *)

