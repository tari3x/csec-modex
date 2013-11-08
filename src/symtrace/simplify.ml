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


let arith_simplify_eq eq want_fold e  =

    let simplify_sums = function
      | Sym ((Plus_int _ | Minus_int), es) as e ->
    
        let elim_zero : exp list -> exp list = fun es -> List.filter_out (eq E.zero) es in
        
        (* The proper way is to make the SMT solver perform the operation *)
        let mk_op : int64 -> (int * exp) -> int64 = fun n -> function
          | (sign, Int m) -> Int64.add n (Int64.mul (Int64.of_int sign) m)
          | _             -> fail "mk_op: not an integer"
        in
  
        let rec signs : int -> exp -> (int * exp) list = fun sign -> function
          | Sym (Plus_int _, es)    -> List.concat_map ~f:(signs sign) es
          | Sym (Minus_int, [a; b]) -> (signs sign a) @ (signs (-1 * sign) b)
          | e -> [(sign, e)]
        in

        let split : exp -> exp list * exp list = fun e ->
          let es = signs 1 e in
          let (e_int, e_sym) = if want_fold then List.partition (function (_, e) -> E.is_integer e) es 
                                         else ([], es) in 
          let (e_pos, e_neg) = List.partition (function (sign, _) -> sign = 1) e_sym in
          let c_int = List.fold_left mk_op 0L e_int in
          ((if c_int = 0L then [] else [Int c_int]) @ List.map snd e_pos, List.map snd e_neg)
        in
        
        let (e_pos, e_neg) = split e in
        begin
          match (elim_zero (List.multidiff eq e_pos e_neg), elim_zero (List.multidiff eq e_neg e_pos)) with
            | (e_pos', [])    -> E.sum e_pos'
            | (e_pos', e_neg') -> Sym (Minus_int, [E.sum e_pos'; E.sum e_neg'])
        end
    
      | e -> e
  in  

  (* TODO: deal with it like you deal with addition *)  
  let elim_one : exp -> exp = function
    | Sym (Mult_int _, es) ->
      E.prod (List.filter_out (eq E.one) es)
      
    | e -> e
  in

  debug "arith_simplify: %s" (E.dump e);
  e (* |> simplify_sums Plus_a Minus_a  *) |> simplify_sums |> elim_one 

(* Not using equal_int as equality, in order not to trigger extra warnings *)
let arith_simplify : exp -> exp = arith_simplify_eq (=) false
let arith_fold     : exp -> exp = arith_simplify_eq (=) true

let op s es =
  arith_simplify (Sym (s, es))

let minus e1 e2 = op Minus_int [e1; e2]
let sum es = E.sum es |> arith_simplify
let prod es = E.prod es |> arith_simplify

let equal_offset : offset -> offset -> S.pbool = function (o_val1, step1) -> function (o_val2, step2) ->
  let eq_val = match o_val1, o_val2 with
    | Index i, Index j -> i = j
    | Flat a, Flat b -> S.equal_int a b
    | Field f, Field g -> f = g
    | Attr f, Attr g -> f = g
    | _ -> false
  in
  eq_val && S.equal_int step1 step2

let is_zero_offset_val : offset_val -> bool = function
  | Index 0 -> true
  | Flat z when S.equal_int E.zero z -> true
  | _ -> false

let is_zero_offset : offset -> bool = function (ov, _) -> is_zero_offset_val ov

let is_field_offset_val : offset_val -> bool = function
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
    let e = Sym (Undef (Var.fresh_id "undef"), []) in 
    S.add_fact (S.eq_int [Len e; l]);
    e
  in

  let mk_concat : exp list -> exp = function
    | [e] -> e
    | es -> Concat es
  in
  
  (* don't think this can be optimised much *)
  let rec concat : exp list -> exp list = function
      (* Concat nesting might give useful hints about message formats, but for now we flatten all concats *)
    | Concat es' :: es -> concat (es' @ es)
    | Range (e1, pos1, len1) :: Range (e2, pos2, len2) :: es
        when S.equal_int pos2 (sum [pos1; len1]) && e1 = e2 ->
      concat (simplify (Range (e1, pos1, sum [len1; len2])) :: es)
    (* FIXME: return string concatenation when you also do corresponding arithmetic simplifications for lengths *) 
    (* | String s1 :: String s2 :: es -> concat (String (s1 ^ s2) :: es) *)
    | e :: es when S.equal_int (Len e) E.zero -> concat es
    | e :: es -> e :: concat es
    | [] -> []

  (* don't think this can be optmised much *)
  and cut : len -> exp list -> (exp list * exp list) option = fun pos es ->
    (* debug ("cut, pos: " ^ E.dump pos);
    debug ("cut, es: " ^ E.dump (Concat es)); *)
    match es with
        (* in case the range extends beyond the end of the expression, we add an undefined chunk *)
      | [] -> Some ((if S.equal_int pos E.zero then [] else [undef pos]), [])
      | e :: es ->
        let l = Len e in 
        match S.greater_equal_len_answer l pos with
        | S.Yes ->
            Some ([simplify (Range (e, E.zero, pos))], 
                   simplify (Range (e, pos, op Minus_int [l; pos])) :: es)
        | S.Maybe -> None
        | S.No -> 
            let pos' = op Minus_int [pos; l] in
            match cut pos' es with
              | Some (es1, es2) -> Some (e :: es1, es2)
              | None -> None
  
  and cut_left : len -> exp list -> exp list option = fun pos es ->
    match cut pos es with
        | Some (left, _) -> Some (concat left)
        | None -> None
  
  and cut_right : len -> exp list -> exp list option = fun pos es ->
    match cut pos es with
        | Some (_, right) -> Some (concat right)
        | None -> None

  and add_pI e_o pos =
    match pos with
    | [Flat b, step] -> [(Flat (sum [b; (prod [step; e_o])]), step)]
    | [Index i, step] -> 
      (* Should not be too eager to concretise because in the parser we may not
         be able to restore the correct general form again. *)
      (* TODO: this should not actually affect parser correctness, think more about this. *)
      let int_value = if E.is_concrete e_o then S.eval e_o else None in 
      begin match int_value with
        | Some j -> [Index (i + j), step]
        | None -> add_pI e_o [Flat (prod [step; (E.int i)]), step]
                    (* fail "add_pI: only concrete integers can be added to index offsets" *)
      end
    | [(o, step)] -> [(o, step); (Flat e_o, step)] (* FIXME: actually need an index here *)
    | o :: os -> o :: add_pI e_o os
    | [] -> fail "add_pI: pointer has no offsets"

  and skip_zeros : pos -> pos = function
    | [os] -> [os]
    | os :: pos' when is_zero_offset os -> skip_zeros pos'
    | pos -> pos

  and flatten_index : pos -> pos = function
    | (Index i, step) :: pos' -> (Flat (prod [step; (E.int i)]), step) :: pos'
    | pos -> pos

  and subtract_pP : pos -> pos -> exp = fun pos1 pos2 ->
    match skip_zeros pos1, skip_zeros pos2 with
      | [Index i, step1], [Index j, step2] ->
        (* 
	        The pointer difference type is ptrdiff_t, which is implementation - dependent.
	        For now, the right thing might be to insert explicit casts during the instrumentation. 
        *)
        if S.equal_int step1 step2 then E.int (i - j) 
        else fail "subtract_pP: pointers have different steps (1)"
        
      | pos1', pos2' -> 
        match flatten_index pos1', flatten_index pos2' with
		      | [Flat a, step1], [Flat b, step2] ->
		        if S.equal_int step1 step2 then op Minus_int [a; b] 
		        else fail "subtract_pP: pointers have different steps (2)" 
        
		      | os1 :: pos1'', os2 :: pos2'' -> 
		        if equal_offset os1 os2 then subtract_pP pos1'' pos2''
		        else fail "subtract_pP: pointers have incompatible offsets (1)"
         
          | _ -> fail "subtract_pP: pointers have incompatible offsets (2)"
  
  and strip_int_cast : exp -> exp = function
    | Sym (Op (Cast_to_int, _), [e]) -> strip_int_cast e
    | e -> e
  in 

  (* TODO: lot of this could be merged with a rewriting step in the solver. *)
  let simplify e_orig =
    match e_orig with
     
    | Sym (Op (Cast_to_ptr, _), [e]) ->
      begin 
      match strip_int_cast e with
        | Ptr (b, pos) -> Ptr (b, pos @ [Index 0, Unknown])
        | Int i   -> Ptr (Abs i, [Index 0, Unknown])
        | _ -> fail "simplify: cast to pointer of non-zero expression: %s" (E.to_string e)
      end

    | Sym (Op (Cast_to_int, ([t2], t3)), [e2]) ->
      let contains t e =
        match t with
        | Bs_int itype -> 
          List.for_all S.is_true (S.Range.contains itype e)
        | _ -> assert false
      in 
      if t2 = t3 then simplify e2 else
      begin match e2 with 
        | Sym (Op (Cast_to_int, ([Bs_int t1],  t2')), [e1]) ->
          assert (t2 = t2');
          if contains t2 (Val (e1, t1)) 
          then Sym (Op (Cast_to_int, ([Bs_int t1], t3)), [e1]) |> simplify
          else e_orig
        | BS (e1, t) ->
          assert (t2 = Bs_int t);
          if contains t2 e1 
          then begin
            match t3 with
            | Bs_int t3 -> BS (e1, t3) |> simplify
            | _ -> assert false
          end
          else e_orig
        | _ -> e_orig
      end
   
    | Val (e2, itype) ->
      begin match e2 with
        | Sym (Op (Cast_to_int, ([Bs_int t1], (Bs_int t2))), [e1]) when S.Range.subset t1 t2 ->
          assert (itype = t2);
          Val (e1, t1) |> simplify
        | BS (e1, itype) when List.for_all S.is_true (S.Range.contains itype e1) -> e1
        | _ -> e_orig
      end
  
    | Sym (Op (Plus_pI,  ([_; Bs_int itype], _)), [Ptr (b, pos); e_o]) ->
      let shift = simplify (Val (e_o, itype)) in
      Ptr (b, add_pI shift pos)
      
    | Sym (Op (Minus_pI, ([_; Bs_int itype], _)), [Ptr (b, pos); e_o]) -> 
      let shift = simplify (Val (e_o, itype)) in
      Ptr (b, add_pI (op Minus_int [E.zero; shift]) pos)
  
    | Sym (Op (Minus_pP, _), [Ptr (b1, pos1); Ptr (b2, pos2)]) -> 
      if b1 <> b2 then
        fail "simplify: trying to subtract pointers with different bases";
      subtract_pP pos1 pos2
  
    | Sym (sym, _) when Sym.is_arithmetic sym -> arith_simplify e_orig
      
    | Sym (Ztp, [Concat es]) ->
      let rec apply_ztp acc = function
        | e :: es when S.equal_bitstring e (E.zero_byte `Signed) -> 
          Sym (Ztp_safe, acc) |> simplify
        | e :: es -> apply_ztp (acc @ [e]) es
        | [] -> e_orig
      in
      apply_ztp [] es
    
    | Sym (Ztp_safe, [e]) when S.equal_bitstring e_orig e -> e 
  
    | Range (e, pos, len) -> 
      begin
        let e_len = Len e in
        let new_len = arith_simplify len in
        let e_new = Range (e, pos, new_len) in
        debug "simplify: e_len = %s" (E.dump e_len);
        debug "simplify: new_len = %s" (E.dump new_len);
        match e with
            (* OLD?: unfortunately e_len is not always known, so we need the disjunction *)
            (* e when S.greater_equal_len new_len e_len -> e *)
          | e when S.equal_int E.zero pos && S.equal_int len e_len -> e 
          | e when S.greater_equal_len E.zero new_len -> Concat []
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
              match cut_right pos es with
                | None -> e_new
                | Some es1 ->
                  (* debug ("cut_right result: " ^ E.dump (Concat es1)); *)
                  match cut_left len es1 with
                    | Some es2 -> 
                      (* debug ("cut_left result:" ^ E.dump (Concat es2)); *) 
                      mk_concat es2
                    | None -> Range (mk_concat es1, E.zero, new_len)
            end
          (* | Range (_, _, len') when len' <> All && len = All -> 
            fail "simplify: e{pos1, l}{pos2, All} with l <> All and pos2 <> 0 is considered suspicious" *)
            (* FIXME: still need to check that new_len is smaller than len' *)
          | Range (e', pos', _) -> simplify (Range (e', sum [pos'; pos], new_len)) 
          (* | Range (e', pos', _) -> simplify (Range (e', L.add_len pos' pos, len)) *)
          
            (* FIXME: need to check that we don't cut the boundary if e_byte has length > 1 *)
          | Sym (Replicate, [e_byte]) -> Sym (Replicate, [e_byte])
          | _ -> e_new 
          (* | _ -> e_orig *) 
      end
  
    | Concat es -> mk_concat (concat es)
  
    | e -> S.simplify e
  in
  
  fun e -> 
    debug "simplify: %s" (E.dump e);
    push_debug "simplify";
    let e = simplify e in
    pop_debug "simplify";
    debug "simplify result: %s" (E.dump e);
    e
  
let rec deep_simplify e = 
  let e = simplify e in
  (* Do not simplify inside function symbols so as not to confuse the solver,
     which treats those as opaque. *)
  match e with
  | Sym (Fun _, _) -> e
  | e -> E.descend deep_simplify e

let rec full_simplify e =
  let e'= deep_simplify e in
  if e' = e then e' else full_simplify e'

let full_simplify e = 
  with_debug "full_simplify" full_simplify e 

(* 280 lines *)

