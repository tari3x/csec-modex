(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(* September 2010: not used or maintained anymore *)

open List

open Types
open Utils
open Simplify

(******************************************************************)
(** {1 State}                                                     *)
(******************************************************************)

(** Equivalence classes of expressions by equality *)
let eqs : exp list list ref = ref []


(******************************************************************)
(** {1 Symbolic Arithmetic Expression Manipulation}               *)
(******************************************************************)

(* let lenLen : len = Len (Int(8L, All)) *)


(** Simple equality of two expressions without trying to use the fact repository *)
let rec simpleEq : exp -> exp -> bool = fun a b ->

  let rec flattenSums : exp -> exp list = function
    | Sym (("+", _), es, _, _) -> concat (map flattenSums es)
    | e -> [e]
  in
  
  (* 
    Discard the length field when we know that this doesn't change the value.
    This can only be done for integers under the assumption that they never get truncated.
    
    For symbols discarding length is never a problem, because two symbols are equal iff their
    names, arguments and ids are equal.
  *) 
  let discardLen : exp -> exp = function
    | Sym (sym, args, len, id) -> Sym (sym, args, All, id)
    | Int (i, _) -> Int (i, All)
    | e -> e
  in
  
  (*
    Discard a truncation if we know that it doesn't change the value.
  *)
  let discardCast : exp -> exp = function
    | Range (e, pos, len) when equalLen pos zeroLen && greaterEqualLen len (effectiveLen e) -> e
    | e -> e
  in

  let normalise : exp -> exp list = fun x -> 
    (* debug ("simpleEq, normalising  " ^ dump x ^ ", hint = " ^ let m = getMeta a in m.hint); *)
    (* discardLen and discardCast come in this order, because effectiveLen depends on length *)
    sort Pervasives.compare (flattenSums (visitExpPost discardLen (visitExpPost discardCast x)))
  in
  (*
  debug ("simpleEq, a: " ^ dump a ^ ", hint = " ^ let m = getMeta a in m.hint);
  debug ("simpleEq, b: " ^ dump b ^ ", hint = " ^ let m = getMeta b in m.hint);
  *)
  let na = normalise a in
  let nb = normalise b in  
  (*
  debug ("simpleEq, normalise a: " ^ "[" ^ String.concat ", "  (map dump na) ^ "]");
  debug ("simpleEq, normalise b: " ^ "[" ^ String.concat ", "  (map dump nb) ^ "]");
  *)
  na = nb

(*
and addFact : exp -> unit = function 
	  | Sym (("==", _), es, _, _) -> 
		  (* debug ("addEqFact, es: " ^ "[" ^ String.concat ", "  (map dump es) ^ "]"); *)
		  
		  let rec add : exp list list -> exp list list = function
		    | eq :: eqs ->
		      if exists (fun e -> exists (simpleEq e) es) eq then
		        (eq @ es) :: eqs (* FIXME: a nup would be good *)
		      else
		        eq :: add eqs
		    | [] -> [es]
      in
      eqs := add !eqs
      
	  | _ -> ()

and queryEqFact : exp -> exp -> bool = fun a b ->

  (* debug ("queryEqFact, a: " ^ dump a);
  debug ("queryEqFact, b: " ^ dump b);
  debug ("queryEqFact, eqs: " ^ "[" ^ String.concat ", " 
    (map (fun eq -> "[" ^ String.concat ", "  (map dump eq) ^ "]") !eqs) ^ "]"); *)

  let rec check : exp list list -> exp list list -> bool = fun xs -> function
    | []    -> eqs := xs; false
    | y::ys -> 
      eqs := xs @ ys; (* when we test with the equivalence class y, we remove y itself for termination *)
      if exists (simpleEq a) y && exists (simpleEq b) y then true
      else check (xs @ [y]) ys
  in
  
  check [] !eqs
*)

and equal : exp -> exp -> pbool = fun a b -> 
  let result = simpleEq a b (* || queryEqFact a b *) in
  debug ("checking (simple) " ^ dump a ^ " == " ^ dump b ^ ", result (simple) = " ^ string_of_bool result);
  result
  
and equalLen : len -> len -> pbool = fun a b ->
  match (a, b) with
    | (Len x, Len y) -> equal x y
    | _              -> false

and greaterEqualAnswer : exp -> exp -> answer = fun a b ->
  (*debug ("greaterEqual, a: " ^ dump a ^ ", hint = " ^ let m = getMeta a in m.hint);
  debug ("greaterEqual, b: " ^ dump b ^ ", hint = " ^ let m = getMeta b in m.hint); *)

  match (getIntVal a, getIntVal b) with
    | (Some a_val, Some b_val) -> if a_val >= b_val then Yes else No
    | _ -> if equal a b then Yes else Maybe

and greaterEqualLenAnswer : len -> len -> answer = fun a b ->
  match (a, b) with
    | (All, _)     -> Yes
    | (_, Len l) when getIntVal l = Some 0 -> Yes (* making the assumption that lengths are positive *)
    | (Len _, All) -> Maybe
    | (Len x, Len y) -> 
	      (* using positivity of lengths *)
	      if isPositiveDiff x y then Yes else
	      if isPositiveDiff y x then No  else
	      greaterEqualAnswer x y 

and greaterEqual : exp -> exp -> pbool = fun a b -> match greaterEqualAnswer a b with
  | Yes -> true
  | _   -> false

and greaterEqualLen : len -> len -> pbool = fun a b -> match greaterEqualLenAnswer a b with
  | Yes -> true
  | _   -> false

and isPositiveDiff : exp -> exp -> pbool = fun ePos eNeg -> 
  match arithSimplifyEq equal (Sym (("-", Infix), [ePos; eNeg], All, 0)) with
    | (Sym (("-", _), _, _, _)) -> false
    | _ -> true

let notEqual : exp -> exp -> pbool = fun a b -> false

