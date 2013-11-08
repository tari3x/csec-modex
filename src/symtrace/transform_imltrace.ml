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
open Iml.Pat.T
open Iml.Stmt.T

module E = Iml.Exp
module S = Solver

(*************************************************)
(** {1 Comments} *)
(*************************************************)

let filter_with_comments f p =
  let rec filter = function
    | Comment c :: s :: p when not (f s) -> filter p
    | s :: p when not (f s) -> filter p
    | s :: p -> s :: filter p
    | [] -> []
  in
  filter p
  
let rec remove_comments = function
  | Comment _ :: p -> remove_comments p
  | s :: p -> s :: remove_comments p
  | [] -> []
  
(*************************************************)
(** {1 Auxiliary Statements} *)
(*************************************************)

let rec is_cryptographic = function
  | Var _ | Range _ | Concat _ | Sym (Fun _, _) -> true
  | Annotation (_, e) -> is_cryptographic e
  | _ -> false

let is_auxiliary_test e =
  match e with
  | Sym (Bs_eq, [e1; e2]) when is_cryptographic e1 && is_cryptographic e2 -> false 
  | _ -> true

let mk_cmp e1 e2 =
  let e = (Sym (Bs_eq, [e1; e2])) in
  if is_auxiliary_test e 
  then Aux_test e
  else Test_eq (e1, e2)


let make_auxiliary : stmt -> stmt = function
  | Test (Sym ((Not, [Sym (Op (Ne, itype), [e1; e2])]))) -> Aux_test (Sym (Op (Eq, itype), [e1; e2]))

  | Test (Sym (Op (Eq, _), [Sym (Fun ("cmp", _), [e1; e2]); z])) when S.equal_int z E.zero -> mk_cmp e1 e2

  | Test (Sym ((Not, [Sym (Fun ("cmp", _), [e1; e2])]))) -> mk_cmp e1 e2
    
  | Test (Sym (Bs_eq, [e1; e2])) -> mk_cmp e1 e2
    
  | Test e when is_auxiliary_test e -> Aux_test e

  | s -> s

                  
let rec map_without_auxiliary f = function
  | (Aux_test _ | Assume _) as s :: p -> s :: map_without_auxiliary f p
  | s :: p ->
    (* enforce evaluation order *)
    let s' = Stmt.descend f s in   
    s' :: map_without_auxiliary f p
  | [] -> []
  
let rec remove_auxiliary = function
  | (Aux_test _ | Assume _) :: p -> remove_auxiliary p
  | s :: p -> s :: remove_auxiliary p
  | [] -> []

  
let proc_and_filter es = (* filter_with_comments interesting_stmt *) (List.map make_auxiliary es)

  
(* 90 lines *)
