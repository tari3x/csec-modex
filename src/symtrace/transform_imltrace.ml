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

let filterWithComments f p =
  let rec filter = function
    | Comment c :: s :: p when not (f s) -> filter p
    | s :: p when not (f s) -> filter p
    | s :: p -> s :: filter p
    | [] -> []
  in
  filter p
  
let rec removeComments = function
  | Comment _ :: p -> removeComments p
  | s :: p -> s :: removeComments p
  | [] -> []
  
  
  
(*************************************************)
(** {1 Auxiliary Statements} *)
(*************************************************)

let isCryptographic = function
  | Var _ | Range _ | Concat _ | Sym (Fun _, _) -> true
  | _ -> false

let isAuxiliaryTest e =
  match e with
  | Sym (BsEq, [e1; e2]) when isCryptographic e1 && isCryptographic e2 -> false 
  | _ -> true

let mkCmp e1 e2 =
  let e = (Sym (BsEq, [e1; e2])) in
  if isAuxiliaryTest e 
  then AuxTest e
  else TestEq (e1, e2)


let makeAuxiliary : stmt -> stmt = function
  | Test (Sym ((Not, [Sym (Op (Ne, itype), [e1; e2])]))) -> AuxTest (Sym (Op (Eq, itype), [e1; e2]))

  | Test (Sym (Op (Eq, _), [Sym (Fun ("cmp", _), [e1; e2]); z])) when S.equalInt z E.zero -> mkCmp e1 e2

  | Test (Sym ((Not, [Sym (Fun ("cmp", _), [e1; e2])]))) -> mkCmp e1 e2
    
  | Test (Sym (BsEq, [e1; e2])) -> mkCmp e1 e2
    
  | Test e when isAuxiliaryTest e -> AuxTest e

  | s -> s

                  
let rec mapWithoutAuxiliary f = function
  | (AuxTest _ | Assume _) as s :: p -> s :: mapWithoutAuxiliary f p
  | s :: p ->
    (* enforce evaluation order *)
    let s' = Stmt.descend f s in   
    s' :: mapWithoutAuxiliary f p
  | [] -> []
  
let rec removeAuxiliary = function
  | (AuxTest _ | Assume _) :: p -> removeAuxiliary p
  | s :: p -> s :: removeAuxiliary p
  | [] -> []

  
let procAndFilter es = (* filterWithComments interestingStmt *) (List.map makeAuxiliary es)

  
(* 90 lines *)
