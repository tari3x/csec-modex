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

let isAuxiliary = function
  | Int _ | Len _ | String _ | Val _ | BS _ -> true
  | Sym (sym, _) when Sym.isArithmetic sym || Sym.resultType sym = Bool -> true
  | Sym (Op (CastToInt, _), _) -> true
  | _ -> false

let mkCmp e1 e2 =
    if isAuxiliary e1 || isAuxiliary e2 then
      AuxTest (Sym (BsEq, [e1; e2]))
    else 
      TestEq (e1, e2)


let makeAuxiliary : stmt -> stmt = function
  | GenTest (Sym ((Not, [Sym (Op (Ne, itype), [e1; e2])]))) -> AuxTest (Sym (Op (Eq, itype), [e1; e2]))

  | GenTest (Sym (Op (Eq, _), [Sym (Fun ("cmp", _), [e1; e2]); z])) when S.equalInt z E.zero -> mkCmp e1 e2

  | GenTest (Sym ((Not, [Sym (Fun ("cmp", _), [e1; e2])]))) -> mkCmp e1 e2
    
  | GenTest e when isAuxiliary e -> AuxTest e

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



(*************************************************)
(** {1 Cast simplification} *)
(*************************************************)

let simplifyCasts p =

  let rec simplifyDouble = function
    | Sym (Op (CastToInt, ([BsInt (sd_from, wd_from)], BsInt (sd_to, wd_to))), 
           [Sym (Op (CastToInt, ([BsInt (sd_from', wd_from')], BsInt (sd_to', wd_to'))), [e])]) 
      when wd_to >= wd_from' ->
      Sym (Op (CastToInt, ([BsInt (sd_from', wd_from')], BsInt (sd_to, wd_to))), [e]) |> simplifyDouble
      
    | Sym (Op (CastToInt, ([itype_from], itype_to)), [e]) when itype_from = itype_to -> 
      simplifyDouble e
      
    | e -> E.descend simplifyDouble e
  in
  
  let removeOuter = function
    | Sym (Op (CastToInt, ([BsInt (sd_from, wd_from)], BsInt (sd_to, wd_to))), [e]) when sd_from = sd_to && wd_from <= wd_to -> e
    | e -> e
  in
  
  let rec simplifyOuter = function
    | Range(e, p, l) -> Range (e, removeOuter p, removeOuter l) |> E.descend simplifyOuter
    | e -> E.descend simplifyOuter e
  in
  
  p |> Iml.map simplifyDouble |> Iml.map simplifyOuter
  
(* 160 lines *)
