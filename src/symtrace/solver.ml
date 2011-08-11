(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open Types

include Solver_yices

(*
let addFact : exp -> unit = Solver_yices.addFact

let equal : exp -> exp -> pbool = fun a b -> Solver_simple.equal a b || Solver_yices.equal a b

let notEqual : exp -> exp -> pbool = fun a b -> Solver_simple.notEqual a b || Solver_yices.notEqual a b

let equalLen : len -> len -> pbool = fun a b -> Solver_simple.equalLen a b || Solver_yices.equalLen a b

let greaterEqual : exp -> exp -> pbool = fun a b -> Solver_simple.greaterEqual a b || Solver_yices.greaterEqual a b

let greaterEqualLen : len -> len -> pbool = fun a b -> Solver_simple.greaterEqualLen a b || Solver_yices.greaterEqualLen a b

let greaterEqualLenAnswer : len -> len -> answer = fun a b ->
  match Solver_simple.greaterEqualLenAnswer a b with
    | Maybe -> Solver_yices.greaterEqualLenAnswer a b
    | x -> x
*)

let arithSimplify : exp -> exp = Simplify.arithSimplifyEq equal false
let arithFold     : exp -> exp = Simplify.arithSimplifyEq equal true
