(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Exp.T

type answer = Yes | No | Maybe

(**
    [true] means true, [false] means we don't know.
*)
type pbool = bool

type fact = exp

(*************************************************)
(** {1 Building facts} *)
(*************************************************)

val eqBitstring: exp list -> fact
val eqInt: exp list -> fact
val not : fact -> fact
val gt : exp -> exp -> fact 
val ge : exp -> exp -> fact


val isDefined: exp -> fact

val trueFact : fact

val inType: exp -> imltype -> fact 
  
module Range : sig
  type t = IntType.t 
  
  val contains : t -> exp -> fact list
  val subset : t -> t -> bool 
end
  
  
(*************************************************)
(** {1 Checking facts} *)
(*************************************************)


val addFact : fact -> unit 

val resetFacts : unit -> unit

val isTrue: fact -> pbool

val equalBitstring : exp -> exp -> pbool

val notEqualBitstring : exp -> exp -> pbool

(** Comparison is done on numeric values. *)
val equalInt : ?facts:fact list -> len -> len -> pbool

val greaterEqual : exp -> exp -> pbool

val greaterEqualLen : len -> len -> pbool

val greaterEqualLenAnswer : len -> len -> answer

val implies: fact list -> fact list -> pbool
  
(*************************************************)
(** {1 Evaluation} *)
(*************************************************)

(** 
  Try evaluation an integer expression.
  Will fail if a value is not unique. 
*)
val eval: exp -> int option
