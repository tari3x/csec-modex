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

val eq_bitstring: exp list -> fact
val eq_int: exp list -> fact
val not : fact -> fact
val gt : exp -> exp -> fact
val ge : exp -> exp -> fact

val is_defined: exp -> fact

val true_fact : fact

val in_type: exp -> imltype -> fact

module Range : sig
  type t = Int_type.t

  val contains : t -> exp -> fact list
  val subset : t -> t -> bool
end


(*************************************************)
(** {1 Checking facts} *)
(*************************************************)

val add_fact : fact -> unit

val reset_facts : unit -> unit

val is_true: fact -> pbool

val equal_bitstring : exp -> exp -> pbool

val not_equal_bitstring : exp -> exp -> pbool

(** Comparison is done on numeric values. *)
val equal_int : ?facts:fact list -> len -> len -> pbool

val greater_equal : exp -> exp -> pbool

val greater_equal_len : len -> len -> pbool

val greater_equal_len_answer : len -> len -> answer

val implies: fact list -> fact list -> pbool

(*************************************************)
(** {1 Evaluation} *)
(*************************************************)

(**
  Evaluation of an integer expression.
  Will fail if a value is not unique or if we cannot prove that it is defined.
*)
val eval : exp -> int option

(*************************************************)
(** {1 Simplification} *)
(*************************************************)

(** Only simplifies the topmost constructor. *)
val simplify : exp -> exp

(** If an expression is opaque, then the simplifier does not understand its structure.
    In particular, the solver cannot tell that simplifications inside the expression preserve equality. *)
val is_opaque : exp -> bool

(*************************************************)
(** {1 Warnings} *)
(*************************************************)

val warn_on_failed_conditions : bool -> unit

(*************************************************)
(** {1 Warnings} *)
(*************************************************)

val test : unit -> unit

