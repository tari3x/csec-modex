(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Iml
open Iml.Type
open Iml.Sym
open Iml.Exp

type answer = Yes | No | Maybe

(**
    [true] means true, [false] means we don't know.
*)
type pbool = bool

(*************************************************)
(** {1 Building facts} *)
(*************************************************)

val eq_bitstring : bterm list -> fact
val eq_int : iterm list -> fact
val not : fact -> fact
val gt : iterm -> iterm -> fact
val ge : iterm -> iterm -> fact

val is_defined : _ exp -> fact

val true_fact : fact

val in_type : bterm -> bitstring Type.t -> fact

module Range : sig
  type t = Int_type.t

  val contains : t -> iterm -> fact list
  val subset : t -> t -> bool
end


(*************************************************)
(** {1 Checking facts} *)
(*************************************************)

val add_fact : fact -> unit

val reset_facts : unit -> unit

val is_true : fact -> pbool

val equal_bitstring : bterm -> bterm -> pbool

val not_equal_bitstring : bterm -> bterm -> pbool

(** Comparison is done on numeric values. *)
val equal_int : ?facts:fact list -> iterm -> iterm -> pbool

val greater_equal : iterm -> iterm -> pbool

val greater_equal_len : iterm -> iterm -> pbool

val greater_equal_len_answer : iterm -> iterm -> answer

val implies : fact list -> fact list -> pbool

(*************************************************)
(** {1 Evaluation} *)
(*************************************************)

(**
  Evaluation of an integer expression.
  Will fail if a value is not unique or if we cannot prove that it is defined.
*)
val eval : iterm -> int option

(*************************************************)
(** {1 Simplification} *)
(*************************************************)

(* CR get rid of stepwise simplification, that's premature optimization. *)
(** Only simplifies the topmost constructor. *)
val simplify : 'a exp -> 'a exp

(** If an expression is opaque, then the simplifier does not understand its structure.  In
    particular, the solver cannot tell that simplifications inside the expression preserve
    equality. *)
val is_opaque : _ exp -> bool

(*************************************************)
(** {1 Warnings} *)
(*************************************************)

val warn_on_failed_conditions : bool -> unit

(*************************************************)
(** {1 Test} *)
(*************************************************)

val test : unit -> unit

