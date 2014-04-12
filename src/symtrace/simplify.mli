open Iml
open Iml.Exp
open Iml.Sym

val simplify : 'a Exp.t -> 'a Exp.t

val minus : iterm -> iterm -> iterm
val sum : iterm list -> iterm
val prod : iterm list -> iterm

(** Does not do constant folding - this way we might see more about the history of the
    expression. *)
val arith_simplify : iterm -> iterm

(** This is supposed to additionally perform constant folding. *)
val arith_fold : iterm -> iterm

(*************************************************)
(** {1 Testing.} *)
(*************************************************)

val test : unit -> unit

(*---------------------------
  To be removed
-----------------------------*)

val is_zero_offset_val : offset_val -> bool
val is_field_offset_val : offset_val -> bool

val full_simplify : 'a Exp.t -> 'a Exp.t
