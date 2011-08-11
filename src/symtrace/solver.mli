 
open Types

val addFact : exp -> unit 

val equal : exp -> exp -> pbool

val notEqual : exp -> exp -> pbool

(** Comparison is done on numeric values. *)
val equalLen : len -> len -> pbool

val greaterEqual : exp -> exp -> pbool

val greaterEqualLen : len -> len -> pbool

val greaterEqualLenAnswer : len -> len -> answer

(**
    Does not do constant folding - this way we might see more about the history of the expression. 
*)
val arithSimplify : exp -> exp

(**
    This is supposed to additionally perform constant folding.
*)
val arithFold : exp -> exp
