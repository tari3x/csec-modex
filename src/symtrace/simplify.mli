
open Iml.Exp.T
open Iml.Sym.T

val simplify: exp -> exp

val minus: exp -> exp -> exp
val sum: exp list -> exp
val prod: exp list -> exp

(**
    Does not do constant folding - this way we might see more about the history of the expression. 
*)
val arith_simplify : exp -> exp
  
(**
    This is supposed to additionally perform constant folding.
*)
val arith_fold : exp -> exp

(*---------------------------
  To be removed
-----------------------------*)

val is_zero_offset_val : offset_val -> bool
val is_field_offset_val : offset_val -> bool

val full_simplify: exp -> exp
