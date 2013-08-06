
open Iml.Exp.T
open Iml.Sym.T

val simplify: exp -> exp

val minus: exp -> exp -> exp
val sum: exp list -> exp
val prod: exp list -> exp

(**
    Does not do constant folding - this way we might see more about the history of the expression. 
*)
val arithSimplify : exp -> exp
  
(**
    This is supposed to additionally perform constant folding.
*)
val arithFold : exp -> exp

(*---------------------------
  To be removed
-----------------------------*)

val isZeroOffsetVal : offsetVal -> bool
val isFieldOffsetVal : offsetVal -> bool

val deepSimplify: exp -> exp
