
(* UNUSED *)
 
open String
open List

open Common

(* 
(* ocaml orderings don't seem to agree with what shell comm expects *) 
let lowcase_compare : string -> string -> int = fun s1 s2 -> compare (lowercase s1) (lowercase s2)
*) 

;;
readConfig Sys.argv.(1);
iter print_endline !opaqueNames
