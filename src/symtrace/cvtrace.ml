open Common

(*
  Trying to get both the full text of the exception and
  the backtrace. Waiting for a fix for
  http://caml.inria.fr/mantis/view.php?id=5040
*)

let setup_debug () =
  set_debug (fun labels ->
    let at_most_n_under n l =
      match List.find_index ((=) l) labels with
      | None -> false
      | Some i -> i <= n
    in
    at_most_n_under (-1) "Typing.check"
    || at_most_n_under (-1) "Custom_map.find"
    || at_most_n_under (-1) "Typing.check_robust_safety"
    || at_most_n_under (-1) "parsing_eqs"
    || at_most_n_under (-1) "auxiliary_facts"
    || at_most_n_under (-1) "parsing_safety"
    || at_most_n_under (-1) "inrange"
    || at_most_n_under (-1) "remove_redundant_auxiliary"
    || at_most_n_under (-1) "parsing_eqs"
    || at_most_n_under (-1) "encoder_facts"
    || at_most_n_under (-1) "match_inverse"

    (* || at_most_n_under (1) "Custom_map.find" *)

(*
    || List.length labels <= 1
*)
  )
;;

Printexc.register_printer (function
  | Failure s -> Some s
  | _ -> None);
;;

setup_debug ()

;;

Printexc.print Cv_transform.main ()

