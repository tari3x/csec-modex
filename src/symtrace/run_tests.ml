open Common

let setup_debug () =
  set_debug (fun labels ->
    let _at_most_n_under n l =
      match List.find_index ((=) l) labels with
      | None -> false
      | Some i -> i <= n
    in
    false
    (* _at_most_n_under (2) "Simplify.test"*)
    (* _at_most_n_under (3) "Simplify.test_simplify_bs_arithmetic"; *)
  (* List.length labels <= 2 *)
  )

let main () =
  setup_debug ();
  Solver.test ();
  Simplify.test ();
  Transform.test ()

;;

(*
  Trying to get both the full text of the exception and
  the backtrace. Waiting for a fix for
  http://caml.inria.fr/mantis/view.php?id=5040
*)

Printexc.register_printer (function
  | Failure s -> Some s
  | _ -> None);
;;

Printexc.print main ()
