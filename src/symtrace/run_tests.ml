
let setup_debug () =
  Common.set_debug (fun labels ->
    (* List.length labels <= 1 *)
    false
  )

let main () =
  setup_debug ();
  Solver.test ();
  Transform.test ()

;;

begin
  try main () with
    Failure s -> begin
      print_endline s;
      exit 1;
    end
end
