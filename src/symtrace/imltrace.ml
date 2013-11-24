(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Iml
open Exp
open Symex

open Transform_imltrace

let setup_debug () =
  set_debug (fun labels ->
    let at_most_n_under n l =
      match List.find_index ((=) l) labels with
      | None -> false
      | Some i -> i <= n
    in
    let under l =  List.mem l labels in
    under "dummy"
    || at_most_n_under 0 "execute"
    (* || at_most_n_under 0 "deep_simplify" *)
    (* || at_most_n_under 0 "rewrite" *)
    (* || under "rewrite" *)
    || false)

let main () =
  setup_debug ();

  let client = execute_file (open_in Sys.argv.(1)) in
  let server = execute_file (open_in Sys.argv.(2)) in

  (*
    Iml.Exp.clip_enabled := false;
  *)

  (*
    if debug_enabled () then prerr_endline "";
    if debug_enabled () then List.iter (fun s -> prerr_endline (Stmt.dump s)) client;
    if debug_enabled () then List.iter (fun s -> prerr_endline (Stmt.dump s)) server;
  *)
  if debug_enabled () then prerr_endline "";
  if debug_enabled () then prerr_endline (Iml.to_string client);
  if debug_enabled () then prerr_endline (Iml.to_string server);
  if debug_enabled () then prerr_endline "";

  let client = client |> proc_and_filter in
  let server = server |> proc_and_filter in

  print_endline "let A = ";
  print_endline (Iml.to_string client);
  print_endline "let B = ";
  print_endline (Iml.to_string server);

  raw_out (open_out_bin Sys.argv.(3)) client server;

  dump_called_funs ();

;;
begin
  try main () with
    Failure s -> begin
      print_endline s;
      exit 1;
    end
end

