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

let main () =
  (* server is typically the process executed first, i.e. P1 *)  
  let server = executeFile (open_in Sys.argv.(1)) in
  let client = executeFile (open_in Sys.argv.(2)) in

  (*
  Iml.Exp.clipEnabled := false;
  *)

  increase_debug_view();
  (*
  if debugEnabled () then prerr_endline "";
  if debugEnabled () then List.iter (fun s -> prerr_endline (Stmt.dump s)) client;
  if debugEnabled () then List.iter (fun s -> prerr_endline (Stmt.dump s)) server;
  *)
  if debugEnabled () then prerr_endline "";
  if debugEnabled () then prerr_endline (Iml.toString client);
  if debugEnabled () then prerr_endline (Iml.toString server);
  if debugEnabled () then prerr_endline "";
  decrease_debug_view();

  let client = client |> procAndFilter |> simplifyCasts in
  let server = server |> procAndFilter |> simplifyCasts in


  print_endline "let A = ";
  print_endline (Iml.toString client);
  print_endline "let B = ";
  print_endline (Iml.toString server);
    
  rawOut (open_out_bin Sys.argv.(3)) client server;
  
  dumpCalledFuns ();

;;
begin
  try main () with 
  Failure s -> begin 
    print_endline s;
    exit 1;
  end 
end
