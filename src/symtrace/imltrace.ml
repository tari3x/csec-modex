(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open List

open Utils
open Exp
open Execute 

;;
begin
  debugEnabled := true;
  inlineAll := false;
  
  (* server is typically the process executed first, i.e. P1 *)  
  let server = execute (open_in Sys.argv.(1)) in
  let client = execute (open_in Sys.argv.(2)) in

  clipEnabled := false;

  (*  
  (* iter (fun e -> print_endline (dump e)) !events *)
  (* if !debugEnabled then iter prerr_endline (map dump (filter interestingEvent events)); *)
  if !debugEnabled then iter (comp debugBracketTree dump) (filter interestingEvent events);
  if !debugEnabled then prerr_endline "";
  *)

  (* resetNames (); *)
  print_endline "let A = ";
  print_endline (showSimpleIML (procAndFilter client));
  print_endline "let B = ";
  print_endline (showSimpleIML (procAndFilter server));
    
  rawOut (open_out_bin Sys.argv.(3)) client server;
end;
