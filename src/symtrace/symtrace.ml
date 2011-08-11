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
  let events = execute (open_in Sys.argv.(1)) in
  print_endline "";
  (* iter (fun e -> print_endline (dump e)) !events *)
  clipEnabled := false;
  (* if !debugEnabled then iter prerr_endline (map dump (filter interestingEvent events)); *)
  if !debugEnabled then iter (comp debugBracketTree dump) (filter interestingEvent events);
  if !debugEnabled then prerr_endline "";
  (* resetNames (); *)
  print_endline (showIML (procAndFilter events));
end;
