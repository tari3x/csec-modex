(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open Cil
open Common

open Str
open List

(*************************************************)
(** {1 Marking of Globals} *)
(*************************************************)

let config = ref ""
let markingDone = ref false

(** 
  The following lists should not be used by any instrumentation code. 
  They are only kept accessible for the purpose of config file analysis.
*)
let proxyNames = ref []
let typeNames = ref []
let blacklist = ref []
let boringNames = ref []


let readConfig : string -> unit = fun name ->
  if name <> "" then

  let curList : string list ref ref = ref proxyNames in
      
  let f = open_in name in

	let chooseList : string -> unit = fun s ->
	  curList := match s with
	    | "==== Functions" -> proxyNames
	    | "==== Types"     -> typeNames
	    | "==== Blacklist" -> blacklist
	    | "==== Boring"    -> boringNames
	    | ""               -> !curList
	    | _ -> fail ("readConfig: unexpected section in config file :" ^ s)
	in
  
	let rec read : unit -> unit = fun () ->
    let s = trim (input_line f) in
    if s = ""      then read () else
    if s.[0] = '/' then read () else
    if s.[0] = '=' then begin chooseList s; read () end 
    else
    begin
      !curList := s :: !(!curList);
      read ()
    end
  in
  
  try read () with End_of_file -> ()

(* take a look if the API already provides something *)
let typeName : typ -> string = function
  | TNamed (v, _) -> v.tname
  | TComp (v, _) -> v.cname
  | TEnum (v, _) -> v.ename
  | _ -> ""

let rec stripPtr : typ -> typ = function
  | TPtr (p, _) -> stripPtr p
  | a -> a

class markVisitorClass = object
  inherit nopCilVisitor
 
  method vvrbl : varinfo -> varinfo visitAction = function 
    | v when v.vglob ->
	    begin
	    match v.vtype with
	      | TFun (ret, args, _, _) ->
		      (* print_endline ("considering function " ^ name); *)
		
		      let funTypes = map stripPtr (ret :: (map snd3 (argsToList args))) in
		      let isProxy = string_match (regexp ".*_proxy$") v.vname 0 in
		
		      if (mem v.vname !proxyNames) ||
		         ((exists (flip mem !typeNames) (map typeName funTypes)) && not isProxy && not (mem v.vname !blacklist)) then
		        markNeedsProxy v;
	          
	      | _ -> ()
	    end;
	    
		  if needsProxy v || mem v.vname !boringNames then
		    markOpaque v;

      addRef v;

      addChild !currentGlobal v;
    	
	    SkipChildren
      
    | _ -> SkipChildren

  method vglob : global -> global list visitAction = function
    | GVar (v, _, loc) -> 
      addDef v loc; 
      DoChildren

    | GFun (f, loc) -> 
      (* addChild g f.svar; (* Add a self-reference. Why are we doing this? *) *)
      addDef f.svar loc; 
      DoChildren
   
    | _ -> DoChildren

end

let markGlobals : file -> unit = fun f ->
  if not !markingDone then
  begin
    markingDone := true;
    readConfig !config;
    visitCilFile (new markVisitorClass) f
  end

