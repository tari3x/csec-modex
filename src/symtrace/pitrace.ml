(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open List

open Types
open Utils
open Solver
open Exp
open Execute

open Transform


(*************************************************)
(** {1 Parsing Safety} *)
(*************************************************)

let checkParsingSafety : unit -> unit = fun () ->
  
  let check : piFunInfo -> unit = fun (p, _) -> 
    if not (List.mem_assoc p !safeParsers) then
    fail ("an unsafe parser found: " ^ p)    
  in
  
  iter check !parsers  
  
(*************************************************)
(** {1 Soundness Proof} *)
(*************************************************)

let prove : unit -> unit = function _ -> failwith "prove: undefined"


(*************************************************)
(** {1 Pi Output} *)
(*************************************************)

let showPiExp : exp -> string = fun e ->

  let rec showExpBody : exp -> string = function 
    | Var (s, _) -> s
    | Sym (("const", _), [String s], _, _) -> s ^ "()"            
	  | Sym ((s, Prefix), es, len, id) ->
	    s ^ "(" ^ String.concat ", " (map showExp es) ^ ")"
    | e -> "unexpected(" ^ dump e ^ ")"      

  and showExp : exp -> string = function e ->
    let name = giveName e in
	  match e with
	    | Sym ((("read"), _), _, _, _) -> 
        "in(c, " ^ name ^ ");";

	    | Sym ((("new" | "newT"), _), _, _, _) -> 
        "new " ^ name ^ ";";
	
	    | Sym (("write", _), [e], _, _) -> 
	      "out(c, " ^ showExp e ^ ");"
	                                                         
        (* The thesis allows if statements now, previously this was let =true = ... in *)
	    | Sym ((("IfEq"), _), [e1; e2], _, _) ->
	      "if " ^ showExp e1 ^ " = " ^ showExp e2 ^ " then "
	
	    | Sym ((("If"), _), [e], _, _) ->
	      "if " ^ showExp e ^ " = true then "
  
	    | Sym ((("event"), _), [e], _, _) ->
	      "event " ^ showExp e ^ ";"

      | Sym ((("let"), _), [pat; rhs], _, _) ->
        "let " ^ showExp pat ^ " = " ^ showExp rhs ^ " in"
	
	    | _ -> showExpBody e

  in
  showExp e

let showPiProcess : exp list -> string = fun es ->
  let es, _ = splitByType (es, emptyMeta ()) in
  (* let es = elimCommonSubs es in *)
  let result = String.concat "\n" (map showPiExp es) ^ " 0.\n" in
  result

let print_indent s = print_endline ("  " ^ s)

let writePi : exp list -> exp list -> unit = fun client server ->
  
  let lastParser : string ref = ref "" in
  
  let printConcat : piFunInfo -> unit = function
    | (name, Basic _) -> print_endline ""; print_endline ("data " ^ name ^ "/" ^ string_of_int (assoc name !arities) ^ ".")
    | _ -> ()
  in

  let showParsingRule : parsingRule -> string = function ((parserName, concatName), e) -> 
    if isValidParse e then
    let numargs = assoc concatName !arities in
    let result = match e with
      | Sym (("arg", _), [Int (i, _)], _, _) -> "x" ^ (Int64.to_string i)
      | e -> showPiExp e
    in
    let newParser = (parserName <> !lastParser) in
    let firstParser = (!lastParser = "") in
    lastParser := parserName;
    let punctuation = if firstParser then "" else if newParser then ".\n" else ";\n" in
    punctuation ^ (if newParser then "reduc \n\  " else  "  ") ^
	    (parserName ^ "(" ^ concatName ^ "(" ^ 
	     String.concat ", " (map (fun i -> "x" ^ string_of_int i) (0 -- (numargs - 1))) ^ "))"
	     ^ " = " ^ result)
    else ""

  in

  let printConstant : string -> unit = fun s -> print_endline ("fun " ^ s ^ "/0.") in

  let clientProc = showPiProcess client in
  let serverProc = showPiProcess server in

  let reducs = if !parsingRules = [] then "" else (String.concat "" (map showParsingRule !parsingRules)) ^ "." in

  (* print_endline "free c."; *)

  iter print_endline !crypto;

  print_endline "\n(******************** \n  Constants \n********************)";

  iter printConstant !constants;
  
  print_endline "\n(******************** \n  Concatenation and Parsing \n********************)";

  iter printConcat !concats;
  
  print_endline "";
  
  print_endline reducs;

  print_endline "";
  iter print_endline !query;
  
  print_endline "";
                          
  print_endline "\n(*************************** \n  Model \n***************************)\n";
                                                                                                              
  print_endline "let A = ";
  print_endline clientProc;
  print_endline "let B = ";
  print_endline serverProc;
  
  iter print_endline !envp
  
  (*
  print_endline "process !";
  (* iter printKey !keys; *)
  print_indent "new keyAB;";
  print_indent "(!A | !B)"
  *)


(*************************************************)
(** {1 Main} *)
(*************************************************)

(* let showSimpleIML : exp list -> string = fun es -> resetNames (); showSimpleIML es *)

;;
begin
  inlineAll := false;

  (*
  (* server is typically the process executed first, i.e. P1 *)
  let server = input_value (open_in_bin Sys.argv.(1)) in
  let client = input_value (open_in_bin Sys.argv.(2)) in
  *)
  let (client, server) = rawIn (open_in_bin Sys.argv.(1)) in

  verbose := true;
  debugEnabled := true;
  
  if !verbose then prerr_endline "raw IML:";
  if !verbose then prerr_endline (showSimpleIMLRaw client);
  if !verbose then prerr_endline (showSimpleIMLRaw server);

  let server = procAndFilter server in
  let client = procAndFilter client in

  if !verbose then prerr_endline "filtered IML:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);
  
  let (client, clientConcats) = extractConcats client in
  let (server, serverConcats) = extractConcats server in
  let allConcats = clientConcats @ serverConcats in

  if !verbose then showFuns allConcats;
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  insertConcats allConcats;

  if !verbose then showFuns !concats;

  try 
    let (name, _) = find (comp not (isInjectiveConcat false)) !concats in
    fail ("concat not injective: " ^ name)
  with Not_found -> ();

  let client = rewriteConcats client in
  let server = rewriteConcats server in

  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let client = extractConstConcats client in
  let server = extractConstConcats server in

  if !verbose then prerr_endline "\nIML after constant concats extraction:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  cleanupConcats (client @ server);

  if !verbose then prerr_endline "concats after tag rewriting:";
  if !verbose then showFuns !concats;

  let client = extractParsers client in
  let server = extractParsers server in

  if !verbose then showFuns !parsers;
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  computeParsingRules !parsers;

  computeSafeParsers client;
  computeSafeParsers server;

  readTemplate (open_in Sys.argv.(2));

  resetMeta ();

  let client = postprocess client in
  let server = postprocess server in

  cleanupParsers (client @ server);
  
  checkParsingSafety ();

  if !verbose then prerr_endline "\npostprocessed IML:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let client = extractConstants client in
  let server = extractConstants server in

  if !verbose then prerr_endline "\nIML after constant extraction:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  writePi client server;
end;

(* 260 lines *)
