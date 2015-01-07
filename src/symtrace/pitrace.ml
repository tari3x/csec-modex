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

let check_parsing_safety : unit -> unit = fun () ->
  
  let check : pi_fun_info -> unit = fun (p, _) -> 
    if not (List.mem_assoc p !safe_parsers) then
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

let show_pi_exp : exp -> string = fun e ->

  let rec show_exp_body : exp -> string = function 
    | Var (s, _) -> s
    | Sym (("const", _), [String s], _, _) -> s ^ "()"            
	  | Sym ((s, Prefix), es, len, id) ->
	    s ^ "(" ^ String.concat ", " (map show_exp es) ^ ")"
    | e -> "unexpected(" ^ dump e ^ ")"      

  and show_exp : exp -> string = function e ->
    let name = give_name e in
	  match e with
	    | Sym ((("read"), _), _, _, _) -> 
        "in(c, " ^ name ^ ");";

	    | Sym ((("new" | "new_t"), _), _, _, _) -> 
        "new " ^ name ^ ";";
	
	    | Sym (("write", _), [e], _, _) -> 
	      "out(c, " ^ show_exp e ^ ");"
	                                                         
        (* The thesis allows if statements now, previously this was let =true = ... in *)
	    | Sym ((("If_eq"), _), [e1; e2], _, _) ->
	      "if " ^ show_exp e1 ^ " = " ^ show_exp e2 ^ " then "
	
	    | Sym ((("If"), _), [e], _, _) ->
	      "if " ^ show_exp e ^ " = true then "
  
	    | Sym ((("event"), _), [e], _, _) ->
	      "event " ^ show_exp e ^ ";"

      | Sym ((("let"), _), [pat; rhs], _, _) ->
        "let " ^ show_exp pat ^ " = " ^ show_exp rhs ^ " in"
	
	    | _ -> show_exp_body e

  in
  show_exp e

let show_pi_process : exp list -> string = fun es ->
  let es, _ = split_by_type (es, empty_meta ()) in
  (* let es = elim_common_subs es in *)
  let result = String.concat "\n" (map show_pi_exp es) ^ " 0.\n" in
  result

let print_indent s = print_endline ("  " ^ s)

let write_pi : exp list -> exp list -> unit = fun client server ->
  
  let last_parser : string ref = ref "" in
  
  let print_concat : pi_fun_info -> unit = function
    | (name, Basic _) -> print_endline ""; print_endline ("data " ^ name ^ "/" ^ string_of_int (assoc name !arities) ^ ".")
    | _ -> ()
  in

  let show_parsing_rule : parsing_rule -> string = function ((parser_name, concat_name), e) -> 
    if is_valid_parse e then
    let numargs = assoc concat_name !arities in
    let result = match e with
      | Sym (("arg", _), [Int (i, _)], _, _) -> "x" ^ (Int64.to_string i)
      | e -> show_pi_exp e
    in
    let new_parser = (parser_name <> !last_parser) in
    let first_parser = (!last_parser = "") in
    last_parser := parser_name;
    let punctuation = if first_parser then "" else if new_parser then ".\n" else ";\n" in
    punctuation ^ (if new_parser then "reduc \n\  " else  "  ") ^
	    (parser_name ^ "(" ^ concat_name ^ "(" ^ 
	     String.concat ", " (map (fun i -> "x" ^ string_of_int i) (0 -- (numargs - 1))) ^ "))"
	     ^ " = " ^ result)
    else ""

  in

  let print_constant : string -> unit = fun s -> print_endline ("fun " ^ s ^ "/0.") in

  let client_proc = show_pi_process client in
  let server_proc = show_pi_process server in

  let reducs = if !parsing_rules = [] then "" else (String.concat "" (map show_parsing_rule !parsing_rules)) ^ "." in

  (* print_endline "free c."; *)

  iter print_endline !crypto;

  print_endline "\n(******************** \n  Constants \n********************)";

  iter print_constant !constants;
  
  print_endline "\n(******************** \n  Concatenation and Parsing \n********************)";

  iter print_concat !concats;
  
  print_endline "";
  
  print_endline reducs;

  print_endline "";
  iter print_endline !query;
  
  print_endline "";
                          
  print_endline "\n(*************************** \n  Model \n***************************)\n";
                                                                                                              
  print_endline "let A = ";
  print_endline client_proc;
  print_endline "let B = ";
  print_endline server_proc;
  
  iter print_endline !envp
  
  (*
  print_endline "process !";
  (* iter print_key !keys; *)
  print_indent "new key_aB;";
  print_indent "(!A | !B)"
  *)


(*************************************************)
(** {1 Main} *)
(*************************************************)

(* let show_simple_iML : exp list -> string = fun es -> reset_names (); show_simple_iML es *)

;;
begin
  inline_all := false;

  (*
  (* server is typically the process executed first, i.e. P1 *)
  let server = input_value (open_in_bin Sys.argv.(1)) in
  let client = input_value (open_in_bin Sys.argv.(2)) in
  *)
  let (client, server) = raw_in (open_in_bin Sys.argv.(1)) in

  verbose := true;
  debug_enabled := true;
  
  if !verbose then prerr_endline "raw IML:";
  if !verbose then prerr_endline (show_simple_iMLRaw client);
  if !verbose then prerr_endline (show_simple_iMLRaw server);

  let server = proc_and_filter server in
  let client = proc_and_filter client in

  if !verbose then prerr_endline "filtered IML:";
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);
  
  let (client, client_concats) = extract_concats client in
  let (server, server_concats) = extract_concats server in
  let all_concats = client_concats @ server_concats in

  if !verbose then show_funs all_concats;
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  insert_concats all_concats;

  if !verbose then show_funs !concats;

  try 
    let (name, _) = find (comp not (is_injective_concat false)) !concats in
    fail ("concat not injective: " ^ name)
  with Not_found -> ();

  let client = rewrite_concats client in
  let server = rewrite_concats server in

  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  let client = extract_const_concats client in
  let server = extract_const_concats server in

  if !verbose then prerr_endline "\n_iML after constant concats extraction:";
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  cleanup_concats (client @ server);

  if !verbose then prerr_endline "concats after tag rewriting:";
  if !verbose then show_funs !concats;

  let client = extract_parsers client in
  let server = extract_parsers server in

  if !verbose then show_funs !parsers;
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  compute_parsing_rules !parsers;

  compute_safe_parsers client;
  compute_safe_parsers server;

  read_template (open_in Sys.argv.(2));

  reset_meta ();

  let client = postprocess client in
  let server = postprocess server in

  cleanup_parsers (client @ server);
  
  check_parsing_safety ();

  if !verbose then prerr_endline "\npostprocessed IML:";
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  let client = extract_constants client in
  let server = extract_constants server in

  if !verbose then prerr_endline "\n_iML after constant extraction:";
  if !verbose then prerr_endline (show_simple_iML client);
  if !verbose then prerr_endline (show_simple_iML server);

  write_pi client server;
end;

(* 260 lines *)
