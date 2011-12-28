(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open Types
open Utils

module L = List
open List
open Array
open Yices

(*************************************************)
(** {1 State} *)
(*************************************************)

let ctx : context = mk_context ()

let cache : pbool IntMap.t ref = ref IntMap.empty

let solver_debug : bool ref = ref false

(*************************************************)
(** {1 Naming} *)
(*************************************************)

(*
  The naming should be separate from the naming used by output routines,
  we want the names to persist continuously, no reset.
  
  At the same time this ending may, if necessary, be made to respect
  output names when they are available.
*)

let mkExpName : id -> string = fun id -> "var" ^ (string_of_int id)

(*************************************************)
(** {1 Functions} *)
(*************************************************)

;;
enable_type_checker true

(* it seems impossible to temporarily redirect stderr to stdout, not even using the Unix library *)
let debug_expr : string -> expr -> unit = fun s e -> 
  if !solver_debug then begin prerr_string s; flush stderr; pp_expr e; print_endline "" end

let debug = fun s -> if !solver_debug then debug s

let debug_lbool : lbool -> unit = fun l -> 
  if !solver_debug then match l with
    | False -> prerr_endline "False"
    | True  -> prerr_endline "True"
    | Undef -> prerr_endline "Undef"

let b2b = ["!"; "&&"; "LOR"]
let n2b = ["=="; "!="; ">"; "<"; "<="; ">="]
let n2n = ["-"; "+"; "*"]

let rec tcBool : exp -> bool = function
  | Sym ((s, _), es, _, _) when L.mem s b2b -> for_all tcBool es
  | Sym ((s, _), es, _, _) when L.mem s n2b -> for_all tcNum es
  | _ -> false

and tcNum : exp -> bool = function
  | Sym ((s, _), es, _, _) when L.mem s n2n -> for_all tcNum es
  | Sym ((s, _), _, _, _)  when L.mem s b2b || L.mem s n2b -> false
  | _  -> true


let addRawFact: expr -> unit = fun y_e ->
  (* debug_expr "asserting_y " y_e; *) 
  assert_simple ctx y_e;
    
  if inconsistent ctx = 1 then
  begin
    (* dump_context ctx; *)
    debug_expr "addFact: the context has become inconsistent: " y_e;
    fail "" (* dump e *)
  end


(**
  This is needed to account for the fact that we are using mathematical integers instead of bitvectors.
*)
let normalise : exp -> exp = 
  
  let rec discard : exp -> exp = fun e_orig ->
   (* debug ("discard: e_orig = " ^ dump e_orig); *)
   match e_orig with
      (* 
        What we really want to say in the following 2 cases is that when a value
        fits in its length, the length is not relevant.
        
        Need to separate proving formulas for bitstrings from proving formulas for values.
      *)         
    | Range ((Int _) as i, Int (0L, _), Int (l, _), _) when l >= 4L -> i
    | Range (e,            Int (0L, _), Int (l, _), _) when l >= 4L -> 
      let e' = discard e in
      if isLength e' then e' else e_orig
      
      (* FIXME: same issue here, discarding length *)
    | Sym (("len", _), [Sym (_, _, Unknown, _) as e'], _, tag) -> Sym (("len", Prefix), [e'], Unknown, tag)
    | Sym (("len", _), [Sym (_, _, l, _)], _, _) -> discard l (* setLen (getLen e) l *)
    | Sym (("len", _), _, _, _) -> fail ("normalise: unexpected len expression: " ^ dump e_orig) (* setLen (getLen e) l *)
    | Sym (("replicate", _), [Int (0L, _)], l, _) -> Int (0L, l)
      (* this should only be used for lengths, but for now we apply it everywhere *)
    | Sym (("castToInt", _), [e; _], _, _) -> discard e
    | Sym (s, es, _, det) -> Sym (s, es, Unknown, det)
    | e -> e
  in

  (* can't use post here, because first length of a sym gets discarded, then we try to apply len *)
  visitExpPre discard

let rec tr : exp -> expr = fun e ->
  
	let getDecl : string -> var_decl = fun name ->
	  try get_var_decl_from_name ctx name 
	  with Failure _ -> mk_var_decl ctx name (mk_type ctx nat_type_name)
  in

  let mkVar: exp -> expr = fun e ->
    let tagId = expId e in
    let structId = idByStructure (Some tagId) e in
    let tagVar = mk_var_from_decl ctx (getDecl (mkExpName tagId)) in
    let structVar = mk_var_from_decl ctx (getDecl (mkExpName structId)) in 
    if tagId <> structId then
      addRawFact (mk_eq ctx tagVar structVar);
    tagVar
  in

  match normalise e with
	  | Int (i, _) -> mk_num ctx (Int64.to_int i)
	  | Sym ((sym, _), es, _, id) ->
	    begin
	    match (sym, es) with
	      | ("-", [a]) -> mk_sub ctx [| mk_num ctx 0; tr a |] 
	      | ("-", _)   -> mk_sub ctx (map tr (of_list es))
	      | ("!", [a]) -> mk_not ctx (tr a)
	      | ("+", _)   -> mk_sum ctx (map tr (of_list es))
	      | ("*", _)   -> mk_mul ctx (map tr (of_list es))
	      | ("&&", _)  -> mk_and ctx (map tr (of_list es))
	      | ("LOR", _) -> mk_or  ctx (map tr (of_list es))
	      | ("==", [a; b]) -> mk_eq ctx (tr a) (tr b)
	      | ("!=", [a; b]) -> mk_diseq ctx (tr a) (tr b)
	      | (">",  [a; b]) -> mk_gt ctx (tr a) (tr b)
	      | (">=",  [a; b])-> mk_ge ctx (tr a) (tr b)
	      | ("<",  [a; b]) -> mk_lt ctx (tr a) (tr b)
	      | ("<=",  [a; b])-> mk_le ctx (tr a) (tr b)
	      | (s, _) when List.mem s ["!"; "=="; "!="; ">"; ">="; "<"; ">="] -> failwith ("tr: " ^ s ^ " expects two arguments")
	      | _ -> mkVar e (* FIXME: shold we use the normalised version? *)
	    end
	    
	    (* FIXME: think of when you should decline to translate *)
	    (* failwith ("tr: non-arithmetic expression encountered: " ^ dump e) *)
	  | _ -> mkVar e 


let isTrue : exp -> pbool = fun e ->
  let id = expId e in
  let result = 
    try IntMap.find id !cache 
	  with Not_found -> 
		  if tcBool e then
		  begin
			  push ctx;
		    let e' = tr (neg e) in
        (* debug_expr "checking " e'; *)
			  assert_simple ctx e';
			  let sat = check ctx in
        pop ctx;
			  match sat with
				  | False -> true
				  | Undef -> false
				  | True  -> false
		  end
		  else false
  in
  debug ("checking (yices) " ^ dump e ^ ", result (yices) = " ^ string_of_bool result);    
  cache := IntMap.add id result !cache;
  result
    
let addFact : exp -> unit = fun e ->
  if tcBool e then
  begin
    debug ("asserting " ^ dump e);
    addRawFact (tr e)
  end
    
let resetFacts : unit -> unit = fun () -> 
  reset ctx;
  cache := IntMap.empty

let equal : exp -> exp -> pbool = fun a b -> 
  if isSpecialLen a b then 
    fail "equal: trying to apply to special length values (Unknown or Infty)";
  isTrue (eq [a; b])

let notEqual : exp -> exp -> pbool = fun a b -> 
  if isSpecialLen a b then 
    fail "notEqual: trying to apply to special length values (Unknown or Infty)";
  isTrue (neg (eq [a; b]))

let greaterEqual : exp -> exp -> pbool = fun a b -> 
  if isSpecialLen a b then 
    fail "greaterEqual: trying to apply to special length values (Unknown or Infty)";
  isTrue (grEq a b)

let equalLen : len -> len -> pbool = fun a b ->
  if isSpecialLen a b then false
  else isTrue (eq [a; b])

let greaterEqualLen : len -> len -> pbool = fun a b ->
  if isSpecialLen a b then false
  else greaterEqual a b
  (* match (a, b) with
    | (All, _) -> true
    | (_, All) -> false
    | (Unknown, _) | (_, Unknown) -> false
    | (x, y) -> greaterEqual x y *)

let greaterEqualLenAnswer : len -> len -> answer = fun a b ->
  if greaterEqualLen a b then
    Yes
  else if greaterEqualLen b a then
    No
  else
    Maybe

