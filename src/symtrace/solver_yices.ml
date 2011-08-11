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

let cache : pbool ExpMap.t ref = ref ExpMap.empty

(*************************************************)
(** {1 Functions} *)
(*************************************************)

;;
enable_type_checker true

(* it seems impossible to temporarily redirect stderr to stdout, not even using the Unix library *)
let debug_expr : expr -> unit = fun e -> if !debugEnabled then begin pp_expr e; flush stdout end

let debug_lbool : lbool -> unit = fun l -> 
  if !debugEnabled then match l with
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


(**
  This is needed to account for the fact that we are using mathematical integers instead of bitvectors.
*)
let normalise : exp -> exp = 
  
  let rec discard : exp -> exp = fun e_orig ->
   (* debug ("discard: e_orig = " ^ dump e_orig); *)
   match e_orig with
    | Range ((Int _) as i, Int (0L, _), Int (l, _)) when l >= 4L -> i
    | Range (e,            Int (0L, _), Int (l, _)) when l >= 4L -> 
      let e' = discard e in
      if isLength e' then e' else e_orig
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

  in match normalise e with
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
	      | _ -> mk_var_from_decl ctx (getDecl (giveName e ""))
	    end
	    
	    (* FIXME: think of when you should decline to translate *)
	    (* failwith ("tr: non-arithmetic expression encountered: " ^ dump e) *)
	  | _ -> mk_var_from_decl ctx (getDecl (giveName e "")) 


let isTrue : exp -> pbool = fun e ->
  let result = 
    try ExpMap.find e !cache 
	  with Not_found -> 
		  if tcBool e then
		  begin
			  push ctx;
		    let e' = tr (neg e) in
        (* debug_expr e'; debug ""; *)
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
  (* debug ("checking (yices) " ^ dump e ^ ", result (yices) = " ^ string_of_bool result); *)  
  cache := ExpMap.add e result !cache;
  result
    
let addFact : exp -> unit = fun e ->
  if tcBool e then
  begin
	  let y_e = tr e in
    (*
    debug ("asserting " ^ dump e);
    debug_expr y_e; debug ""; 
    *)
	  assert_simple ctx y_e;

    if inconsistent ctx = 1 then
    begin
      (* dump_context ctx; *)
      fail ("addFact: the context has become inconsistent: " ^ dump e)
    end
  end
    
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

