(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Sym.Op.T
open Iml.Exp.T
open Iml.Pat.T
open Iml.Stmt.T

open Transform_imltrace

module E = struct 
  include Iml.Exp
  include Iml.Exp.T
end
module S = Solver

open Printf

(*************************************************)
(** {1 Types} *)
(*************************************************)

(**
  We represent a lambda expression with n arguments by an expression containing variables
  (mk_arg 0) to (mk_arg (n - 1)).
*)
type sym_def = exp

type sym_defs = sym_def Sym.Map.t

(**
  [parser(concat) = result]
*)
type parsing_eq = (sym * sym) * exp

type fact = Solver.fact

(*************************************************)
(** {1 Formal Arguments} *)
(*************************************************)

let mk_arg id = ("arg" ^ string_of_int id)

(** 
  [lenarg(id) = len(arg(id))]
*)
let mk_arg_len len id = 
  let l = Len (Var (mk_arg id)) in
  (* FIXME: remove this *)
  S.add_fact (S.ge l E.zero);
  l

let mk_formal_args n = List.map mk_arg (0 -- (n - 1))

(*************************************************)
(** {1 Debug Output} *)
(*************************************************)

let show_fun sym def =
  (* This is called for boolean conditions as well. *)
  (* E.typecheck Bitstring def; *)
  Sym.to_string sym ^ " := " ^ (E.to_string def)
  (* | (s, Rewrite e) -> Sym.to_string s ^ "/" ^ string_of_int (List.assoc s !arities) ^ " ~> " ^ (E.to_string e) *)

let show_funs : sym_defs -> unit = fun cs ->
  prerr_endline "";
  Sym.Map.iter (fun s info -> prerr_endline (show_fun s info)) cs;
  prerr_endline ""


(*************************************************)
(** {1 Helpers} *)
(*************************************************)

(* TODO: make these local *)
let concat_id : int ref = ref 0
let parser_id : int ref = ref 0

let new_concat_sym ~arity =
  Fun ("conc" ^ string_of_int (increment concat_id), arity)  

let new_parser_sym () = 
  Fun ("parse" ^ string_of_int (increment parser_id), 1)  


let find_definition f defs: sym_def =
  match Sym.Map.maybe_find f defs with
    | Some def -> def
    | _ -> fail "Could not find definition for %s" (Sym.to_string f)

let show_parsing_eq ?fun_types concats (((p, c), e): parsing_eq) =
  let arity = Sym.arity c in
  let args = mk_formal_args arity in
  let header = match fun_types with
    | Some fun_types ->
      let ts, _ = Sym.Map.find c fun_types in
      List.map2 (fun arg t -> arg ^ ": " ^ Type.to_string t) args ts 
      |> String.concat ", "
      |> sprintf "forall %s;\n" 
    | None -> ""
  in  
  sprintf "%s%s(%s(%s)) = %s" header (Sym.to_string p) (Sym.to_string c) (String.concat ", " args) (E.to_string e)

(*
let value_unsigned e = 
  match S.eval (E.Len e) with
  | None   -> fail "cannot determine width of %s" (E.to_string e)
  | Some w -> E.Val (e, (Int_type.Unsigned, w))
*)

(*************************************************)
(** {1 Typing} *)
(*************************************************)


module Typing: sig

  type type_ctx = Type.t Var.Map.t
  type fun_type_ctx = Fun_type.t Sym.Map.t

  val infer_exp: fun_type_ctx -> Type.t -> exp -> type_ctx
  val infer: fun_type_ctx -> iml -> type_ctx
  
  val derive_unknown_types: fun_type_ctx -> type_ctx -> iml -> fun_type_ctx
  
  val check: sym_defs -> fun_type_ctx -> type_ctx -> fact list -> iml -> iml
  
  val merge: type_ctx list -> type_ctx 
  
  val merge_fun_types: fun_type_ctx list -> fun_type_ctx
  
  val dump_types: type_ctx -> unit
  val dump_fun_types: fun_type_ctx -> unit
  
  val cast: Type.t -> Type.t -> exp -> exp
  val casts: iml -> (Type.t * Type.t) list

  (**
    Check robust safety of concats, as defined in the paper.
  *)
  val check_robust_safety: sym_defs -> fun_type_ctx -> unit
  
  (**
    Check that all functions for which we don't have a definition have a type.
  *)
  val check_missing_types: sym_defs -> template_types:fun_type_ctx -> inferred_types:fun_type_ctx -> iml -> unit
  
end = struct

  type type_ctx = Type.t Var.Map.t
  type fun_type_ctx = Fun_type.t Sym.Map.t
  
  let merge (ctxs: type_ctx list): type_ctx = 
    let merge_types _ t1 t2 = 
      match t1, t2 with
        | Some t, None | None, Some t -> Some t
        | Some t1, Some t2 -> Some (Type.intersection t1 t2)
        | None, None -> None
    in
    List.fold_left (Var.Map.merge merge_types) Var.Map.empty ctxs

  let merge_fun_types (ctxs: fun_type_ctx list): fun_type_ctx = 
    let merge_types f t1 t2 = 
      match t1, t2 with
        | Some t, None | None, Some t -> Some t
        | Some t1, Some t2 -> 
          fail "colliding types: %s and %s" (Sym.cv_declaration f t1) (Sym.cv_declaration f t2) 
        | None, None -> None
    in
    List.fold_left (Sym.Map.merge merge_types) Sym.Map.empty ctxs

  let dump_types ctx = 
    Var.Map.iter (fun v t -> prerr_endline (sprintf "%s:  %s" v (Type.to_string t))) ctx;
    prerr_endline ""

  let dump_fun_types : fun_type_ctx -> unit = fun fun_types ->
    Sym.Map.iter (fun f t -> prerr_endline (Sym.cv_declaration f t)) fun_types;
    prerr_endline ""  

  let exp_type fun_types var_types = function
    | Var v when Var.Map.mem v var_types -> Var.Map.find v var_types
    | Annotation(Type_hint t, _) -> t
    | Sym(f, es) when Sym.Map.mem f fun_types -> 
      let(_, t) = Sym.Map.find f fun_types in t
    | _ -> Bitstring
  
  let cast t t' e =
    if t = t' then e else
    Sym (Cast (t, t'), [e])
  
  let rec casts p = 
  
    let rec casts_e e =
      let cs = List.concat_map ~f:casts_e (E.children e) in
      match e with
      | Sym (Cast (t, t'), _) ->
        (t, t') :: cs 
      | _ -> cs
    in
    
    match p with
      | s :: p -> List.concat_map ~f:casts_e (Stmt.children s) @ casts p
      | [] -> []


  let rec infer_exp (fun_types: fun_type_ctx) t = function 
    | Var v -> Var.Map.singleton v t
    
    | Annotation(Type_hint t, e) -> infer_exp fun_types t e
              
    | Sym(f, es) when not (Sym.Map.mem f fun_types) -> merge (List.map (infer_exp fun_types Bitstring) es) 
  
    | Sym(f, es) ->
      let (ts, _) = Sym.Map.find f fun_types in
      merge (List.map2 (infer_exp fun_types) ts es) 
      
    | Annotation(_, e) -> (infer_exp fun_types) t e
    
    | e -> fail "infer_exp_types: unexpected expression %s" (E.dump e)

            
  let infer (fun_types: fun_type_ctx) (p: iml): type_ctx = 
  
    let exp_type fun_types e = exp_type fun_types Var.Map.empty e in
    let infer_exp = infer_exp fun_types in
   
    let rec infer = function
      | Let (VPat v, e) :: p ->  
        let t = exp_type fun_types e in
        let ctx_e = infer_exp t e in
        let ctx_p = infer p in
        let ctx_v = Var.Map.singleton v t in
        merge [ctx_e; ctx_p; ctx_v]
        
      | Let ((FPat _ | Underscore), _) :: _ -> fail "infer_types: let patterns not supported: %s" (Iml.to_string p)
        
      | New (v, t) :: p -> 
        let ctx_p = infer p in
        let ctx_v = Var.Map.singleton v t in
        merge [ctx_p; ctx_v]
    
      | In vs :: p -> 
        let ctx_p = infer p in
        let ctx_v = Var.Map.of_list (List.map (fun vs -> vs, Bitstring) vs) in
        merge [ctx_p; ctx_v]
      
      | Aux_test _ :: p -> infer p

      | Test e :: p -> 
        let ctx_e = infer_exp Bool e in
        let ctx_p = infer p in
        merge [ctx_e; ctx_p]
                        
      | Test_eq (e1, e2) :: p -> 
        let ctx1 = infer_exp Bitstring e1 in
        let ctx2 = infer_exp Bitstring e2 in
        let ctx_p = infer p in
        merge [ctx1; ctx2; ctx_p]
        
      | Assume e :: p ->
        infer p
      
      | Event (ev, es) :: p ->
        (* Events symbols of type bool in CV *) 
        let ctx_e = infer_exp Bool (Sym (Fun (ev, List.length es), es)) in
        let ctx_p = infer p in
        merge [ctx_e; ctx_p]
      
      | (Comment _ | Out _ | Yield) as s :: p -> 
        let ctx_s = List.map (infer_exp Bitstring) (Stmt.children s) in
        let ctx_p = infer p in
        merge (ctx_p :: ctx_s)
        
      | [] -> Var.Map.empty
    in
    
    infer p
    
  (**
    Returns only the context for formatter functions. Merge with user functions yourself.
  
    Assumes that the process is in the formatting-normal form, that is,
    every formatter application has the form let [x = f(x1, ..., xn)]. 
    
    We replace all argument types of auxiliary tests by bitstring. Consider
    
      in(c_in, (msg4: bitstring, cipher2: bitstring));
      if auxiliary11(cipher2, msg4) then 
      let msg6 = D(cast_bitstring_bounded_1077_ciphertext(cipher2), key2) in ...
    
    We cannot require that cipher2 is bounded_1077_ciphertext when auxiliary11 is invoked,
    because belonging to the type is what auxiliary11 checks in the first place.
  *)
  let derive_unknown_types fun_types (ctx: type_ctx) (p: iml): fun_type_ctx = 
  
    let rec derive s = 
      match s with
      | Let (VPat v, Sym (f, vs)) when not (Sym.Map.mem f fun_types) ->
        let ts = 
          List.map (function | Var v -> Var.Map.find v ctx 
                             | _ -> fail "formatting-normal form expected: %s" (Stmt.to_string s))
          vs
        in                   
        Some (f, (ts, Var.Map.find v ctx))
        
      | Test (Sym (f, vs)) when not (Sym.Map.mem f fun_types) -> 
        let ts = 
          List.map (function | Var v -> Bitstring 
                             | _ -> fail "malformed test statement: %s" (Stmt.to_string s))
          vs
        in
        Some (f, (ts, Bool))
        
      | _ -> None 
        
    in Sym.Map.of_list (List.filter_map ~f:derive p)
        
  let prove_type facts ((arg_types, res_type): Fun_type.t) (f: sym) (f_def: exp) (args: exp list): bool =
  
    if List.length args <> List.length arg_types then
      fail "wrong number of arguments: %s(%s)" (Sym.to_string f) (E.dump_list args);

    let formal_args = mk_formal_args (List.length args) in
    let e_f = E.subst formal_args args f_def in

    (*
    debug ("typecheck: e_def = " ^ E.dump e_def);
    debug ("typecheck: context = " ^ dump_list ctx);
    *)

    let arg_facts = List.map2 S.in_type args arg_types in
    let res_fact = S.in_type e_f res_type in
    
    debug "proving type %s" (Sym.cv_declaration f (arg_types, res_type));
    S.implies (arg_facts @ facts) [res_fact]


  let erase_type_annotations p = 
    let rec erase = function
      | Annotation (Type_hint _, e) -> erase e
      | e -> E.descend erase e
    in
    Iml.map erase p


  let check (defs: sym_defs) (fun_types: fun_type_ctx) (ctx: type_ctx) (facts: fact list) (p: iml): iml = 

    let typefacts ctx = 
      Var.Map.bindings ctx 
      |> List.map ~f:(fun (v, t ) -> S.in_type (Var v) t)
    in

    let rec check_exp ctx facts t' e: exp = 
    match e with
      | Var v -> 
        let t = Var.Map.find v ctx in
        if not (S.implies (facts @ typefacts ctx) [S.in_type (Var v) t']) then
          fail  "cannot prove type: %s: %s" v (Type.to_string t');
        cast t t' e
    
      | Sym (f, es) -> 
        let (ts, t) = Sym.Map.find f fun_types in
        let es' = List.map2 (check_exp ctx facts) ts es in
        let tt = Type.intersection t t' in
        begin match Sym.Map.maybe_find f defs with
          | Some def -> 
            if not (prove_type (facts @ typefacts ctx) (ts, tt) f def es) then
              fail "typecheck: cannot prove type %s" (Sym.cv_declaration f (ts, tt))
          | None -> 
            if not (Type.subtype t t') then
              fail "typecheck: cannot prove type %s" (Sym.cv_declaration f (ts, t'))
        end;
        cast t t' (Sym (f, es'))
        
        (* Type annotations are only used in inference, and ignored in typechecking *)
      | Annotation (a, e) -> Annotation (a, check_exp ctx facts t' e) 
        
      | e -> fail "check_exp: unexpected expression %s" (E.dump e)
    in
  
    let rec check ctx facts p =
    match p with
      | Let (VPat v, e) :: p ->
        let t = exp_type fun_types ctx e in
        let e' = check_exp ctx facts t e in
        let p' = check (Var.Map.add v t ctx) facts p in
        Let (VPat v, e') :: p' 
        
      | Let (_, _) :: _ -> fail "check_types: let patterns not supported: %s" (Iml.to_string p)
        
      | Aux_test e :: p ->
        let p' = check ctx (facts @ [e]) p in
        Aux_test e :: p'
        
      | Test e :: p ->
        let e = check_exp ctx facts Bool e in
        let p = check ctx facts p in
        Test e :: p
        
      | Test_eq (e1, e2) :: p ->
        let t1 = exp_type fun_types ctx e1 in
        let t2 = exp_type fun_types ctx e2 in
        let tt = Type.union t1 t2 in
        (* Not adding a non-auxiliary test to facts *)
        let p' = check ctx facts p in
        Test_eq(cast t1 tt e1, cast t2 tt e2) :: p'
        
      | Assume e :: p ->
        Assume e :: check ctx (facts @ [e]) p
    
      | In vs :: p -> 
        let ctx_v = Var.Map.of_list (List.map (fun vs -> vs, Bitstring) vs) in
        let p' = check (merge [ctx; ctx_v]) facts p in
        In vs :: p'
        
      | New (v, t) :: p ->
        begin match Type.strip_name t with
        | Fixed _ ->  
          let p' = check  (Var.Map.add v t ctx) facts p in
          New (v, t) :: p' 
        | _ -> fail "fixed type expected in new expression: %s" (Stmt.to_string (New (v, t)))
        end
            
      | Out es :: p ->
        let es' = List.map (fun e -> check_exp ctx facts (exp_type fun_types ctx e) e) es in
        let p' = check ctx facts p in
        Out es' :: p'
    
      | Event (ev, es) :: p ->
        let (ts, t) = Sym.Map.find (Fun (ev, List.length es)) fun_types in 
        let es' = List.map2 (fun e t -> check_exp ctx facts t e) es ts in
        let p' = check ctx facts p in
        Event (ev, es') :: p'
        
      | Yield :: p -> Yield :: check ctx facts p
        
      | Comment s :: p -> Comment s :: check ctx facts p
        
      | [] -> []
    in
  
    check ctx facts (erase_type_annotations p)
    
    
  let check_robust_safety (concats: sym_defs) (fun_types: fun_type_ctx) = 
  
    let safe f def = 
      let (ts, t) = Sym.Map.find f fun_types in
      let args = mk_formal_args (Sym.arity f) |> List.map ~f:E.var in
      if not (prove_type [] (ts, t) f def args && t <> Bitstringbot) then
        fail "function %s is not robustly safe" (Sym.cv_declaration f (ts, t));
    in
    
    Sym.Map.iter safe concats

  let check_missing_types defs ~template_types ~inferred_types p = 
    let rec check = function
      | Sym (f, es) ->
        if not (Sym.Map.mem f defs) && not (Sym.Map.mem f template_types) then
          begin match Sym.Map.maybe_find f inferred_types with
            | Some t -> fail "No type found for function %s, suggested type: %s" (Sym.to_string f) (Sym.cv_declaration f t);
            | None -> fail "No type found for function %s" (Sym.to_string f);
          end;
        List.iter check es
      | e -> List.iter check (E.children e)
    in
    Iml.iter check (remove_auxiliary p)

end


(*************************************************)
(** {1 Facts} *)
(*************************************************)

(* TODO: this will be merged with solver facts *)
module CVFact = struct
  type t = Forall of (var * Type.t) list * exp
  
  let make fun_types (e: exp): t =
    let ts = Typing.infer_exp fun_types Bool e in
    Forall (Var.Map.bindings ts, e)

  let to_string (Forall (args, e)) =
    let show_var (v, t) = v ^ ": " ^ Type.to_string t in
    "forall " ^ String.concat ", " (List.map show_var args) ^ ";\n\t" ^ E.to_string e ^ "."
         
end

(*************************************************)
(** {1 Crypto rewriting} *)
(*************************************************)

let rewrite e = 
  
  let rec rewrite : exp -> exp = function
    | Sym (Fun ("HMAC", 3), [String hash; msg; key]) -> Sym (Fun ("HMAC_" ^ hash, 2), [msg; key])
    | Sym (Fun ("SHA256", 1), [e]) ->
      (* we cannot use a CV rewrite rule cause the key needs to be freshly generated *)
      let sha256key = Var "SHA256_key" in 
      Sym (Fun ("SHA_hash", 2), [sha256key; e]) 
    (*
    | Sym (("If_eq", _), [Sym (("DSA_verify", _), es, l, tag); e_one], l', tag') when S.equal_len e_one one -> 
      Sym (("If", Prefix), [Sym (("DSA_check", Prefix), es, l, tag)], l', tag')
    *)
    | e -> E.descend rewrite e
  in

  let e = rewrite e in 
  e

let rewrite_crypto p =
  List.map (Stmt.descend rewrite) p


(*************************************************)
(** {1 Let simplification} *)
(*************************************************)

let simplify_lets p =
 
  (* Remove width annotations in lets as those are not useful *)
  let cleanup = function
    (* | Let (VPat v, Annotation (Width _, e)) -> Let (VPat v, e) *)
    | s -> s
  in

  let rec simplify = function
    | Let (VPat v, Var v') :: p -> simplify (Iml.subst [v] [Var v'] p) 
    | Let (VPat v, e) :: p when Iml.refcount v p = 0 -> simplify p
    | s :: p -> s :: simplify p
    | [] -> []
  in
  
  List.map cleanup p |> simplify

let simplify_double_lets p = 

  let rec simplify defs = function
    | Let (VPat v, Var v') :: p -> Let (VPat v, Var v') :: simplify defs p  
    | Let (VPat v, e) :: p -> 
      begin try
        let v'= List.assoc e defs in
        Let (VPat v, Var v') :: simplify defs p
      with Not_found ->
        Let (VPat v, e) :: simplify ((e, v) :: defs) p
      end
    | s :: p -> s :: simplify defs p
    | [] -> []
  in
  
  simplify [] p


(*************************************************)
(** {1 Name annotations} *)
(*************************************************)

(**
  Changes things like
    new var1: fixed_n;
    let var2 = var1 in
    let named_var = var2 in P
  (where there is a name annotation on var2) to 
    new named_var: fixed_n in P
  while checking that var1 does not occur in P.

  No renaming is done to free variables of course.
  
  Name annotations get removed in the end.
*)
  
let apply_name_annotations p = 

  let free_vars = Iml.free_vars p in

  (* 
    Which variable should be renamed to which? No loops.
  *)
  let names = ref Var.Map.empty in
  
  let rec resolve name =
    match Var.Map.maybe_find name !names with
      | Some name' -> resolve name'
      | None -> name 
  in 

  (* Rename v1 and all members of its equivalence class to v2. *)
  let rec rename v1 v2 =
    match Var.Map.maybe_find v1 !names with
      | None ->
        (* We are at the top of the chain, add a new element above it *)
        if v1 <> v2 then
          names := Var.Map.add v1 v2 !names
      | Some v1' ->
        if v1 = v2 then
          (* v1 will become the new top, so we remove its own renaming *)
          names := Var.Map.remove v1 !names;
        rename v1' v2
  in

  let rec exp_name = function
    | Var v -> Some v
    | Annotation (Name name, e) -> Some name
    | Annotation (_, e) -> exp_name e
    | e -> None
  in 

  let rec collect_names_e = function
    | Annotation (Name name, e) ->
      begin match exp_name e with
          (* Do not rename free variables *)
        | Some name' when not (List.mem name' free_vars) -> 
          rename name' name
        | _ -> ()
      end;
      collect_names_e e
    | e -> List.iter collect_names_e (E.children e)
  in
      
  let collect_names = function
    | Let (VPat v, e) ->
      begin match exp_name e with
        | Some name -> rename v name 
        | _ -> ()
      end
    | s -> ()
  in
  
  (* We do substitution without regard for capture *)
  let subst_v vs vs' = Iml.map (E.subst_v vs vs') in
  
  (* Rename variables according to collected names *)
  let rec rename_vars = function
    | Let (VPat v, e) :: p ->
      let v' = resolve v in
      Let (VPat v', e) :: rename_vars (subst_v [v] [v'] p)
    | New (v, t) :: p ->
      let v' = resolve v in
      New (v', t) :: rename_vars (subst_v [v] [v'] p)
    | In vs :: p ->
      let vs' = List.map resolve vs in
      In vs' :: rename_vars (subst_v vs vs' p) 
    | s :: p -> s :: rename_vars p
    | [] -> []
  in

  let rec remove_name_annotations = function
    | Annotation (Name _, e) -> remove_name_annotations e
    | e -> E.descend remove_name_annotations e
  in 

  List.iter collect_names p;
  (* It is important that this comes second, 
     to make sure annotation renamings override 
     assignment renamings *)
  Iml.iter collect_names_e p;
  rename_vars p |> Iml.map remove_name_annotations |> simplify_lets
         
(*************************************************)
(** {1 Normal Form} *)
(*************************************************)

let is_tag: exp -> bool = fun e -> E.is_concrete e 

let sort_defs defs =

  let gt s s' =
    match s, s' with
      | Let (_, e), Let (VPat v, _) -> List.mem v (E.vars e)
      | _ -> false
  in
  List.topsort gt defs


let normal_form p = 

  let rec normalize p = 
  
    let defs = ref [] in
  
    let mk_var = function
      | Var v -> Var v
      | e ->  
        let v = Var.fresh "" in
        defs := Let (VPat v, e) :: !defs;
        Var v 
    in
    
    (* remove expressions that are themselves lengths of an expression that follows *) 
    let rec remove_lens = function
      | BS (e, _) :: es ->
        if List.exists (fun e' -> S.equal_int e (Len e')) es
        then remove_lens es
        else e :: remove_lens es
      | e :: es -> e :: remove_lens es
      | [] -> []
    in
  
    (*
      This is the heuristic part - we convert an expression like 
      20 | 20 | x | y, 
      where len(x) = 20 and len(y) = 20 to
      len(x) | len(y) | x | y
      
      args is the list of arguments that we haven't found a length for yet. 
    *)
    let rec explicate_lens args = function 
      | [] -> []
      | e :: es ->
        match S.eval (Len e) with
        | None -> e :: explicate_lens args es
        | Some width ->
          let itype = Int_type.create `Unsigned width in
          match Option2.try_with (fun () -> E.typecheck (Bs_int itype) e) with
          | None -> e :: explicate_lens args es
          | Some () ->
            let e_val = Val (e, itype) in
            match List.find_and_remove (fun e' -> S.equal_int e_val (Len e')) args with
            | None -> e :: explicate_lens args es
            | Some (e', args) -> 
              BS (Len e', itype) :: explicate_lens args es
    in
  
    let rec extract_non_cryptographic e = 
      match e with 
      | e when not (is_cryptographic e) -> E.descend extract_non_cryptographic e
      | e -> mk_var (extract e)

    (* Variables for same expressions will later be unified by simplify_lets *)
    and extract_concat = function
      | e when is_tag e -> e
      | BS (Len e, itype) -> BS (Len (mk_var (extract e)), itype)
      | e -> mk_var (extract e) 
      
    and extract_parser v m e =
      match e with
      | e when Type.subtype (E.type_of e) Bitstring && S.equal_bitstring m e -> v
      | e when Type.subtype (E.type_of e) Type.Int && S.equal_int (Len m) e -> Len v
      | Sym (s, es) when Sym.is_arithmetic s -> 
        E.descend (extract_parser v m) e
      | Sym (Op (Cast_to_int, _), _) 
      | Val _
      | BS _
      | Range _ 
      | Int _ -> E.descend (extract_parser v m) e
      | e -> fail "normal_form: unexpected parser subexpression %s" (E.dump e) (* mk_var (extract e) *)
      
    and extract e = 
      match e with
      | Concat es ->
        let args = remove_lens (List.filter (non is_tag) es) in
        let es = explicate_lens args es in
        debug "extract concat: args = %s" (E.list_to_string args);
        debug "extract concat: es = %s" (E.list_to_string es);
        Concat (List.map extract_concat es)
        
      | Range (Range _, _, _) ->
        fail "extract_parsers: nested ranges not supported: %s" (E.dump e)
        
      | Range (m, pos, len) ->
        let v = mk_var (extract m) in
        extract_parser v m e

      | Var v -> Var v
        
      | Sym (Fun _, _) -> E.descend extract e

      | Annotation (a, e) -> Annotation (a, mk_var (extract e))

      | e when not (is_cryptographic e) -> extract_non_cryptographic e
                        
      | _ -> assert false
    in 
    
    match p with
      | Aux_test e :: p ->
        S.add_fact e; 
        Aux_test e :: normalize p
        
      | Assume e :: p ->
        S.add_fact e;
        Assume e :: normalize p
        
      | Let (VPat v, e) :: p ->
        S.add_fact (S.eq_bitstring [Var v; e]);
        let e = extract e in
        sort_defs !defs @ (Let (VPat v, e) :: normalize p)

      | Let _ :: _ ->
        fail "normal_form: impossible: let patterns unexpected"
                        
      | In vs as s :: p -> 
        List.iter (fun v -> S.add_fact (S.is_defined (Var v))) vs;
        s :: normalize p
        
      | (Test _ | Test_eq _ | Out _ | New _ | Event _ | Yield | Comment _ ) as s :: p ->
        let move_out e = match e with
          | Concat _ | Range _ | Annotation _ -> mk_var (extract e)
          | Var _ | Sym (Fun _, _) -> extract e
          | e when not (is_cryptographic e) -> mk_var (extract e)  
          | e -> 
            fail "Normal form: impossible: %s" (E.to_string e)
        in
        let s = Stmt.descend move_out s in
        sort_defs !defs @ (s :: normalize p)
        
      | [] -> []
  in
  S.reset_facts ();
  let p = normalize p in
  S.reset_facts ();
  simplify_lets p

(*************************************************)
(** {1 Extraction helper} *)
(*************************************************)

let extract_def e = 
  let vs = E.vars e in
  let args = mk_formal_args (List.length vs) |> List.map ~f:E.var in
  let e = E.subst vs args e in
  vs, e
  
(*************************************************)
(** {1 Arithmetic expressions} *)
(*************************************************)

let extract_arithmetic p: iml * sym_defs =

  let defs = ref [] in

  let rec extract e = 
    match e with
    | e when not (is_cryptographic e) -> 
      let vs, def = extract_def e in
      let f = Fun (Var.fresh "arithmetic", List.length vs) in
      defs := (f, def) :: !defs;
      let args = List.map E.var vs in
      Sym (f, args)
      
    | e -> E.descend extract e
  in   
   
  let p = map_without_auxiliary extract p in
  p, Sym.Map.of_list !defs


(*************************************************)
(** {1 Constants} *)
(*************************************************)

(*
  TODO: just return Const symbols in a sym_def
*)
(**
  Returns definitions of extracted constants. 
*)
let extract_constants concats p: iml * exp Var.Map.t = 
  
  let defs = ref Var.Map.empty in
  
  let mk_const name def =
    defs := Var.Map.add name def !defs;
    Var name
  in
  
	let rec extract e =
    match e with
    | Int ival -> mk_const ("integer_" ^ Int64.to_string ival) e
    | String s -> mk_const ("string_" ^ s) e
    | Sym (c, []) when Sym.Map.mem c concats ->
      let def = find_definition c concats in
      mk_const ("const_" ^ (Sym.to_string c)) def 
            
    | e -> E.descend extract e
  in
  
  let p = map_without_auxiliary extract p in
  p, !defs



(*************************************************)
(** {1 Concatenations} *)
(*************************************************)

let extract_concats p: iml * sym_defs =

  let concats: (sym * sym_def) list ref = ref [] in

  (*
    Check whether the concat definition only consists of formal arguments
    (no lengths or tags).
  *)
  let rec is_trivial_concat: exp list -> bool = function
    | Var _ :: es -> is_trivial_concat es 
    | [] -> true
    | _ :: es -> false
  in

  let extract : exp -> exp = function
    | Concat es as e ->
      debug "extract, e = %s" (E.dump (Concat es));
      let vs, def = extract_def e in 
      let f_c = new_concat_sym (List.length vs) in
      concats := (f_c, def) :: !concats;
      debug "extract, e_new = %s" (E.dump def);
      begin match def with
        | Concat es when is_trivial_concat es ->
          fail
            "The concatenation does not contain argument lengths or tags. This may lead to non-termination. %s"
            (E.dump def)
        | _ -> ()
      end;
      let args = List.map E.var vs in      
      Sym (f_c, args)
      
    | e -> e
  in
      
  let p = map_without_auxiliary extract p in
  p, Sym.Map.of_list !concats

(**
  If [use_type_info], we don't require lengths for arguments of fixed-length types. 
*)
let is_injective_concat sym def =
  (*
  debug "is_injective_concat: %s" (E.to_string def);
  *)
	match def with 
  | Concat es ->
    (* if use_type_info then
      fail ("use_type_info: fix code")
      (*
	    let (ts, _) = 
	      try List.assoc name !fun_types
	      with Not_found -> fail ("is_injective_concat: concat " ^ name ^ " has no type") in
	    check ts [] es
      *)
    else *) begin
      let args = List.filter (function Var _ -> true | _ -> false) es in
      let args_with_lens = List.filter_map (function BS (Len v, _) -> Some v | _ -> None) es in
      let args_without_lens = List.diff args args_with_lens in 
      (*
      debug "args: %s" (E.list_to_string args);
      debug "lens: %s" (E.list_to_string lens);
      debug "args_without_lens: %s" (E.list_to_string args_without_lens);
      *)
      List.length args_without_lens <= 1
    end
  | _ -> false

type encoder_fact = 
  | Disjoint of sym * sym
  | Equal of sym * sym
    
let encoder_fact (s, e) (s', e') = 
  
  let rec scan es es' =
    debug "encoder_fact: matching %s and %s" (E.dump_list es) (E.dump_list es'); 
    match es, es' with
      | e :: es, e' :: es' when S.equal_bitstring e e' -> scan es es'
      | e :: es, e' :: es' when is_tag e && is_tag e' && S.equal_int (Len e) (Len e') -> Some (Disjoint (s, s'))
      | [], [] -> Some (Equal (s, s'))
      | _ -> None
  in
  match e, e' with
    | Concat es, Concat es' -> scan es es'
    | _ -> failwith "encoder_fact: impossible"

        
let rec encoder_facts: (sym * sym_def) list -> encoder_fact list = function
  | c :: cs -> 
    List.filter_map ~f:(encoder_fact c) cs @ encoder_facts cs
  | [] -> []
  

    
(*************************************************)
(** {1 Extracting Parsers} *)
(*************************************************)

let extract_parsers p =

  let parsers = ref [] in
 
  let extract e = 
    match e with
    | Range (Var v, _, _) ->
      debug "adding parser for the expression %s" (E.to_string e);
      
      let vs, def = extract_def e in
      if vs <> [v] then fail "extract_parsers: impossible";
      
      let f_p = new_parser_sym () in
      
      (*
      debug ("adding parser, " ^ Sym.to_string f_p ^"(x) = " ^ E.dump def);
      *)
      
      parsers := (f_p, def) :: !parsers;
      
      let args = List.map E.var vs in
      Sym (f_p, args)
      
    | e -> e
  in
      
  let p = map_without_auxiliary extract p in
  p, Sym.Map.of_list !parsers


(*************************************************)
(** {1 Extracting Auxiliary Test Conditions} *)
(*************************************************)

(**
  Returns arities of extracted expressions.
*)
let extract_auxiliary p: iml * sym_defs =

  let arities = ref [] in

  let rec extract = function
    | Aux_test e :: p ->  
      let vs, def = extract_def e in
      let f = Fun (Var.fresh "auxiliary", List.length vs) in
      arities := (f, def) :: !arities;
      let args = List.map E.var vs in
      Test (Sym (f, args)) :: Aux_test e :: extract p
      
    | s :: p -> s :: extract p
    | [] -> []
  in   
   
  let p = extract p in
  p, Sym.Map.of_list !arities



(*************************************************)
(** {1 Parsing Rules} *)
(*************************************************)

let compute_parsing_rules fun_types (parsers: sym_defs) (concats: sym_defs): parsing_eq list =
  
  let parsing_eqs = ref [] in
  
  let check_type nargs p c e =
    let (pts, pt) = Sym.Map.find p fun_types in
    let (cts, ct) = Sym.Map.find c fun_types in
    if pts <> [ct] then false else
    begin
      let args = mk_formal_args nargs |> List.map ~f:E.var in 
      List.any (List.map2 (fun arg t -> arg = e && t = pt) args cts) 
    end
  in
    
  let apply_parser f_p parser_def f_c concat_def =
    let arg = mk_arg 0 in
    let e = E.subst [arg] [concat_def] parser_def in 
    debug "apply_parser: e after subst arg = %s" (E.dump e);
    let e' = Simplify.full_simplify e in
    debug "apply_parser %s to %s: \n  %s \n  ~> %s  \n" (Sym.to_string f_p) (Sym.to_string f_c)  
                                                       (E.dump e) (E.dump e');
    if check_type (Sym.arity f_c) f_p f_c e' 
    then [((f_p, f_c), e')]
    else []
  in 

  let compute_rules_for_concat f_c concat_def =
    let parsers = Sym.Map.to_list parsers in
    let (ts, _) = Sym.Map.find f_c fun_types in
    let arg_facts =
      List.mapi ts ~f:(fun i t -> 
        S.in_type (Var (mk_arg i)) t) 
    in
    List.iter arg_facts ~f:S.add_fact; 
    (* S.add_fact (S.is_defined concat_def); *)

    (* We expect some conditions to fail when the parser doesn't match. *)
    S.warn_on_failed_conditions false;    
    let new_eqs = 
      List.concat_map (fun (f_p, parser_def) ->
        apply_parser f_p parser_def f_c concat_def)
        parsers
    in
    S.warn_on_failed_conditions true;
    S.reset_facts ();
    (* This is not a good warning because sometimes we send tag|msg together, but receive tag and msg separately. *)
    (* 
    if new_eqs = [] 
    then warn "No parsing equations found for %s" (Sym.to_string f_c);
    *)
    parsing_eqs := new_eqs @ !parsing_eqs;
  in
  
  Sym.Map.iter compute_rules_for_concat concats;
  !parsing_eqs

(*************************************************)
(** {1 Parsing Safety} *)
(*************************************************)

let well_formed e_c = 
  let args = List.filter (function Var _         -> true | _ -> false) e_c in
  let lens = List.filter (function BS (Len _, _) -> true | _ -> false) e_c in
  (* debug "well_formed: %s, args = %s, lens = %s" (E.list_to_string e_c) (E.list_to_string args) (E.list_to_string lens); *)
  if not (List.distinct args) || not (List.distinct lens) then false
  else 
    let args_with_lens = List.map (function BS (Len v, _) -> v | _ -> fail "well_formed: impossible") lens in
    (* debug "well_formed: args_with_lens = %s" (E.list_to_string args_with_lens); *)
    match List.multidiff (=) args args_with_lens with
      | [e] -> e = List.last e_c
      | _ -> false

let rec mk_parsers ls ps es e_c = 
  let x = Var (mk_arg 0) in
  match e_c with
    | e_i :: e_c ->
      let l = 
        match e_i, e_c with
          | _, [] ->
            Sym (Minus_int, [Len x; Simplify.sum ls])
          | Var _ as v, _ ->
            (* debug "looking for %s in %s" (E.dump v) (E.dump_list es); *) 
            (* Need comparison in this order as es will contain lengths of lengths *)
            List.combine es ps
            |> List.first_some ~f:(function
                | (BS (Len v', itype), p) when v = v' -> Some (Val (p, itype)) 
                | _ -> None)
            |> Option2.value_exn
          | e_i, _ -> 
            Len e_i
      in
      let p = Range (x, Simplify.sum ls, l) in
      mk_parsers (ls @ [l]) (ps @ [p]) (es @ [e_i]) e_c
      
    | [] -> ps

let rec tag_facts ps e_c =
  match ps, e_c with
    | p :: ps, (BS (Len _, _) | Var _) :: e_c ->
      tag_facts ps e_c
    | p :: ps, e_t :: e_c ->
      S.eq_bitstring [p; e_t] :: tag_facts ps e_c
    | [], [] -> []
    | _ -> failwith "tag_facts: impossible"
      

let inrange facts e c c_def = 
  let x = mk_arg 0 in
  match c_def with
  | Concat e_c when well_formed e_c ->
    
    push_debug "inrange";
    
    let ps = mk_parsers [] [] [] e_c in
    debug "inrange: parsers: %s\n" (E.list_to_string ps);
    let fields = List.map S.is_defined ps in
    let tags = tag_facts ps e_c in
    
    let parse_facts = List.map (E.subst [x] [e]) (fields @ tags) in

    pop_debug "inrange";

    S.implies facts parse_facts
    
  | _ -> false

let match_concat parsing_eqs facts p e (c, c_def) =
  debug "\nmatch_concat: checking %s(%s) against concat %s" (Sym.to_string p) (E.to_string e) (Sym.to_string c);
  (*
    debug (sprintf "check_parsing_safety: the parser %s is not an inverse of %s" p c); 
    debug (sprintf "check_parsing_safety: no concat satisfies the application of %s to %s" p (dump e));
  *) 
  if not (is_injective_concat c c_def) || not (inrange facts e c c_def) then None
  else 
    match maybe_assoc (p, c) parsing_eqs with
      | Some (Var v) ->
        let vs = mk_formal_args (Sym.arity c) in
        Some (c, List.find_index_exn ((=) v) vs)
      | _ -> None 

let safe_parse (concats: sym_defs) parsing_eqs facts f_p e =
  debug "safe_parse, facts = %s" (E.list_to_string facts); 
  List.first_some ~f:(match_concat parsing_eqs facts f_p e) (Sym.Map.bindings concats)


(*************************************************)
(** {1 Trailing computation} *)
(*************************************************)

(**
  Remove unobservable computations at the end of a process.
*)
let remove_trailing_computations p =

  let rec remove p = 
    match p with
    | (Out _ | Event _) :: _ -> p 
    | s :: p -> remove p
    | [] -> []
  in
  
  List.rev (remove (List.rev p))       

(*************************************************)
(** {1 Cleanup} *)
(*************************************************)

(*
(**
  Leave only basic concats. Also remove unused concats (those turned into constants).
*)
*)
let cleanup_defs p (defs: sym_defs): sym_defs =

  let contains_sym c s = List.exists (E.contains_sym c) (Stmt.children s) in

  Sym.Map.filter (fun s _ -> List.exists (contains_sym s) p) defs
  
  
let cleanup_parsing_eqs p (eqs: parsing_eq list): parsing_eq list =

  let contains_sym sym stmt = List.exists (E.contains_sym sym) (Stmt.children stmt) in

  List.filter (fun ((f_p, _), _) -> List.exists (contains_sym f_p) p) eqs


(* 680 lines *)
