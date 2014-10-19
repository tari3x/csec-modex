(*
  Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
  This file is distributed as part of csec-tools under a BSD license.
  See LICENSE file for copyright notice.
*)

open Common

open Type
open Sym
open Exp
open Iml
open Iml.Pat
open Iml.Stmt

module E = Exp
module S = Solver

open Transform

open Printf

type cvfact = CV_fact.t

(********************************************************)
(** {1 Replace inverse functions by pattern matching} *)
(********************************************************)

let is_inverse f =
  match Str.split (Str.regexp "_") f with
    | "inverse" :: _ -> true
    | _ -> false

let inverse_of f =
  Fun (Str.replace_first (Str.regexp "inverse_") "" f,
       (1, Kind.Bitstring))

let rec check_no_inverse : type a. a exp -> unit = fun e ->
  match e with
  | Sym (Fun (f, _), _) when is_inverse f ->
    fail "inverse function not directly in let-bindig: %s" (E.to_string e)
  | e -> E.iter_children {E.f = check_no_inverse} e

let rec match_inverse p =
  match p with
    | Let (VPat v, Sym (Fun (f, _), [e])) :: p when is_inverse f ->
      Let (FPat (inverse_of f, [VPat v]), e) :: match_inverse p

    | s :: p ->
      Stmt.iter_children {E.f = check_no_inverse} s;
      s :: match_inverse p

    | [] -> []


(*************************************************)
(** {1 Use pattern matching for safe parsing} *)
(*************************************************)

let mk_pattern f_c arity v i =
  let pat = List.replicate arity Underscore in
  FPat (f_c, List.set_element i (VPat v) pat)

(**
  Expects formatting-normal form.
*)
let match_safe_parsers
    fun_types
    (parsers : bitstring Sym_defs.t)
    (concats : bitstring Sym_defs.t)
    parsing_eqs facts p =

  let rec do_match facts = function
    | (Let (VPat v, Sym (Fun (_, (_, Kind.Bitstring)) as f_p, [e]))) as s :: p
        when Sym_defs.mem f_p parsers ->
      begin match safe_parse fun_types concats parsing_eqs facts f_p e with
      | Some (f_c, i) ->
        Let (mk_pattern f_c (Sym.arity f_c) v i, e) :: do_match facts p
      | None ->
        s :: do_match facts p
      end

    | Aux_test e :: p ->
      Aux_test e :: do_match (facts @ [e]) p

    | Assume e :: p ->
      Assume e :: do_match (facts @ [e]) p

    | s :: p -> s :: do_match facts p

    | [] -> []
  in
  do_match facts p

(* CR: This is broken, you shouldn't move pattern matches past conditionals.  Have a pass
   that moves conditionals as far up as possible first. *)
let merge_patterns ~fun_types p =

  let choose_symbol f vs f' vs' =
    let rec vote ts vs ts' vs' =
      match ts, vs, ts', vs' with
      | t :: ts, v :: vs, t' :: ts', v' :: vs' ->
        begin
          if t = t' then vote ts vs ts' vs'
          else match v, v' with
          | VPat _, Underscore ->
            f :: vote ts vs ts' vs'
          | Underscore, VPat _ ->
            f' :: vote ts vs ts' vs'
          | Underscore, Underscore ->
            vote ts vs ts' vs'
          | VPat _, VPat _ ->
            (* Types are not equal, so make an inconsistent vote. *)
            [f; f']
          | _ -> assert false
        end
      | [], [], [], [] -> []
      | _ -> assert false
    in
    let rec tally vote = function
      | [] -> vote
      | f :: fs ->
        match vote with
        | Some f'  ->
          if f = f' then tally (Some f) fs else None
        | None -> tally (Some f) fs
    in
    let ts, _  = Fun_type_ctx.find f  fun_types in
    let ts', _ = Fun_type_ctx.find f' fun_types in
    match vote ts vs ts' vs' with
    | [] -> Some f
    | fs -> tally None fs
  in

  let merge vpat vpat' =
    match vpat, vpat' with
    | VPat v, _ | Underscore, VPat v  -> VPat v
    | Underscore, Underscore -> Underscore
    | _ -> failwith "merge_patterns: impossible"
  in

  let merge_pattern = List.map2 ~f:merge in

  let rec match_vars pat pat' =
    match pat, pat' with
      | VPat v :: pat, VPat v' :: pat' ->
        (v', Var (v, Kind.Bitstring)) :: match_vars pat pat'
      | _ :: pat, _ :: pat' -> match_vars pat pat'
      | [], [] -> []
      | _ -> failwith "match_vars: impossible"
  in

  let rec collect_pattern f vs e p =
    match p with
    | [] -> [], FPat (f, vs)
    | s :: p ->
      let default () =
        let p, pat = collect_pattern f vs e p in
        s :: p, pat
      in
      match s with
      | Let (FPat (f', vs'), e') when e = e' ->
        begin match choose_symbol f vs f' vs' with
        | None -> default ()
        | Some f ->
          let vs = merge_pattern vs vs' in
          let xs, xs' = List.split (match_vars vs vs') in
          let p = Iml.subst xs xs' p in
          collect_pattern f vs e p
        end
      | _ -> default ()
  in

  let rec merge = function
    | Let (FPat (f, vs), e) :: p ->
      let p, pat = collect_pattern f vs e p in
      Let (pat, e) :: merge p
    | s :: p -> s :: merge p
    | [] -> []
  in
  merge p

let test_merge_patterns () =
  let f1 = Fun ("f1", (2, Kind.Bitstring)) in
  let f2 = Fun ("f2", (2, Kind.Bitstring)) in
  let e = String ['x'] in
  let p =
    [ Let (FPat (f1, [VPat "v1"; Underscore]), e)
    ; Let (FPat (f2, [Underscore; VPat "v2"]), e) ]
  in
  let t1 = Type.Named ("t1", None) in
  let t2 = Type.Named ("t2", None) in

  let fun_types =
    Fun_type_ctx.of_list [ f1, ([t1; t1], Type.Bitstring)
                         ; f2, ([t1; t2], Type.Bitstring)]
  in
  let p' = [ Let (FPat (f2, [VPat "v1"; VPat "v2"]), e) ] in
  test_result ~expect:p' (merge_patterns ~fun_types p) Iml.to_string;

  let fun_types =
    Fun_type_ctx.of_list [ f1, ([t1; t1], Type.Bitstring)
                         ; f2, ([t2; t2], Type.Bitstring)]
  in
  test_result ~expect:p (merge_patterns ~fun_types p) Iml.to_string


(*************************************************)
(** {1 Zero functions} *)
(*************************************************)

module Zero_funs = struct
  (* Types for which we need to generate ZT, ZT', and possibly Zero_t

     Bitstring zeros may be used in auxiliary_facts.
  *)
  let zts = ref [Type.Bitstring]

  let zero_fun t =
    zts := t :: !zts;
    make_sym ("Z" ^ Type.to_string t) ~arity:1

  (* Assume that zero_fun will be called for all of these, so no need to add to zts. *)
  let zero_fun_prime t =
    make_sym ("Z" ^ Type.to_string t ^ "_prime") ~arity:1

  let zero_sym t =
    zts := t :: !zts;
    make_const ("zero_" ^ Type.to_string t)

  let zero_defs () =
    (* Suitable for generating sym_defs and Fun_type_ctx.t *)
    let z_fun_info t =
      let zt = zero_fun t in
      let zt' = zero_fun_prime t in
      let zero_t = zero_sym t in
      [(zt,  Unknown Kind.Bitstring), (zt,  ([t], t));
       (zt', Unknown Kind.Bitstring), (zt', ([t], t))]
      @ if Type.has_fixed_length t
        then [(zero_t, Unknown Kind.Bitstring), (zero_t, ([], t))]
        else []
    in
    let z_defs, z_types =
      List.concat_map ~f:z_fun_info (List.dedup !zts) |> List.split
    in
    let z_defs = Sym_defs.of_list z_defs in
    let z_types = Fun_type_ctx.of_list z_types in
    z_defs, z_types
end

(*************************************************)
(** {1 Regularity Properties} *)
(*************************************************)

(**
  Return the zero equations, zero function definitions and types
  (including definitions and types for zero constants of fixed types).

  Generate the following equations:

    - for each conc : T1 x ... x Tn -> T
      ZT(conc(x1, ..., xn)) = ZT'(conc(ZT1(x1), ..., ZTn(xn)))

    - for each cast_T1_T2:
      ZT2(cast_T1_T2(x)) = ZT2'(cast_T1_T2(ZT1(x)))

    - for each fixed type T that occurs anywhere in argument types in fun_types:
      ZT(x) = Zero_T
*)
let zero_facts
    (concats : bitstring Sym_defs.t)
    (casts: (bitstring Type.t * bitstring Type.t) list)
    (fun_types: Fun_type_ctx.t) : cvfact list =

  let zero_of e t = Sym (Zero_funs.zero_fun t, [e]) in

  let concat_fact c =
    let ts, t = Fun_type_ctx.find c fun_types in
    let args = mk_formal_args (Sym.arity c) |> List.map ~f:E.var in
    let zt = Zero_funs.zero_fun t in
    let zt' = Zero_funs.zero_fun_prime t in
    E.eq_bitstring [Sym (zt, [Sym (c, args)]);
                    Sym (zt', [Sym (c, List.map2 ~f:zero_of args ts)])]
  in

  let cast_fact (t1, t2) =
    let sym = Cast (t1, t2) in
    let x = Var ("x", Kind.Bitstring) in
    let zt2 = Zero_funs.zero_fun t2 in
    let zt2' = Zero_funs.zero_fun_prime t2 in
    E.eq_bitstring [Sym (zt2,  [Sym (sym, [x])]);
                    Sym (zt2', [Sym (sym, [zero_of x t1])])]
  in

  let const_fact t =
    let zt = Zero_funs.zero_fun t in
    let zero_t = Sym (Zero_funs.zero_sym t, []) in
    let x = Var ("x", Kind.Bitstring) in
    E.eq_bitstring [Sym (zt, [x]); zero_t]
  in

  let concat_facts = List.map ~f:concat_fact (Sym_defs.keys concats) in
  let cast_facts = List.map ~f:cast_fact casts in
  let fixed_types =
    Fun_type_ctx.map_bindings fun_types
      { Fun_type_ctx.f = fun _ (ts, _) -> ts }
    |> List.concat
    |> List.filter ~f:Type.has_fixed_length
    |> List.dedup
  in
  let const_facts = List.map ~f:const_fact fixed_types in
  let _, z_types = Zero_funs.zero_defs () in
  let facts =
    List.map
      (concat_facts @ cast_facts @ const_facts)
      ~f:(CV_fact.make (Fun_type_ctx.compatible_union [fun_types; z_types]))
  in
  facts

(********************************************************)
(** {1 Auxiliary Test Properties} *)
(********************************************************)

(*
  There are two ways to check
    (len(x) = len(y)) => (def[x/arg] = def[y/arg]).

  The first way is to do length substitutions and then check syntactic equality.
  One needs to expand lengths because of things like
    !(cast_to_int[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + cast_to_int[false,4,false,8](len55)))

  The other way is to use the solver directly, but then you need to show overflow safety
  as well. When formalising, you need to replace auxiliary facts by hardened facts that
  check overflow safety.

  The second option is conceptually simpler, but less efficient. Another problem with the
  second option is that it is tricky to tell the solver to assume overflow safety for an
  expression. One cannot just extract the overflow safety fact, because that itself may
  not be overflow safe. For these reasons I'm using the first option now.

  Another reason for checking syntactic equality is that we actually want to simplify the
  expressions
*)
let auxiliary_facts
    (concats : bitstring Sym_defs.t)
    (auxiliary : bool Sym_defs.t)
    (fun_types : Fun_type_ctx.t) : cvfact list =

  (* facts for a single auxiliary test *)
  let facts fun_types sym def arg_types =
    let num_args = List.length arg_types in
    let args = mk_formal_args num_args in
    let zero_of v t = Sym (Zero_funs.zero_fun t, [Var (v, Kind.Bitstring)]) in
    let replace_len v =
      let rec replace : type a. a exp -> a exp = function
        | Len (Var (v', Kind.Bitstring)) when v' = v ->
          Var (Var.fresh "len", Kind.Int)
        | e -> E.descend {E.descend = replace} e
      in
      replace
    in
    let rec expand_lens : type a. a exp -> a exp = function
      | Len (Concat es) ->
        List.map ~f:E.len es |> E.sum |> expand_lens
      | e -> E.descend {E.descend = expand_lens} e
    in
    let can_erase arg =
      let x = Var (Var.fresh "x", Kind.Bitstring) in
      let y = Var (Var.fresh "y", Kind.Bitstring) in
      let def = replace_len arg def in
      let def_x = E.subst [arg] [x] def in
      let def_y = E.subst [arg] [y] def in
      DEBUG "can_erase: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
      def_x = def_y
    in
    let concat_pairs arg t =
      let pair c =
        match Fun_type_ctx.maybe_find c fun_types with
          (* I don't exactly understand why restricting to the same type is enough, but it
             feels like it should be enough, and it looks like it is. *)
        | Some (ts, t') when t = t' ->
          let c_def = Sym_defs.find c concats in

          (* Rename args of c_def to avoid collision with args of def. *)
          let c_args = List.map ~f:(fun _ -> Var.fresh "c_arg") (1 -- (Sym.arity c)) in
          let c_def = E.subst_v (mk_formal_args (Sym.arity c)) c_args c_def in
          (* For simplifcation. *)
          S.add_fact (E.is_defined c_def);

          (* We expect some conditions to fail when trying to simplify something that's
             impossible to simplify. *)
          S.warn_on_failed_conditions false;
          let def =
            E.subst [arg] [c_def] def
            (* We may be substituting an encoder inside a parser, so we need to
               simplify. *)
            |> Simplify.full_simplify
            (* Deal with stuff like
               {[
                 !(cast_to_int[false,4,false,8](len("p"|len54|x92|x93)) <=
                     (i5 + cast_to_int[false,4,false,8](len55)))
               ]}
            *)
            |> expand_lens
            (* Replace all argument lengths by fresh variables *)
            |> fun init -> List.fold_right ~f:replace_len ~init c_args
          in
          S.warn_on_failed_conditions true;

          let xs = List.map ~f:(fun _ -> Var.fresh "x") (1 -- (Sym.arity c)) in
          let ys = List.map ~f:(fun _ -> Var.fresh "y") (1 -- (Sym.arity c)) in
          let def_x = E.subst_v c_args xs def in
          let def_y = E.subst_v c_args ys def in
          DEBUG "concat_pairs: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
          if def_x = def_y then
            let zxs = List.map2 ~f:zero_of xs ts in
            let xs = List.map ~f:E.var xs in
            Some (Sym (c, xs), Sym (prime c, zxs))
          else None
        | _ -> None
      in
      List.filter_map ~f:pair (Sym_defs.keys concats)
    in
    let mk_fact sym1 sym2 arg_pairs =
      let args1, args2 = List.split arg_pairs in
      if args1 = args2 then []
      else
        [ Sym (Logical Logical.Eq, [Sym (sym1, args1); Sym (sym2, args2)])
          |> CV_fact.make fun_types
        ]
    in
    let var x = Var (x, Kind.Bitstring) in
    (* First phase: zero out things that can be zeroed out completely. *)
    let x_facts =
      List.map2 arg_types args ~f:(fun t -> function
      | x when can_erase x -> var x, zero_of x t
      | x -> var x, var x)
      |> mk_fact sym (prime sym)
    in
    (* Apply the rewriting to the result of the previous phase if any. *)
    let sym =
      match x_facts with
      | [] -> sym
      | _ -> prime sym
    in
    (* Second phase: rewrite specific concats.*)
    let mk_concat_fact x e1 e2 =
      List.map args ~f:(function
      | x' when x' = x -> e1, e2
      | x -> var x, var x)
      |> mk_fact sym sym
    in
    let concat_facts =
      List.map2 args arg_types ~f:(fun x t ->
        if can_erase x then []
        else List.concat_map (concat_pairs x t) ~f:(fun (e1, e2) ->
          mk_concat_fact x e1 e2))
      |> List.concat
    in
    x_facts @ concat_facts
  in
  S.reset_facts ();
  let fun_types =
    List.fold (Sym_defs.keys auxiliary) ~init:fun_types ~f:(fun fun_types f ->
      Fun_type_ctx.add_primed fun_types f)
  in
  Sym_defs.to_list auxiliary
  |> List.concat_map ~f:(fun (sym, def) ->
    DEBUG "Auxiliary facts: checking %s: %s" (Sym.to_string sym) (E.to_string def);
    let (ts, _) = Fun_type_ctx.find sym fun_types in
    facts fun_types sym def ts)


(*************************************************)
(** {1 Input and Output Merging} *)
(*************************************************)

let merge_in_out p =

  let rec merge_in (vs: var list) p =
    match (vs, p) with
    | vs, In [v] :: p -> merge_in (v :: vs) p
    | [], s :: p -> s :: merge_in [] p
    | vs, (Out _ as s) :: p ->
      In vs :: s :: merge_in [] p
    | vs, s :: p -> s :: merge_in vs p
    | vs, [] -> [In vs] (* including vs =  [] *)
  in

  (*
    Requires only-variables-in-write form.
  *)
  let rec merge_out es p =
  match (es, p) with
    | es, Out [e] :: p -> merge_out (e :: es) p
    | [], s :: p -> s :: merge_out [] p
    | es, (In _ as s) :: p ->
      Out es :: s :: merge_out [] p
    | es, s :: p -> s :: merge_out es p
    | [], [] -> [Yield]
    | es, [] -> [Out es]
  in

  List.rev (merge_in [] (List.rev (merge_out [] p)))

(*************************************************)
(** {1 The full model} *)
(*************************************************)

module Model = struct
  type t = {
    client : iml;
    server : iml;
    template : Template.t;
    var_types : Type_ctx.t;
    fun_types : Fun_type_ctx.t;

    concats : bitstring Sym_defs.t;
    parsers : bitstring Sym_defs.t;
    arith : bitstring Sym_defs.t;
    auxiliary : bool Sym_defs.t;
    zero_funs : bitstring Sym_defs.t;

    primed : Sym.any_bitstring list;

    auxiliary_facts : CV_fact.t list;
    zero_facts : CV_fact.t list;

    encoder_facts : Aux_fact.t list;
    arithmetic_facts : Aux_fact.t list;

    parsing_eqs : parsing_eq list;
  }

  let rec collect_primed :
  type a. a exp -> Sym.any_bitstring list =
    fun e ->
      match e with
      | Sym (Fun _ as sym, es) ->
        begin match Sym.unprime sym with
        | Some sym ->
          Sym.Any_bitstring sym :: List.concat_map es ~f:collect_primed
        | None -> List.concat_map es ~f:collect_primed
        end
      | e -> List.concat (Exp.map_children { f = collect_primed } e)

  (* CR-soon: consider using Fun_type_ctx.add_primed. *)
  let add_primed t =
    let originals =
      List.concat_map t.auxiliary_facts ~f:(fun (CV_fact.Forall (_, fact)) ->
        collect_primed fact)
      |> List.dedup
    in
    let fun_types =
      List.fold_left originals ~init:t.fun_types ~f:(fun fun_types (Any_bitstring sym) ->
        let t = Fun_type_ctx.find sym t.fun_types in
        Fun_type_ctx.add (Sym.prime sym) t fun_types)
    in
    let primed =
      List.map originals ~f:(fun (Any_bitstring sym) -> Any_bitstring (Sym.prime sym))
    in
    { t with fun_types; primed }
end

open Model

(*************************************************)
(** {1 CV Output} *)
(*************************************************)

module Aux_fact = struct
  include Aux_fact

  let show_relation
      ((arg_types1, _), c1)
      ((arg_types2, _), c2)
      op =
    let id = ref 0 in

    let formal_arg _ =
      id := !id + 1;
      "var" ^ string_of_int !id
    in
    let show_arg v t =
      v ^ ": " ^ Type.to_string t
    in

    let args1 = List.map ~f:formal_arg arg_types1 in
    let args2 =
      if op = "<>" then List.map ~f:formal_arg arg_types2
      else args1
    in
    let all_args =
      List.dedup (List.map2 ~f:show_arg args1 arg_types1
                  @ List.map2 ~f:show_arg args2 arg_types2)
    in
    sprintf "forall %s;\n  %s(%s) %s %s(%s)."
      (String.concat ~sep:", " all_args)
      (Sym.to_string c1) (String.concat ~sep:", " args1)
      op
      (Sym.to_string c2) (String.concat ~sep:", " args2)

  let to_string = function
    | Disjoint (s, s') -> show_relation s s' "<>"
    | Equal    (s, s') -> show_relation s s' "="
end

module CV_fact = struct
  include CV_fact

  let to_string (Forall (args, e)) =
    let show_var (v, t) = v ^ ": " ^ Type.to_string t in
    "forall " ^ String.concat ~sep:", " (List.map ~f:show_var args)
    ^ ";\n\t" ^ E.to_string e ^ "."
end

let printf a = fprintf Common.out_channel a

let show_cv_stmt: Stmt.t -> string = fun s ->

  let rec show_exp_body : type a. a exp -> string = function
    | Var (v, _) -> v
    | Sym (Fun (s, _), []) -> s
    | Sym (s, es) ->
      begin match s with
      | Cast _ -> ()
      | Fun _ -> ()
      | s -> fail "print cv: unexpected symbol: %s" (Sym.to_string s)
      end;
      sprintf "%s(%s)"
        (Sym.to_string s)
        (String.concat ~sep:", " (List.map ~f:show_exp_body es))
    | Annotation (_, e) -> show_exp_body e
    | e -> "unexpected{" ^ E.dump e ^ "}"
  and show_in_var t name = name ^ ": " ^ Type.to_string t
  in

  match s with
    | In [v] ->
      "in(c_in, " ^ show_in_var Bitstring v ^ ");";

    | In vs ->
      "in(c_in, (" ^ String.concat ~sep:", " (List.map ~f:(show_in_var Bitstring) vs) ^ "));";

    | New (v, t) ->
      "new " ^ show_in_var t v ^ ";";

    | Out [e] ->
      "out(c_out, " ^ show_exp_body e ^ ");";

    | Out es ->
      "out(c_out, (" ^ String.concat ~sep:", " (List.map ~f:show_exp_body es) ^ "));";

    | Eq_test (e1, e2) ->
      "if " ^ show_exp_body e1 ^ " = " ^ show_exp_body e2 ^ " then "

    | Aux_test e ->
      "if " ^ show_exp_body e ^ " then "

    | Fun_test e ->
      "if " ^ show_exp_body e ^ " then "

    | Assume e ->
      Printf.sprintf "assume %s in" (show_exp_body e)

    | Event (name, es) ->
      "event " ^ name ^ "(" ^ String.concat ~sep:", " (List.map ~f:show_exp_body es) ^ ");"

    | Let (pat, e) ->
      "let " ^ Pat.dump pat ^ " = " ^ show_exp_body e ^ " in"

    | Yield -> "yield ."

    | Comment s -> sprintf "(* %s *)" s

let show_cv_process p =
  let zero =
    if p = [] then " 0 .\n" else
    match List.last p with
      | Yield -> "\n"
      | _ -> " 0 .\n"
  in
  let result = String.concat ~sep:"\n" (List.map ~f:show_cv_stmt p) ^ zero in
  result

let print_indent s = print_endline ("  " ^ s)

let write_cv model =
  let {
    client; server;
    template;
    var_types = _;
    fun_types;
    parsers;
    concats;
    arith;
    auxiliary;
    zero_funs;
    auxiliary_facts;
    zero_facts;
    (* funny, we never need these. *)
    parsing_eqs = _;
    encoder_facts;
    arithmetic_facts;
    primed
  } = model
  in
  let casts = List.dedup (Typing.casts client @ Typing.casts server) in
  let print_fun_def is_injective sym def =
    if Template.is_defined template sym
    then
      printf "(* %s is already defined in the template *)\n\n" (Sym.to_string sym)
    else begin
      begin match def with
      | Unknown _ -> ()
      | def -> print_endline ("(* " ^ Sym_defs.show_fun sym def ^ " *)")
      end;
      let compos = if is_injective then " [compos]." else "." in
      match sym with
      | Fun (s, (0, _)) ->
        let _, t = Fun_type_ctx.find sym fun_types in
        print_endline ("const " ^ s ^ ": " ^ Type.to_string t ^ ".");
        print_endline ""
      | sym ->
        print_endline ("fun "
                       ^ Sym.cv_declaration sym (Fun_type_ctx.find sym fun_types)
                       ^ compos);
        print_endline ""
    end
  in
  let print_concat sym def =
    print_fun_def (is_injective_concat fun_types sym def) sym def;
  in
  let print_cast (t, t') =
    print_endline ("fun " ^ Sym.to_string (Cast (t, t'))
                   ^ "(" ^ Type.to_string t ^ "): " ^ Type.to_string t' ^ " [compos].")
  in
  let print_arithmetic sym def =
    let is_injective = is_injective_arithmetic def in
    print_fun_def is_injective sym def
  in
  (* TODO: most of these can now be printed by converting to CV_facts *)
  let print_cast_eq (t, t') =
    (* check that the inverse function is defined at all *)
    if List.mem (t', t) ~set:casts && Type.subtype t t' then
    begin
      print_endline ("forall x: " ^ Type.to_string t ^ ";");
      print_endline ("  " ^ Sym.to_string (Cast (t', t)) ^ "(" ^ Sym.to_string (Cast (t, t')) ^ "(x)) = x.")
    end
  in
  (*
  let print_constant name def =
    let t = Type_ctx.find name model.var_types in
    print_endline ("(* " ^ E.dump def ^ " *)");
    print_endline ("const " ^ name ^ ": " ^ Type.to_string t ^ ".")
  in
  *)
  let print_aux_fact fact = print_endline (Aux_fact.to_string fact) in
  let print_cv_fact fact = print_endline (CV_fact.to_string fact) in

  let client_proc = show_cv_process client in
  let server_proc = show_cv_process server in

  List.iter ~f:print_endline (Template.crypto template);

  (*
  print_endline "\n(*************************** \n Constants \n***************************)\n";
  Var.Map.iter print_constant model.constants;
  *)

  print_endline "\n(*************************** \n  Formatting Functions \n***************************)\n";
  Sym_defs.iter ~f:print_concat concats;
  Sym_defs.iter ~f:(print_fun_def false) parsers;
  print_endline "";
  List.iter ~f:print_aux_fact encoder_facts;

  print_endline "\n(*************************** \n  Arithmetic Functions \n***************************)\n";
  Sym_defs.iter ~f:print_arithmetic arith;
  List.iter ~f:print_aux_fact arithmetic_facts;

  print_endline "\n(*************************** \n  Auxiliary Tests \n***************************)\n";
  Sym_defs.iter ~f:(print_fun_def false) auxiliary;

  print_endline "\n(*************************** \n  Zero Functions \n***************************)\n";
  Sym_defs.iter ~f:(print_fun_def false) zero_funs;

  print_endline "\n(*************************** \n  Primed Functions \n***************************)\n";
  List.iter primed ~f:(fun (Any_bitstring sym) ->
    print_fun_def false sym (Unknown Kind.Bitstring));

  print_endline "\n(*************************** \n  Typecasting \n***************************)\n";
  List.iter ~f:print_cast casts;
  List.iter ~f:print_cast_eq casts;

  print_endline "\n(*************************** \n  Auxiliary Facts \n***************************)\n";
  List.iter ~f:print_cv_fact auxiliary_facts;

  print_endline "\n(*************************** \n  Zero Facts \n***************************)\n";
  List.iter ~f:print_cv_fact zero_facts;

  print_endline "";

  List.iter ~f:print_endline (Template.crypto2 template);
  List.iter ~f:print_endline (Template.query template);

  print_endline "\n(*************************** \n  Model \n***************************)\n";
  print_endline "let client = ";
  print_endline client_proc;
  print_endline "let server = ";
  print_endline server_proc;

  List.iter ~f:print_endline (Template.envp template)

(*************************************************)
(** {1 Main} *)
(*************************************************)

let verbose = true

let rec remove_casts : type a. a exp -> a exp = function
  | Sym (Op (Sym.Op.Cast_to_int, _), [e]) -> remove_casts e
  | e -> E.descend {E.descend = remove_casts} e

let debug_iml client server title =
  if verbose
  then begin
    prerr_title title;
    prerr_endline "Client = ";
    prerr_endline (Iml.to_string client);
    prerr_endline "Server = ";
    prerr_endline (Iml.to_string server)
  end

let main () =

  let (client, server) = Symex.raw_in (open_in_bin Sys.argv.(1)) in

  let server = server |> remove_comments in
  let client = client |> remove_comments in

  debug_iml client server "initial IML";

  error_if_undefs server;
  error_if_undefs client;

  let server = remove_trailing_computations server in
  let client = remove_trailing_computations client in
  debug_iml client server "IML after removing trailing computations";

  let server = rewrite_xor server in
  let client = rewrite_xor client in
  debug_iml client server "IML after XOR rewriting";

  let server = rewrite_crypto_arithmetic_comparisons server in
  let client = rewrite_crypto_arithmetic_comparisons client in
  debug_iml client server "IML after arithmetic comparison rewriting";

  let server = normal_form server in
  let client = normal_form client in
  debug_iml client server "IML in normal form";

  let client = apply_name_annotations client in
  let server = apply_name_annotations server in
  debug_iml client server "IML after applying all name annotations";

  let client, client_concats = extract_concats client in
  let server, server_concats = extract_concats server in
  let concats = Sym_defs.disjoint_union [client_concats; server_concats] in

  debug_iml client server "IML after concat extraction";
  if verbose then Sym_defs.print concats;

  let client, client_parsers = extract_parsers client in
  let server, server_parsers = extract_parsers server in
  let parsers = Sym_defs.disjoint_union [client_parsers; server_parsers] in

  debug_iml client server "IML after parser extraction";
  if verbose then Sym_defs.print parsers;

  let server, server_arith = extract_arithmetic server in
  let client, client_arith = extract_arithmetic client in
  let arith = Sym_defs.disjoint_union [server_arith; client_arith] in
  debug_iml client server "IML after replacing arithmetic expressions";
  if verbose then Sym_defs.print arith;

  let server, server_auxiliary = extract_auxiliary server in
  let client, client_auxiliary = extract_auxiliary client in
  let auxiliary = Sym_defs.disjoint_union [server_auxiliary; client_auxiliary] in
  debug_iml client server "IML after adding formal versions of auxiliary tests";

  (*
  let client, client_constants = extract_constants concats client in
  let server, server_constants = extract_constants concats server in
  let constants = Var.Map.disjoint_union [server_constants; client_constants] in
  debug_iml client server "IML after constant extraction";
  *)

  let concats = cleanup_defs (client @ server) concats in
  let parsers = cleanup_defs (client @ server) parsers in

  (************************
    Typechecking
  *************************)

  let template = Template.read_file ~cv_lib_name:Sys.argv.(2) ~name:Sys.argv.(3) in
  let template_var_types = Template.var_types template in
  let fun_types = Template.fun_types template in
  prerr_title "Template Function Types: ";
  Fun_type_ctx.dump fun_types;
  prerr_title "Template Variable Types: ";
  Type_ctx.dump template_var_types;

  let inferred_var_types = Type_ctx.merge [Typing.infer fun_types client;
                                           Typing.infer fun_types server]
  in
  prerr_title "Inferred Variable Types";
  Type_ctx.dump inferred_var_types;
  let var_types = Type_ctx.merge [template_var_types; inferred_var_types] in

  let client_formatter_types = Typing.derive_unknown_types fun_types var_types client in
  let server_formatter_types = Typing.derive_unknown_types fun_types var_types server in

  let bitstring_defs = Sym_defs.disjoint_union [concats; parsers; arith] in
  let bool_defs = auxiliary in
  Typing.check_missing_types bitstring_defs bool_defs
    ~template_types:fun_types ~inferred_types:client_formatter_types client;
  Typing.check_missing_types bitstring_defs bool_defs
    ~template_types:fun_types ~inferred_types:server_formatter_types server;

  prerr_title "Inferred Client Types";
  Fun_type_ctx.dump client_formatter_types;

  prerr_title "Inferred Server Types";
  Fun_type_ctx.dump server_formatter_types;

  let fun_types =
    Fun_type_ctx.disjoint_union [fun_types; client_formatter_types; server_formatter_types]
  in

  push_debug "Typing.check";
  let client = Typing.check bitstring_defs fun_types template_var_types [] client in
  let server = Typing.check bitstring_defs fun_types template_var_types [] server in
  pop_debug "Typing.check";

  debug_iml client server "IML after typechecking";

  with_debug "Typing.check_robust_safety" (Typing.check_robust_safety concats) fun_types;

  (**********************************
    Remove redundant auxilary tests
  **********************************)

  push_debug "remove_redundant_auxiliary";
  let server = remove_redundant_auxiliary auxiliary var_types server in
  let client = remove_redundant_auxiliary auxiliary var_types client in
  debug_iml client server "IML after removing redundant auxiliary tests";
  pop_debug "remove_redundant_auxiliary";

  (************************
    Type-based warnings
  *************************)

  warn_on_non_injective_concats fun_types concats;

  (************************
    Template assertions
  *************************)

  Template.check_assertions template bitstring_defs;

  (************************
    Formatting facts
  *************************)

  let parsing_eqs = with_debug "parsing_eqs" (compute_parsing_rules fun_types parsers) concats in

  prerr_title "Parsing Equations";
  List.iter ~f:(fun eq -> prerr_endline (show_parsing_eq ~fun_types eq)) parsing_eqs;

  let parsers = cleanup_defs (client @ server) parsers in
  let parsing_eqs = cleanup_parsing_eqs (client @ server) parsing_eqs in

  push_debug "encoder_facts";
  let encoder_facts =
    Aux_fact.fun_facts fun_types (Sym_defs.to_list concats @ Sym_defs.to_list parsers)
  in
  pop_debug "encoder_facts";

  (************************
    Arithmetic facts
  *************************)

  let arithmetic_facts = Aux_fact.fun_facts fun_types (Sym_defs.to_list arith) in

  (************************
    Pattern matching
  *************************)

  push_debug "match_inverse";
  let client = match_inverse client in
  let server = match_inverse server in
  pop_debug "match_inverse";

  push_debug "parsing_safety";
  let client = match_safe_parsers fun_types parsers concats parsing_eqs [] client in
  let server = match_safe_parsers fun_types parsers concats parsing_eqs [] server in
  pop_debug "parsing_safety";

  let client = merge_patterns ~fun_types client in
  let server = merge_patterns ~fun_types server in

  debug_iml client server "IML after inserting pattern matching";

  (********************************************
    Bring the process into IO-alternating form
  *********************************************)

  let client = merge_in_out client in
  let server = merge_in_out server in

  debug_iml client server "IML after merging inputs and outputs";

  (************************
    Auxiliary tests
  *************************)

  push_debug "auxiliary_facts";
  let auxiliary_facts = auxiliary_facts concats auxiliary fun_types in
  pop_debug "auxiliary_facts";
  let client = remove_auxiliary client in
  let server = remove_auxiliary server in
  debug_iml client server "IML after removing auxiliary ifs";

  (************************
    Zero facts
  *************************)

  let casts = List.dedup (Typing.casts client @ Typing.casts server) in
  let zero_facts = zero_facts concats casts fun_types in
  let zero_funs, zero_fun_types = Zero_funs.zero_defs () in
  let fun_types = Fun_type_ctx.compatible_union [fun_types; zero_fun_types] in

  let model = {
    client; server;
    template;
    var_types;
    fun_types;
    parsers;
    concats;
    arith;
    auxiliary;
    zero_funs;
    auxiliary_facts;
    zero_facts;
    parsing_eqs;
    encoder_facts;
    arithmetic_facts;
    primed = []
  }
  in
  let model = Model.add_primed model in
  write_cv model

let test () =
  test_merge_patterns ()

