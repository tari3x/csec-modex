(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Type
open Sym
open Sym.Op
open Exp
open Iml
open Iml.Pat
open Iml.Stmt

module E = Exp
module S = Solver

(*************************************************)
(** {1 Formal Arguments} *)
(*************************************************)

let mk_arg id = ("arg" ^ string_of_int id)

let mk_arg_len id =
  Len (Var (mk_arg id, Kind.Bitstring))

let mk_formal_args n = List.map ~f:mk_arg (0 -- (n - 1))

module Sym_defs = struct
  include Sym.Map(E)

  (**
     We represent a lambda expression with n arguments by an expression containing variables
     (mk_arg 0) to (mk_arg (n - 1)).
  *)
  type 'a def = 'a exp

  let show_fun sym def =
    Sym.to_string sym ^ " := " ^ (E.to_string def)

  let print defs =
    prerr_endline "";
    iter ~f:(fun sym def -> prerr_endline (show_fun sym def)) defs;
    prerr_endline ""

  (* Writing a recursive expansion is a bit more tricky since you would need to know the
     kind of the map. *)
  let expand_top_def t e =
    match e with
    | Sym (Fun _ as sym, es) ->
      begin match maybe_find sym t with
      | None -> e
      | Some def ->
        let xs = mk_formal_args (List.length es) in
        E.subst xs es def
      end
    | e -> e
end

(**
  [parser(concat) = result]
*)
type parsing_eq = (bfun * bfun) * bterm


(*************************************************)
(** {1 Helpers} *)
(*************************************************)

(* TODO: make these local *)
let concat_id : int ref = ref 0
let parser_id : int ref = ref 0

(* CR-soon: move to Sym *)
let make_sym sym ~arity =
  Fun (sym, (arity, Kind.Bitstring))

let make_const sym =
  make_sym sym ~arity:0

let make_bool_sym sym ~arity =
  Fun (sym, (arity, Kind.Bool))

let new_concat_sym ~arity =
  make_sym ("conc" ^ string_of_int (increment concat_id)) ~arity

let new_parser_sym () =
  make_sym ("parse" ^ string_of_int (increment parser_id)) ~arity:1

(*************************************************)
(** {1 Typing} *)
(*************************************************)

module Type_ctx : sig
  type t

  val empty : t
  val singleton : Var.t -> bitstring Type.t -> t
  val add : Var.t -> bitstring Type.t -> t -> t
  val maybe_find : Var.t -> t -> bitstring Type.t option
  val find : Var.t -> t -> bitstring Type.t
  val mem : Var.t -> t -> bool
  val merge : t list -> t
  val of_list : (Var.t * bitstring Type.t) list -> t
  val to_list : t -> (Var.t * bitstring Type.t) list
  val dump : t -> unit
  val keys : t -> var list
end = struct
  module Map = Var.Map
  type 'a map = 'a Map.t
  type t = bitstring Type.t map
  include (Map : Custom_map with type 'a t := 'a map
                            and type key = Var.t)

  let dump t =
    iter (fun v t ->
      prerr_endline (Printf.sprintf "%s:  %s" v (Type.to_string t))) t;
    prerr_endline ""

  let merge ts =
    let merge_types _key t1 t2 = Some (Type.intersection t1 t2) in
    merge ~f:merge_types ts
end

module Fun_type_ctx = struct
  module Fun_type = struct
    type 'a t = (bitstring, 'a) Fun_type.t
    module Kind = Kind
    let kind (_, t) = Type.kind t
  end
  include Sym.Map_any (Fun_type)

  let dump t =
    iter t {f = fun f t -> prerr_endline (Sym.cv_declaration f t) };
    prerr_endline ""

  let add_primed (t : t) f : t =
    let typ = find f t in
    add (Sym.prime f) typ t
end

module Typing : sig
  val infer_exp : Fun_type_ctx.t -> 'a Type.t option -> 'a exp -> Type_ctx.t
  val infer : Fun_type_ctx.t -> iml -> Type_ctx.t

  val derive_unknown_types : Fun_type_ctx.t -> Type_ctx.t -> iml -> Fun_type_ctx.t

  val check
    :  bitstring Sym_defs.t
    -> Fun_type_ctx.t
    -> Type_ctx.t
    -> fact list
    -> iml
    -> iml

  val cast : bitstring Type.t -> bitstring Type.t -> bterm -> bterm
  val casts : iml -> (bitstring Type.t * bitstring Type.t) list

  (**
    Check robust safety of concats, as defined in the paper.
  *)
  val check_robust_safety : bitstring Sym_defs.t -> Fun_type_ctx.t -> unit

  (**
    Check that all functions for which we don't have a definition have a type.
  *)
  val check_missing_types
    :  bitstring Sym_defs.t
    -> bool Sym_defs.t
    -> template_types:Fun_type_ctx.t
    -> inferred_types:Fun_type_ctx.t
    -> iml
    -> unit

  val test : unit -> unit
end = struct

  let exp_type (type a) fun_types var_types (e : a exp) : a Type.t option =
    match e with
    | Var (v, Kind.Bitstring) ->
      Type_ctx.maybe_find v var_types
    | Annotation (Type_hint t, _) -> Some t
    | Sym (Fun _ as sym, _) ->
      Option.map (Fun_type_ctx.maybe_find sym fun_types) ~f:snd
    | e -> fail "Typing.exp_type: %s" (E.to_string e)

  let cast t t' e =
    if t = t' then e else
    Sym (Cast (t, t'), [e])

  let rec casts p =
    let rec casts_e
        : type a. a exp -> (bitstring Type.t * bitstring Type.t) list = fun e ->
      let cs = E.map_children { E.f = casts_e } e |> List.concat in
      match e with
      | Sym (Cast (t, t'), _) -> (t, t') :: cs
      | _ -> cs
    in
    match p with
    | s :: p ->
      List.concat (Stmt.map_children { E.f = casts_e } s) @ casts p
    | [] -> []

  let rec infer_exp
      : type a. Fun_type_ctx.t -> a Type.t option -> a exp -> Type_ctx.t
      = fun fun_types t e ->
      match e with
      | Var (v, Kind.Bitstring) ->
        begin match t with
        | None -> Type_ctx.empty
        | Some t -> Type_ctx.singleton v t
        end

      | Annotation (Type_hint t, e) -> infer_exp fun_types (Some t) e

      | Sym (Fun _ as f, es) ->
        begin match Fun_type_ctx.maybe_find f fun_types with
        | None ->
          Type_ctx.merge (List.map ~f:(infer_exp fun_types None) es)
        | Some (ts, _) ->
          Type_ctx.merge (List.map2 es ts ~f:(fun e t ->
            infer_exp fun_types (Some t) e))
        end

      | Annotation(_, e) -> infer_exp fun_types t e

      | Sym (Cast (t, _), [e]) ->
        infer_exp fun_types (Some t) e

      | Sym (Logical Logical.Eq, [e1; e2]) ->
        Type_ctx.merge [infer_exp fun_types (Some Type.Bool) e1;
                        infer_exp fun_types (Some Type.Bool) e2]

      | Sym (Bs_eq, [e1; e2]) ->
        Type_ctx.merge [infer_exp fun_types None e1;
                        infer_exp fun_types None e2]

      | e -> fail "infer_exp: unexpected expression %s" (E.dump e)


  let infer (fun_types: Fun_type_ctx.t) (p: iml) : Type_ctx.t =

    let exp_type fun_types e = exp_type fun_types Type_ctx.empty e in
    let infer_exp e = infer_exp fun_types e in

    let rec infer = function
      | Let (VPat v, e) :: p ->
        let ctx_e = infer_exp None e in
        let ctx_p = infer p in
        let ctx = Type_ctx.merge [ctx_e; ctx_p] in
        begin match exp_type fun_types e with
        | None -> ctx
        | Some t -> Type_ctx.add v t ctx
        end

      | Let ((FPat _ | Underscore), _) :: _ ->
        fail "infer_types: let patterns not supported: %s" (Iml.to_string p)

      | New (v, t) :: p ->
        let ctx = infer p in
        Type_ctx.add v t ctx

      | In vs :: p ->
        let ctx = infer p in
        List.fold_left vs ~init:ctx ~f:(fun ctx v -> Type_ctx.add v Bitstring ctx)

      | Aux_test _ :: p -> infer p

      | Fun_test e :: p ->
        let ctx_e = infer_exp (Some Bool) e in
        let ctx_p = infer p in
        Type_ctx.merge [ctx_e; ctx_p]

      | Eq_test (e1, e2) :: p ->
        let ctx1 = infer_exp None e1 in
        let ctx2 = infer_exp None e2 in
        let ctx_p = infer p in
        Type_ctx.merge [ctx1; ctx2; ctx_p]

      | Assume _ :: p ->
        infer p

      | Event (ev, es) :: p ->
        (* Events symbols are of type bool in CV *)
        let sym = make_bool_sym ev ~arity:(List.length es) in
        let ctx_e = infer_exp (Some Bool) (Sym (sym, es)) in
        let ctx_p = infer p in
        Type_ctx.merge [ctx_e; ctx_p]

      | Out es :: p ->
        let ctx_s = List.map ~f:(infer_exp None) es in
        let ctx_p = infer p in
        Type_ctx.merge (ctx_p :: ctx_s)

      | (Comment _ | Yield) :: p -> infer p

      | [] -> Type_ctx.empty
    in
    infer p

  (** Returns only the context for formatter functions. Merge with user functions
      yourself.

      Assumes that the process is in the formatting-normal form, that is,
      every formatter application has the form let [x = f(x1, ..., xn)].
  *)
  let derive_unknown_types fun_types (ctx: Type_ctx.t) (p: iml) : Fun_type_ctx.t =
    let find_type v =
      match Type_ctx.maybe_find v ctx with
      | Some t -> t
      | None -> Type.Bitstring
    in
    let rec derive derived_fun_types = function
      | [] -> derived_fun_types
      | Let (VPat v, Sym (Fun _ as f, vs)) as s :: p
          when not (Fun_type_ctx.mem f fun_types) ->
        let ts =
          List.map vs ~f:(function
          | Var (v, Kind.Bitstring) -> find_type v
          | _ -> fail "formatting-normal form expected: %s" (Stmt.to_string s))
        in
        let derived_fun_types =
          Fun_type_ctx.add f (ts, find_type v) derived_fun_types
        in
        derive derived_fun_types p
      | Fun_test (Sym (Fun _ as f, vs)) as s :: p
          when not (Fun_type_ctx.mem f fun_types) ->
        let ts =
          List.map vs ~f:(function
          | Var (v, Kind.Bitstring) -> find_type v
          | _ -> fail "malformed test statement: %s" (Stmt.to_string s))
        in
        let derived_fun_types =
          Fun_type_ctx.add f (ts, Bool) derived_fun_types
        in
        derive derived_fun_types p
      | _ :: p -> derive derived_fun_types p
    in
    derive Fun_type_ctx.empty p

  let prove_type
      (facts : fact list)
      ((arg_types, res_type) : (bitstring, bitstring) Fun_type.t)
      (f : (bitstring, bitstring) Sym.t)
      (f_def : bterm)
      (args: bterm list) : bool =

    if List.length args <> List.length arg_types then
      fail "wrong number of arguments: %s(%s)" (Sym.to_string f) (E.dump_list args);

    let formal_args = mk_formal_args (List.length args) in
    let e_f = E.subst formal_args args f_def in

    (*
    debug ("typecheck: e_def = " ^ E.dump e_def);
    debug ("typecheck: context = " ^ dump_list ctx);
    *)

    let arg_facts = List.map2 ~f:E.in_type args arg_types in
    let res_fact = E.in_type e_f res_type in

    DEBUG "proving type %s" (Sym.cv_declaration f (arg_types, res_type));
    S.implies (arg_facts @ facts) [res_fact]

  let erase_type_annotations p =
    let rec erase : type a. a exp -> a exp = function
      | Annotation (Type_hint _, e) -> erase e
      | e -> E.descend {E.descend = erase} e
    in
    Iml.map {E.descend = erase} p

  let check
      (defs : bitstring Sym_defs.t)
      (fun_types : Fun_type_ctx.t)
      (ctx: Type_ctx.t)
      (facts: fact list)
      (p: iml) : iml =

    let typefacts ctx =
      Type_ctx.to_list ctx
      |> List.map ~f:(fun (v, t) -> E.in_type (Var (v, Type.kind t)) t)
    in

    let rec check_exp
        : type a. Type_ctx.t -> fact list -> a Type.t -> a exp -> a exp =
      fun ctx facts t' e ->
        match e with
        | Var (v, Kind.Bitstring) ->
          let t = Type_ctx.find v ctx in
          if not (S.implies
                    (facts @ typefacts ctx)
                    [E.in_type (Var (v, Type.kind t')) t'])
          then fail  "cannot prove type: %s: %s" v (Type.to_string t');
          cast t t' e

        | Sym (Fun _ as f, es) ->
          let fail f_type =
            fail "typecheck: cannot prove type %s" (Sym.cv_declaration f f_type)
          in
          let (ts, t) = Fun_type_ctx.find f fun_types in
          let es' = List.map2 ~f:(check_exp ctx facts) ts es in
          let e' = Sym (f, es') in
          let tt = Type.intersection t t' in
          begin match Type.kind t with
          | Kind.Int -> assert false
          | Kind.Bool ->
            if t <> t'
            then fail (ts, t')
            else e'
          | Kind.Bitstring ->
            begin match Sym_defs.maybe_find f defs with
            | Some def ->
              if not (prove_type (facts @ typefacts ctx) (ts, tt) f def es)
              then fail (ts, tt)
            | None ->
              if not (Type.subtype t t')
              then fail (ts, t')
            end;
            cast t t' e'
          end;

        (* Type annotations are only used in inference, and ignored in typechecking *)
        | Annotation (a, e) -> Annotation (a, check_exp ctx facts t' e)

        | e -> fail "check_exp: unexpected expression %s" (E.dump e)
    in

    let exp_type fun_types ctx e = Option.value_exn (exp_type fun_types ctx e) in

    let rec check ctx facts p =
    match p with
      | Let (VPat v, e) :: p ->
        let t =  exp_type fun_types ctx e in
        let e' = check_exp ctx facts t e in
        let p' = check (Type_ctx.add v t ctx) facts p in
        Let (VPat v, e') :: p'

      | Let (_, _) :: _ -> fail "check_types: let patterns not supported: %s" (Iml.to_string p)

      | Aux_test e :: p ->
        let p' = check ctx (facts @ [e]) p in
        Aux_test e :: p'

      | Fun_test e :: p ->
        let e = check_exp ctx facts Bool e in
        let p = check ctx facts p in
        Fun_test e :: p

      | Eq_test (e1, e2) :: p ->
        let t1 = exp_type fun_types ctx e1 in
        let t2 = exp_type fun_types ctx e2 in
        let tt = Type.union t1 t2 in
        (* Not adding a non-auxiliary test to facts *)
        let p' = check ctx facts p in
        Eq_test(cast t1 tt e1, cast t2 tt e2) :: p'

      | Assume e :: p ->
        Assume e :: check ctx (facts @ [e]) p

      | In vs :: p ->
        let ctx_v = Type_ctx.of_list (List.map ~f:(fun vs -> vs, Bitstring) vs) in
        let p' = check (Type_ctx.merge [ctx; ctx_v]) facts p in
        In vs :: p'

      | New (v, t) :: p ->
        (* Not checking whether the type is fixed, because of the types created by
           Apply_nondet *)
        let p' = check (Type_ctx.add v t ctx) facts p in
        New (v, t) :: p'
        (*
        begin match Type.strip_name t with
        | Fixed _ ->
          let p' = check (Type_ctx.add v t ctx) facts p in
          New (v, t) :: p'
        | _ -> fail "fixed type expected in new expression: %s" (Stmt.to_string (New (v, t)))
        end
        *)

      | Out es :: p ->
        let es' = List.map es ~f:(fun e ->
          check_exp ctx facts (exp_type fun_types ctx e) e)
        in
        let p' = check ctx facts p in
        Out es' :: p'

      | Event (ev, es) :: p ->
        let sym = make_bool_sym ev ~arity:(List.length es) in
        let (ts, _) = Fun_type_ctx.find sym fun_types in
        let es' = List.map2 ~f:(fun e t -> check_exp ctx facts t e) es ts in
        let p' = check ctx facts p in
        Event (ev, es') :: p'

      | Yield :: p -> Yield :: check ctx facts p

      | Comment s :: p -> Comment s :: check ctx facts p

      | [] -> []
    in
    erase_type_annotations (check ctx facts p)

  let check_robust_safety (concats : bitstring Sym_defs.t) (fun_types : Fun_type_ctx.t) =
    let safe f def =
      let (ts, t) = Fun_type_ctx.find f fun_types in
      let args = mk_formal_args (Sym.arity f) |> List.map ~f:E.var in
      if not (prove_type [] (ts, t) f def args && t <> Bitstringbot) then
        fail "function %s is not robustly safe" (Sym.cv_declaration f (ts, t));
    in
    Sym_defs.iter ~f:safe concats

  (* Give an error and perhaps a suggestion if a type is missing in a template. *)
  let check_missing_types
      (bitstring_defs : bitstring Sym_defs.t)
      (bool_defs : bool Sym_defs.t)
      ~template_types ~inferred_types p =
    let is_missing (type a) (kind : a Kind.t) (f : (bitstring, a) Sym.t) =
      if Fun_type_ctx.mem f template_types then false
      else match kind with
      | Kind.Bitstring -> not (Sym_defs.mem f bitstring_defs)
      | Kind.Bool -> not (Sym_defs.mem f bool_defs)
      | Kind.Int -> assert false
    in
    let rec check : type a. a exp -> unit = function
      | Sym (Fun _ as f, es) as e ->
        if is_missing (E.kind e) f
        then begin match Fun_type_ctx.maybe_find f inferred_types with
        | Some t ->
          fail "No type found for function %s, suggested type: %s"
            (Sym.to_string f) (Sym.cv_declaration f t);
        | None ->
          fail "No type found for function %s" (Sym.to_string f);
        end;
        List.iter ~f:check es
      | e -> E.iter_children {E.f = check} e
    in
    Fun_type_ctx.dump template_types;
    Iml.iter {E.f = check} (remove_auxiliary p)

  let test_cond_checking () =
    let t1 = Type.Named ("t", None) in
    let t2 = Type.Bitstring in
    let aux = Fun ("auxiliary", (1, Kind.Bool)) in
    let f = Fun ("auxiliary", (1, Kind.Bitstring)) in
    let cast = Cast (t1, t2) in
    let v = Var ("v", Kind.Bitstring) in
    let fun_types =
      Fun_type_ctx.empty
      |> Fun_type_ctx.add aux ([t2], Type.Bool)
      |> Fun_type_ctx.add f   ([t2], t1)
    in
    let var_types = Type_ctx.of_list
      [ "v", Type.Bitstring ]
    in
    let p = [Fun_test (Sym (aux, [Sym (f, [v])]))] in
    let p' = check (Sym_defs.empty ()) fun_types var_types [] p in
    let expect =
      [Fun_test (Sym (aux, [Sym (cast, [Sym (f, [v])])]))] in
    test_result ~expect p' Iml.to_string

  let test () =
    test_cond_checking ()
end


(*************************************************)
(** {1 XOR rewriting} *)
(*************************************************)

(* Make sure that XOR will be treated as cryptographic function. *)
(* CR-someday: this might be done on a per-case bases using a plugin. *)

let rewrite_xor p =

  let assumptions = ref [] in

  let rec rewrite : type a. a exp -> a exp = function
    | Sym (Op (BXor, ([t1; t2], t)), [e1; e2]) ->
      let e1 = rewrite e1 in
      let e2 = rewrite e2 in
      let e = Sym (Fun ("XOR", (2, Kind.Bitstring)), [e1; e2]) in
      let fact =
        E.implication
          [E.in_type e1 t1; E.in_type e2 t2]
          [E.in_type e t]
      in
      assumptions := Assume fact :: !assumptions;
      e
    | e -> E.descend {E.descend = rewrite} e
  in
  let rewrite s =
    let s = Stmt.descend {E.descend = rewrite} s in
    let result = !assumptions @ [s] in
    assumptions := [];
    result
  in
  List.concat_map ~f:rewrite p

(*************************************************)
(** {1 Crypto-arithmetic comparison rewriting} *)
(*************************************************)

(* Deal with DSA_verify(...) == 1

   We can't easily turn this into bitstring comparison because Val is not necessarily
   injective.
*)
let rewrite_crypto_arithmetic_comparisons p =
  let is_interesting = function
    | Var _ -> true
    | Sym (Fun _, _) -> true
    | _ -> false
  in
  let rewrite s =
    match s with
    | Aux_test (Sym (Int_cmp Cmp.Eq, [Val (e, _); Int n])) when is_interesting e ->
      (* Because we preserve the original test, we don't need to mention the conversion
         type. *)
      let f = Printf.sprintf "value_equal_%d" (Int64.to_int n) in
      [s; Fun_test (Sym (Fun (f, (1, Kind.Bool)), [e]))]
    | s -> [s]
  in
  List.concat_map ~f:rewrite p

(*************************************************)
(** {1 Error if IML contains undef *)
(*************************************************)

let error_if_undefs p =
  let rec error : type a. a exp -> unit = function
    | Sym (Undef _, _) -> fail "IML contains undef"
    | e -> E.iter_children {E.f = error} e
  in
  Iml.iter {E.f = error} p

(*************************************************)
(** {1 Let simplification} *)
(*************************************************)

let simplify_lets p =
  let rec simplify defs = function
    | Let (VPat v, Var (v', Kind.Bitstring)) :: p ->
      simplify defs (Iml.subst_v [v] [v'] p)
    | Let (VPat v, _) :: p when Iml.refcount v p = 0 -> simplify defs p
    | Let (VPat v, e) :: p ->
      begin match Option.try_with (fun () -> List.assoc e defs) with
      | Some v' ->
        simplify defs (Iml.subst_v [v] [v'] p)
      | None ->
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
   {[
    new var1: fixed_n;
    let var2 = var1 in
    let named_var = var2 in P
   ]}
  (where there is a name annotation on var2) to
   {[
     new named_var: fixed_n in P
   ]}
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

  let exp_name = function
    | Var (v, _) -> Some v
    | Annotation (Name name, _) -> Some name
    (* Don't rename variables inside annotations, since annotations will not be removed by
       simplify_lets. *)
    (* | Annotation (_, e) -> exp_name e *)
    | _ -> None
  in

  let rec collect_names_e : type a. a exp -> unit = function
    | Annotation (Name name, e) ->
      begin match exp_name e with
        (* Do not rename free variables *)
        | Some name' when not (List.mem name' ~set:free_vars) ->
          rename name' name
        | _ -> ()
      end;
      collect_names_e e
    | e ->
      E.iter_children {E.f = collect_names_e } e
  in

  let collect_names = function
    | Let (VPat v, e) ->
      begin match exp_name e with
        | Some name -> rename v name
        | _ -> ()
      end
    | _ -> ()
  in

  (* We do substitution without regard for capture *)
  let subst_v vs vs' = Iml.map {E.descend = fun e -> E.subst_v vs vs' e} in

  (* Rename variables according to collected names *)
  let rec rename_vars = function
    | Let (VPat v, e) :: p ->
      let v' = resolve v in
      Let (VPat v', e) :: rename_vars (subst_v [v] [v'] p)
    | New (v, t) :: p ->
      let v' = resolve v in
      New (v', t) :: rename_vars (subst_v [v] [v'] p)
    | In vs :: p ->
      let vs' = List.map ~f:resolve vs in
      In vs' :: rename_vars (subst_v vs vs' p)
    | s :: p -> s :: rename_vars p
    | [] -> []
  in

  let rec remove_name_annotations : type a. a exp -> a exp = function
    | Annotation (Name _, e) -> remove_name_annotations e
    | e -> E.descend {E.descend = remove_name_annotations} e
  in

  List.iter ~f:collect_names p;
  (* It is important that this comes second,
     to make sure annotation renamings override
     assignment renamings *)
  Iml.iter {E.f = collect_names_e} p;
  rename_vars p |> Iml.map {E.descend = remove_name_annotations} |> simplify_lets

(*************************************************)
(** {1 Normal Form} *)
(*************************************************)

let is_tag e = E.is_constant e

let sort_defs defs =
  let gt s s' =
    match s, s' with
      | Let (_, e), Let (VPat v, _) -> List.mem v ~set:(E.vars e)
      | _ -> false
  in
  List.topsort gt defs

let normal_form p =
  let rec normalize p =

    let defs = ref [] in

    let mk_var = function
      | Var (v, Kind.Bitstring) -> Var (v, Kind.Bitstring)
      | e ->
        let v = Var.fresh "" in
        defs := Let (VPat v, e) :: !defs;
        Var (v, Kind.Bitstring)
    in

    let is_length_of e_l e =
      match e_l with
      | BS (l, _) ->
        S.equal_int l (Len e)
      | e_l ->
        match Simplify.full_simplify (Len e) with
        | Val (e_l', _) ->
          S.equal_bitstring e_l e_l'
        | _ -> false
    in

    (* remove expressions that are themselves lengths of an expression that follows *)
    let rec remove_lens = function
      | e :: es ->
        if List.exists ~f:(fun e' -> is_length_of e e') es
        then remove_lens es
        else e :: remove_lens es
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
        | None ->
          e :: explicate_lens args es
        | Some width ->
          let itype = Int_type.create `Unsigned width in
          match
            List.find_and_remove args ~f:(fun e' ->
              S.equal_bitstring e (BS (Len e', itype)))
          with
          | None -> e :: explicate_lens args es
          | Some (e', args) ->
            BS (Len e', itype) :: explicate_lens args es
    in

    let rec extract_non_cryptographic : type a. a exp -> a exp = fun e ->
      match e, E.kind e with
      | e, Kind.Bitstring when E.is_cryptographic e ->
        mk_var (extract (e : bterm))
      | e, _ ->
        E.descend {E.descend = extract_non_cryptographic} e

    (* Variables for same expressions will later be unified by simplify_lets *)
    and extract_concat = function
      | e when is_tag e -> e
      | BS (Len e, itype) -> BS (Len (mk_var (extract e)), itype)
      | e -> mk_var (extract e)

    and extract_parser : type a. bterm -> bterm -> a exp -> a exp = fun v m e ->
      let descend e = extract_parser v m e in
      match e, E.kind e with
      | e, Kind.Bitstring when S.equal_bitstring m e -> v
      | e, Kind.Int when S.equal_int (Len m) e -> Len v
      | Sym (Int_op _, _), _             -> E.descend {E.descend} e
      | Sym (Op (Cast_to_int, _), _), _  -> E.descend {E.descend} e
      | Val _, _                         -> E.descend {E.descend} e
      | BS _, _                          -> E.descend {E.descend} e
      | Range _, _                       -> E.descend {E.descend} e
      | Int _, _                         -> E.descend {E.descend} e
      | e, _ -> fail "normal_form: unexpected parser subexpression %s" (E.dump e) (* mk_var (extract e) *)

    and extract_fun = function
      | Sym (Fun _ as f, es)  ->
        Sym (f, List.map ~f:extract_fun (es : bterm list))
      | e -> mk_var (extract e)

    and extract (e : bterm) =
      match e with
      | Concat es ->
        let args = remove_lens (List.filter ~f:(non is_tag) es) in
        let es = explicate_lens args es in
        DEBUG "extract concat: args = %s" (E.list_to_string args);
        DEBUG "extract concat: es = %s" (E.list_to_string es);
        Concat (List.map ~f:extract_concat es)

      | Range (Range _, _, _) ->
        fail "extract_parsers: nested ranges not supported: %s" (E.dump e)

      | Range (m, _, _) ->
        let v = mk_var (extract m) in
        extract_parser v m e

      | Var (v, t) -> Var (v, t)

      | Sym (Fun _, _) -> extract_fun e

      | Annotation (a, e) -> Annotation (a, mk_var (extract e))

      | e when not (E.is_cryptographic e) -> extract_non_cryptographic e

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
        S.add_fact (E.eq_bitstring [Var (v, Kind.Bitstring); e]);
        let e = extract e in
        sort_defs !defs @ (Let (VPat v, e) :: normalize p)
      | Let _ :: _ ->
        fail "normal_form: impossible: let patterns unexpected"
      | In vs as s :: p ->
        List.iter ~f:(fun v -> S.add_fact (E.is_defined (Var (v, Kind.Bitstring)))) vs;
        s :: normalize p
      | New (v, t) as s :: p ->
        S.add_fact (E.in_type (Var (v, Kind.Bitstring)) t);
        s :: normalize p
      | (Fun_test _ | Eq_test _ | Out _ | Event _ | Yield | Comment _ ) as s :: p ->
        let move_out_bitstring (e : bterm) =
          match e with
          | Concat _ | Range _ | Annotation _ -> mk_var (extract e)
          | Var _ -> extract e
          | Sym (Fun _, _) -> extract e
          | e when not (E.is_cryptographic e) -> mk_var (extract e)
          | e ->
            fail "Normal form: impossible: %s" (E.to_string e)
        in
        let move_out (type a) (e : a exp) : a exp =
          match E.kind e with
          | Kind.Bitstring -> move_out_bitstring e
          | Kind.Int -> fail "Normal form: impossible: %s" (E.to_string e)
          | Kind.Bool ->
            match e with
            | Sym (Fun (f, t), es) ->
              Sym (Fun (f, t), List.map ~f:extract_fun es)
            | e -> fail "Normal form: impossible: %s" (E.to_string e)
        in
        let s = Stmt.descend {E.descend = move_out} s in
        sort_defs !defs @ (s :: normalize p)
      | [] -> []
  in
  push_debug "normal_form";
  S.reset_facts ();
  let p = normalize p in
  S.reset_facts ();
  pop_debug "normal_form";
  simplify_lets p

let test_normal_form_concat () =
  let var v = Var (v, Kind.Bitstring) in
  let itype = Int_type.create `Unsigned 8 in
  let l1 = Range (var "msg", Int 4L, Int 8L) in
  let e1 = Range (var "msg", Int 12L, Val (l1, itype)) in
  let t = Named ("nonce", Some (Fixed 20)) in
  let e = Concat [E.string "msg"; l1; BS (Int 20L, itype);
                  Annotation (Type_hint t, e1); var "nonce"; var "host"]
  in
  let p = [ New ("nonce", t)
          ; Assume (E.is_defined e)
          ; Out [e] ]
  in
  let p' = [ New ("nonce", t)
           ; Assume (E.is_defined e)
           ; Let (VPat "var3", e1)
           ; Let (VPat "var4", Annotation (Type_hint t, var "var3"))
           ; Let (VPat "var5", Concat [ E.string "msg"
                                      ; BS (Len (var "var4"), itype)
                                      ; BS (Len (var "nonce"), itype)
                                      ; var "var4"; var "nonce"; var "host"])
           ; Out [var "var5"] ]
  in
  test_result ~expect:p' (normal_form p) Iml.to_string;
  S.reset_facts ()

let test_normal_form_fun () =
  let f = make_sym "f" ~arity:1 in
  let var v = Var (v, Kind.Bitstring) in
  let e_c = Concat [var "msg1"; var "msg2"] in
  let e = Sym (f, [e_c]) in
  let p = [ Assume (E.is_defined e); Out [e] ] in
  let p' = [ Assume (E.is_defined e)
           ; Let (VPat "var1", e_c)
           ; Out [Sym (f, [var "var1"])] ]
  in
  test_result ~expect:p' (normal_form p) Iml.to_string;
  S.reset_facts ()

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

(* CR-soon: this isn't an int expression, so rename to something less suggestive
   of that. *)
let extract_arithmetic p : iml * bitstring Sym_defs.t =

  let defs = ref [] in

  let extract = function
    | Let (v, e) when not (E.is_cryptographic e) ->
      let vs, def = extract_def e in
      let f = make_sym (Var.fresh "arithmetic") ~arity:(List.length vs) in
      defs := (f, def) :: !defs;
      let args = List.map ~f:E.var vs in
      Let (v, Sym (f, args))
    | s -> s
  in
  let p = List.map ~f:extract p in
  p, Sym_defs.of_list !defs

let is_injective_arithmetic = function
  | Sym (Op (Op.Cast_to_int, ([Bs_int t1], Bs_int t2)), [Var _]) ->
    Int_type.signedness t1 = Int_type.signedness t2
    && Int_type.width t1 <= Int_type.width t2
  | _ -> false

(*************************************************)
(** {1 Concatenations} *)
(*************************************************)

(**
   If [use_type_info], we don't require lengths for arguments of fixed-length types.
*)
let is_injective_concat fun_types sym def =
  (*
    DEBUG "is_injective_concat: %s" (E.to_string def);
  *)
  let args_that_should_have_lens ts es =
    let rec collect ts es =
      match ts, es with
      | t :: ts, (Var _) :: es when Type.has_fixed_length t ->
        collect ts es
      | _ :: ts, (Var _ as v) :: es ->
        v :: collect ts es
      | ts, _ :: es ->
        collect ts es
      | [], [] -> []
      | _ -> assert false
    in
    collect ts es
  in
  match def with
  | Concat es ->
    let (ts, _) = Fun_type_ctx.find sym fun_types in
    let args = args_that_should_have_lens ts es in
    let args_with_lens =
      List.filter_map ~f:(function BS (Len v, _) -> Some v | _ -> None) es
    in
    let args_without_lens = List.diff args args_with_lens in
      (*
        DEBUG "args: %s" (E.list_to_string args);
        DEBUG "lens: %s" (E.list_to_string lens);
        DEBUG "args_without_lens: %s" (E.list_to_string args_without_lens);
      *)
    List.length args_without_lens <= 1
  | _ -> false

let extract_concats p: iml * bitstring Sym_defs.t =

  let concats = ref [] in

  (*
    Check whether the concat definition only consists of formal arguments
    (no lengths or tags).
  *)
  let rec is_trivial_concat : bterm list -> bool = function
    | Var _ :: es -> is_trivial_concat es
    | [] -> true
    | _ :: _ -> false
  in

  let extract = function
    | Let (v, (Concat es as e)) ->
      DEBUG "extract, e = %s" (E.dump (Concat es));
      let vs, def = extract_def e in
      let f_c = new_concat_sym ~arity:(List.length vs) in
      concats := (f_c, def) :: !concats;
      DEBUG "extract, e_new = %s" (E.dump def);
      begin match def with
        | Concat es when is_trivial_concat es ->
          fail
            "The concatenation does not contain argument lengths or tags. This may lead to non-termination. %s"
            (E.dump def)
        | _ -> ()
      end;
      let args = List.map ~f:E.var vs in
      Let (v, Sym (f_c, args))
    | s -> s
  in
  let p = List.map ~f:extract p in
  p, Sym_defs.of_list !concats

let warn_on_non_injective_concats fun_types concats =
  Sym_defs.iter concats ~f:(fun f_c def ->
    if not (is_injective_concat fun_types f_c def)
    then warn "Concat not injective: %s" (Sym_defs.show_fun f_c def))

(*************************************************)
(** {1 Facts} *)
(*************************************************)

module Aux_fact = struct
  type fun_decl = (bitstring, bitstring) Fun_type.t * bfun

  type t =
  | Disjoint of fun_decl * fun_decl
  | Equal of fun_decl * fun_decl

  (* CR: if two aligned arguments are of different types, then generate no fact straight
     away, to avoid warnings. *)
  let fun_fact fun_types (s, e) (s', e') =
    let rec facts n ts ts' =
      match ts, ts' with
      | t :: ts, t' :: ts' ->
        if t = t'
        then
          let v = Var (mk_arg n, Kind.Bitstring) in
          E.in_type v t :: facts (n + 1) ts ts'
        else facts (n + 1) ts ts'
      | [], _ | _, [] -> []
    in
    let ts, _  as t  = Fun_type_ctx.find s  fun_types in
    let ts', _ as t' = Fun_type_ctx.find s' fun_types in
    let facts = facts 0 ts ts' in
    let rec scan es es' =
      DEBUG "encoder_fact: matching %s and %s" (E.dump_list es) (E.dump_list es');
      match es, es' with
      | e :: es, e' :: es' when S.equal_bitstring ~facts e e' -> scan es es'
      | e :: _, e' :: _
        when is_tag e && is_tag e' && S.equal_int ~facts (Len e) (Len e') ->
        Some (Disjoint ((t, s), (t', s')))
      | [], [] -> Some (Equal ((t, s), (t', s')))
      | _ -> None
    in
    match e, e' with
    | Concat es, Concat es' -> scan es es'
    | e, e' ->
      if e = e' then Some (Equal ((t, s), (t', s'))) else None

  let rec fun_facts fun_types (cs : (bfun * bitstring Sym_defs.def) list) : t list =
    match cs with
    | c :: cs ->
      List.filter_map ~f:(fun_fact fun_types c) cs @ fun_facts fun_types cs
    | [] -> []

  let is_valid = function
    | Equal ((t1, _), (t2, _)) -> t1 = t2
    | Disjoint (((_, t1), _), ((_, t2), _)) -> t1 = t2

  let fun_facts fun_types cs =
    List.filter (fun_facts fun_types cs) ~f:is_valid
end

module CV_fact = struct
  type t = Forall of (var * bitstring Type.t) list * fact

  let make fun_types (e : fact) : t =
    let vs = E.vars e in
    let ts = Typing.infer_exp fun_types (Some Bool) e in
    match List.diff vs (Type_ctx.keys ts) with
    | [] -> Forall (Type_ctx.to_list ts, e)
    | vs ->
      let vs = String.concat vs ~sep:", " in
      fail "CV_fact.make: could not infer types for %s in %s"
        vs (E.to_string e)
end

(*************************************************)
(** {1 Extracting Parsers} *)
(*************************************************)

let extract_parsers p =
  let parsers = ref [] in
  let extract = function
    | Let (v_pat, (Range (Var (v, _), _, _) as e)) ->
      DEBUG "adding parser for the expression %s" (E.to_string e);
      let vs, def = extract_def e in
      if vs <> [v] then fail "extract_parsers: impossible";
      let f_p = new_parser_sym () in
      (*
      debug ("adding parser, " ^ Sym.to_string f_p ^"(x) = " ^ E.dump def);
      *)
      parsers := (f_p, def) :: !parsers;
      let args = List.map ~f:E.var vs in
      Let (v_pat, Sym (f_p, args))
    | s -> s
  in
  let p = List.map ~f:extract p in
  p, Sym_defs.of_list !parsers


(*************************************************)
(** {1 Extracting Auxiliary Test Conditions} *)
(*************************************************)

let extract_auxiliary p : iml * bool Sym_defs.t =

  let arities = ref [] in

  let rec extract = function
    | Aux_test e :: p ->
      let vs, def = extract_def e in
      let f = make_bool_sym (Var.fresh "auxiliary") ~arity:(List.length vs) in
      arities := (f, def) :: !arities;
      let args = List.map ~f:E.var vs in
      Fun_test (Sym (f, args)) :: Aux_test e :: extract p
    | s :: p -> s :: extract p
    | [] -> []
  in
  let p = extract p in
  p, Sym_defs.of_list !arities

(*************************************************)
(** {1 Removing Redundant Test Conditions} *)
(*************************************************)

let remove_redundant_auxiliary defs var_types p =
  let rec remove_casts : type a. a exp -> a exp = function
    | Sym (Cast _, [e]) -> remove_casts e
    | e -> E.descend {descend = remove_casts } e
  in
  let assume_var_types () =
    Type_ctx.to_list var_types
    |> List.iter ~f:(fun (v, t) ->
      S.add_fact (E.in_type (Var (v, Kind.Bitstring)) t))
  in
  let rec remove = function
    | [] -> []
    | stmt :: p ->
      match stmt with
      | Fun_test fact ->
        let fact = remove_casts fact |> Sym_defs.expand_top_def defs in
        if S.is_true fact
        then remove p else stmt :: remove p
      | stmt ->
        List.iter (Stmt.fact stmt) ~f:S.add_fact;
        stmt :: remove p
  in
  S.reset_facts ();
  assume_var_types ();
  remove p

(*************************************************)
(** {1 Parsing Rules} *)
(*************************************************)

let compute_parsing_rules
    fun_types
    (parsers : bitstring Sym_defs.t)
    (concats : bitstring Sym_defs.t) : parsing_eq list =

  let parsing_eqs = ref [] in

  let check_type nargs p c e =
    let (pts, pt) = Fun_type_ctx.find p fun_types in
    let (cts, ct) = Fun_type_ctx.find c fun_types in
    let result =
      if pts <> [ct] then false
      else begin
        let args = mk_formal_args nargs |> List.map ~f:E.var in
        List.any (List.map2 ~f:(fun arg t -> arg = e && t = pt) args cts)
      end
    in
    begin if not result then match e with
    | Var _ ->
      info ("derived equation %s(%s(...)) = %s but the types don't match,\n"
             ^^ "  %s: %s, and %s: %s")
        (Sym.to_string p) (Sym.to_string c) (E.to_string e)
        (Sym.to_string c) (Fun_type.to_string (cts, ct))
        (Sym.to_string p) (Fun_type.to_string (pts, pt))
    | _ -> ()
    end;
    result
  in

  let apply_parser f_p parser_def f_c concat_def =
    let arg = mk_arg 0 in
    let e = E.subst [arg] [concat_def] parser_def in
    DEBUG "apply_parser: e after subst arg = %s" (E.dump e);
    let e' = Simplify.full_simplify e in
    DEBUG "apply_parser %s to %s: \n  %s \n  ~> %s  \n" (Sym.to_string f_p) (Sym.to_string f_c)
                                                       (E.dump e) (E.dump e');
    if check_type (Sym.arity f_c) f_p f_c e'
    then [((f_p, f_c), e')]
    else []
  in

  let compute_rules_for_concat f_c concat_def =
    let parsers = Sym_defs.to_list parsers in
    let (ts, _) = Fun_type_ctx.find f_c fun_types in
    let arg_facts =
      List.mapi ts ~f:(fun i t ->
        E.in_type (Var (mk_arg i, Kind.Bitstring)) t)
    in
    List.iter arg_facts ~f:S.add_fact;
    (* S.add_fact (E.is_defined concat_def); *)

    (* We expect some conditions to fail when the parser doesn't match. *)
    S.warn_on_failed_conditions false;
    let new_eqs =
      List.concat_map ~f:(fun (f_p, parser_def) ->
        apply_parser f_p parser_def f_c concat_def)
        parsers
    in
    S.warn_on_failed_conditions true;
    S.reset_facts ();
    parsing_eqs := new_eqs @ !parsing_eqs;
  in

  let check_parser_is_matched p _ =
    if List.exists !parsing_eqs ~f:(fun ((p', _), _) -> p = p') then ()
    (* A corresponding warning for encoders would not be good because sometimes we send
       tag|msg together, but receive tag and msg separately. *)
    else warn "No parsing equation for %s" (Sym.to_string p)
  in

  Sym_defs.iter ~f:compute_rules_for_concat concats;
  Sym_defs.iter ~f:check_parser_is_matched parsers;
  !parsing_eqs

let show_parsing_eq ?fun_types (((p, c), e): parsing_eq) =
  let arity = Sym.arity c in
  let args = mk_formal_args arity in
  let header =
    match fun_types with
    | Some fun_types ->
      let ts, _ = Fun_type_ctx.find c fun_types in
      List.map2 ~f:(fun arg t -> arg ^ ": " ^ Type.to_string t) args ts
      |> String.concat ~sep:", "
      |> Printf.sprintf "forall %s;\n"
    | None -> ""
  in
  Printf.sprintf "%s%s(%s(%s)) = %s"
    header
    (Sym.to_string p)
    (Sym.to_string c)
    (String.concat ~sep:", " args)
    (E.to_string e)

(*************************************************)
(** {1 Parsing Safety} *)
(*************************************************)

let well_formed e_c =
  let args = List.filter ~f:(function Var _         -> true | _ -> false) e_c in
  let lens = List.filter ~f:(function BS (Len _, _) -> true | _ -> false) e_c in
  (* DEBUG "well_formed: %s, args = %s, lens = %s"
     (E.list_to_string e_c) (E.list_to_string args) (E.list_to_string lens); *)
  if not (List.distinct args) || not (List.distinct lens) then false
  else
    let args_with_lens =
      List.map lens ~f:(function BS (Len v, _) -> v | _ -> fail "well_formed: impossible")
    in
    (* DEBUG "well_formed: args_with_lens = %s" (E.list_to_string args_with_lens); *)
    match List.multidiff (=) args args_with_lens with
      | [e] -> e = List.last e_c
      | _ -> false

let rec mk_parsers ls ps es e_c =
  let open Sym.Arith in
  let x = Var (mk_arg 0, Kind.Bitstring) in
  match e_c with
    | e_i :: e_c ->
      let l =
        match e_i, e_c with
          | _, [] ->
            Sym (Int_op Minus, [Len x; Simplify.sum ls])
          | Var _ as v, _ ->
            (* DEBUG "looking for %s in %s" (E.dump v) (E.dump_list es); *)
            (* Need comparison in this order as es will contain lengths of lengths *)
            List.combine es ps
            |> List.first_some ~f:(function
                | (BS (Len v', itype), p) when v = v' -> Some (Val (p, itype))
                | _ -> None)
            |> Option.value_exn
          | BS (_, itype), _ ->
            E.int (Int_type.width itype)
          | e_i, _ ->
            match S.eval (Len e_i) with
            | Some n -> E.int n
            | None -> fail "mk_parsers: Cannot determine width of %s" (E.to_string e_i)
      in
      let p = Range (x, Simplify.sum ls, l) in
      mk_parsers (ls @ [l]) (ps @ [p]) (es @ [e_i]) e_c

    | [] -> ps

let rec tag_facts ps e_c =
  match ps, e_c with
    | _ :: ps, (BS (Len _, _) | Var _) :: e_c ->
      tag_facts ps e_c
    | p :: ps, e_t :: e_c ->
      E.eq_bitstring [p; e_t] :: tag_facts ps e_c
    | [], [] -> []
    | _ -> failwith "tag_facts: impossible"


let inrange facts e c_def =
  let x = mk_arg 0 in
  match c_def with
  | Concat e_c when well_formed e_c ->

    push_debug "inrange";

    let ps = mk_parsers [] [] [] e_c in
    DEBUG "inrange: parsers: %s\n" (E.list_to_string ps);
    let fields = List.map ~f:E.is_defined ps in
    let tags = tag_facts ps e_c in

    let parse_facts = List.map ~f:(E.subst [x] [e]) (fields @ tags) in

    pop_debug "inrange";

    S.implies facts parse_facts

  | _ -> false

let check_concat_safety fun_types facts e c c_def =
  DEBUG "Checking parsing safety of %s(...) = %s" (Sym.to_string c) (E.to_string e);
  let result = is_injective_concat fun_types c c_def && inrange facts e c_def in
  DEBUG "Result = %b" result;
  result

let match_concat fun_types parsing_eqs facts p e (c, c_def) =
  match maybe_assoc (p, c) parsing_eqs with
  | Some (Var (v, Kind.Bitstring)) ->
    DEBUG "Found parsing equation for %s(%s)" (Sym.to_string p) (Sym.to_string c);
    if not (check_concat_safety fun_types facts e c c_def)
    then None
    else
      let vs = mk_formal_args (Sym.arity c) in
      Some (c, List.find_index_exn ((=) v) vs)
  | _ ->
    DEBUG "Found no parsing equation for %s(%s)" (Sym.to_string p) (Sym.to_string c);
    None

let safe_parse fun_types (concats : bitstring Sym_defs.t) parsing_eqs facts f_p e =
  DEBUG "Checking parsing safety for %s(%s)" (Sym.to_string f_p) (E.to_string e);
  let result =
    List.filter_map
      ~f:(match_concat fun_types parsing_eqs facts f_p e)
      (Sym_defs.to_list concats)
  in
  match result with
  | [] ->
    DEBUG "Parsing %s(%s) is not safe" (Sym.to_string f_p) (E.to_string e);
    None
  | [c, i] ->
    DEBUG "%s(%s) safely parses %s at position %d"
      (Sym.to_string f_p) (E.to_string e) (Sym.to_string c) i;
    Some (c, i)
  | (c, i) :: _ :: _ as cs ->
    let cs =
      List.map cs ~f:(fun (c, i) ->
        Printf.sprintf "%s at position %d" (Sym.to_string c) i)
      |> String.concat ~sep:", "
    in
    warn "Several safe parsing candidates for %s: %s, taking first"
      (Sym.to_string f_p) cs;
    Some (c, i)

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
    | _ :: p -> remove p
    | [] -> []
  in

  List.rev (remove (List.rev p))

(*************************************************)
(** {1 Cleanup} *)
(*************************************************)

(**
  Leave only basic concats. Also remove unused concats (those turned into constants).
*)
let cleanup_defs p (defs : bitstring Sym_defs.t) : bitstring Sym_defs.t =
  let contains_sym c s =
    Stmt.exists_child {E.f = fun e -> E.contains_sym c e} s
  in
  Sym_defs.filter ~f:(fun s _ -> List.exists ~f:(contains_sym s) p) defs


let cleanup_parsing_eqs p (eqs: parsing_eq list): parsing_eq list =
  let contains_sym c s =
    Stmt.exists_child {E.f = fun e -> E.contains_sym c e} s
  in
  List.filter ~f:(fun ((f_p, _), _) -> List.exists ~f:(contains_sym f_p) p) eqs

(*************************************************)
(** {1 Testing} *)
(*************************************************)

let test () =
  push_debug "Transform.test";
  Typing.test ();
  Var.reset_fresh ();
  test_normal_form_concat ();
  Var.reset_fresh ();
  test_normal_form_fun ();
  pop_debug "Transform.test"

(* 1300 lines *)
