open Common

open Iml
open Iml.Type
open Iml.Sym
open Iml.Exp
open Iml.Pat
open Iml.Stmt

module E = Iml.Exp
module S = Solver

open Transform

open Printf

type cvfact = CV_fact.t

module Template: sig
  type t

  val crypto: t -> string list
  val crypto2: t -> string list
  val query: t -> string list
  val envp: t -> string list
  val model: t -> string list

  val read_file: cv_lib_name:string -> name:string -> t

  val var_types : t -> Type_ctx.t
  val fun_types : t -> Fun_type_ctx.t

  val is_defined : t -> (bitstring, _) Sym.t -> bool
end = struct

  module CV = Cryptoverif

  open CV.Types
  open CV.Syntax
  open CV.Stringmap

  type t = {
    crypto: string list;
    (** Printed after the automatically generated facts *)
    crypto2: string list;
    query : string list;
    envp: string list;
    (**
      This part is dropped.
    *)
    model: string list;
    var_types : Type_ctx.t;
    fun_types : Fun_type_ctx.t }

  let crypto t = t.crypto
  let crypto2 t = t.crypto2
  let query t = t.query
  let envp t = t.envp
  let model t = t.model
  let var_types t = t.var_types
  let fun_types t = t.fun_types

  let collect_types env q =

    let types = ref [] in
    let fun_types = ref Fun_type_ctx.empty in

    let add_var_type (v : string) (t : typet) =
      match Option.try_with (fun () ->
        Type.of_string_bitstring t.tname)
      with
      | None ->
        info ("add_var_type: ignoring variabe %s"
              ^^ " because it has a non-bitstring type.") v
      | Some t ->
        types := (v, t) :: !types
    in

    let add_fun_type (f : string) ((ts, t) : typet list * typet) =
      match Option.try_with (fun () ->
        List.map ts ~f:(fun t -> Type.of_string_bitstring t.tname))
      with
      | None ->
        info ("add_fun_type: ignoring function %s"
              ^^ " because it contains a non-bitstring argument type.") f
      | Some ts ->
        let Type.Any t = Type.of_string t.tname in
        let kind = Type.kind t in
        let sym = Sym.Fun (f, (List.length ts, kind)) in
        fun_types := Fun_type_ctx.add sym (ts, t) !fun_types
    in

    let collect_env_types env =
      let do_entry : string -> env_entry -> unit = fun _ -> function
        | EFunc f ->
          (* Constants are encoded as functions with no arguments, but we want to treat
             them as variables in our typechecking. This currently forces us to ignore
             variables false and true, which hopefully will not become a problem. It
             should be easy to treat constants as functions though if that ever becomes
             necessary.  *)
          begin match f.f_type with
          | ([], t) -> add_var_type f.f_name t
          | t       -> add_fun_type f.f_name t
          end
        | EEvent f ->
          (* for some reason it adds an extra bitstring parameter in front of the ones I
             define *)
          let (atypes, rtype) = f.f_type in
          add_fun_type f.f_name (List.tl atypes, rtype)
        | EVar b ->
          add_var_type b.sname b.btype
        | _ -> ()
      in
      StringMap.iter do_entry env
    in

    let rec collect_input_process_types : inputprocess -> unit = fun q ->
      let rec collect_pattern : pattern -> unit = function
        | PatVar b ->
          add_var_type b.sname b.btype
        | PatTuple (_, pats) -> List.iter ~f:collect_pattern pats
        | PatEqual _ -> ()
      in
      match q.i_desc with
      | Nil -> ()
      | Par (q, q') -> collect_input_process_types q; collect_input_process_types q'
      | Repl (_, q) -> collect_input_process_types q
      | Input (_, pat, q) -> collect_pattern pat; collect_output_process_types q

    and collect_output_process_types : process -> unit = fun p ->
      match p.p_desc with
      | Yield -> ()
      | Restr (b, p) ->
        add_var_type b.sname b.btype;
        collect_output_process_types p
      | Test (_, p, p') -> collect_output_process_types p; collect_output_process_types p'
      | Find _ -> fail "collect_types: unexpected find construct"
      | Output (_, _, q) -> collect_input_process_types q
      | Let (pat, _, p, p') ->
        collect_pattern_types pat;
        collect_output_process_types p; collect_output_process_types p'
      | EventP (_, p) -> collect_output_process_types p

    and collect_pattern_types: pattern -> unit = function
      | PatVar b ->
        add_var_type b.sname b.btype
      | PatTuple (_, pats) -> List.iter ~f:collect_pattern_types pats
      | PatEqual _ -> ()
    in

    collect_env_types env;
    collect_input_process_types q;
    Type_ctx.of_list !types, !fun_types


  let read_file ~cv_lib_name ~name =

    let crypto = ref [] in
    let crypto2 = ref [] in
    let query = ref [] in
    let envp = ref [] in
    let model = ref [] in

    let rec split_template: string list ref -> string list -> unit = fun dest -> function
      | l1 :: l2 :: ls' when String.trim l2 = "<Environment>" -> split_template envp (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when String.trim l2 = "<Query>" -> split_template query (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when String.trim l2 = "<Model>" -> split_template model (((l1 ^ "\n" ^ l2) :: ls'))
      | _ :: l2 :: _ when String.trim l2 = "<Type hints>" ->
        failwith "<Type hints> are deprecated"
      | l1 :: l2 :: ls' when String.trim l2 = "<Crypto2>" -> split_template crypto2 (((l1 ^ "\n" ^ l2) :: ls'))
      | l :: ls'  -> dest := !dest @ [l]; split_template dest ls'
      | [] -> ()
    in

    let c = open_in name in
    split_template crypto (Common.read_file c);
    Cryptoverif.Settings.lib_name := cv_lib_name;
    let (_, _, _, _, _, _, q) = read_file name in
    let var_types, fun_types = collect_types !CV.Stringmap.env q in
    { crypto = !crypto; crypto2 = !crypto2; query = !query; envp = !envp; model = !model;
      var_types; fun_types }

  let is_defined t sym =
    Fun_type_ctx.mem sym t.fun_types
end

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
    (parsers : bitstring Sym_defs.t)
    (concats : bitstring Sym_defs.t)
    parsing_eqs facts p =

  let rec do_match facts = function
    | (Let (VPat v, Sym (Fun (_, (_, Kind.Bitstring)) as f_p, [e]))) as s :: p
        when Sym_defs.mem f_p parsers ->
      begin match safe_parse concats parsing_eqs facts f_p e with
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


let rec merge_patterns p =

  let merge vpat vpat' =
    match vpat, vpat' with
      | VPat v, _ | _, VPat v  -> VPat v
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

  let rec collect_pattern f pat e p =
    match p with
    | Let (FPat (f', pat'), e') :: p when f = f' && e = e' ->
      let pat = merge_pattern pat pat' in
      let vs, vs' = List.split (match_vars pat pat') in
      let p = Iml.subst vs vs' p in
      collect_pattern f pat e p

    | s :: p ->
      let p, pat = collect_pattern f pat e p in
      s :: p, pat

    | [] -> [], pat
  in

  match p with
    | Let (FPat (f, pat), e) :: p ->
      let p, pat = collect_pattern f pat e p in
      Let (FPat (f, pat), e) :: merge_patterns p

    | s :: p -> s :: merge_patterns p

    | [] -> []

(*************************************************)
(** {1 Regularity Properties} *)
(*************************************************)

let zero_fun_sym t =
  make_sym ("Z" ^ Type.to_string t) ~arity:1
let zero_fun_prime_sym t =
  make_sym ("Z" ^ Type.to_string t ^ "_prime") ~arity:1
let zero_sym t =
  make_const ("zero_" ^ Type.to_string t)

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
    (fun_types: Fun_type_ctx.t) : cvfact list * bitstring Sym_defs.t * Fun_type_ctx.t =

  (* Types for which we need to generate ZT, ZT', and possibly Zero_t *)
  let zts : bitstring Type.t list ref = ref [] in

  let zero_fun t =
    zts := t :: !zts;
    zero_fun_sym t
  in

  (* Assume that zero_fun will be called for all of these, so no need to add to zts. *)
  let zero_fun_prime t = zero_fun_prime_sym t in

  let zero_of e t = Sym (zero_fun t, [e]) in

  (* Suitable for generating sym_defs and Fun_type_ctx.t *)
  let z_fun_info t =
    let zt = zero_fun_sym t in
    let zt' = zero_fun_prime_sym t in
    let zero_t = zero_sym t in
    [(zt,  Unknown Kind.Bitstring), (zt,  ([t], t));
     (zt', Unknown Kind.Bitstring), (zt', ([t], t));
     (zero_t, Unknown Kind.Bitstring), (zero_t, ([], t))]
  in

  let concat_fact c =
    let ts, t = Fun_type_ctx.find c fun_types in
    let args = mk_formal_args (Sym.arity c) |> List.map ~f:E.var in
    let zt = zero_fun t in
    let zt' = zero_fun_prime t in
    S.eq_bitstring [Sym (zt, [Sym (c, args)]);
                    Sym (zt', [Sym (c, List.map2 ~f:zero_of args ts)])]
  in

  let cast_fact (t1, t2) =
    let sym = Cast (t1, t2) in
    let x = Var ("x", Kind.Bitstring) in
    let zt2 = zero_fun t2 in
    let zt2' = zero_fun_prime t2 in
    S.eq_bitstring [Sym (zt2,  [Sym (sym, [x])]);
                    Sym (zt2', [Sym (sym, [zero_of x t1])])]
  in

  let const_fact t =
    let zt = zero_fun t in
    let zero_t = Sym (zero_sym t, []) in
    let x = Var ("x", Kind.Bitstring) in
    S.eq_bitstring [Sym (zt, [x]); zero_t]
  in

  (*
    Remove information for symbols that are already present in the template
    (such as the zero function in the definition of the encryption).
  *)
  let cleanup bindings =
    List.filter ~f:(fun (sym, _) -> not (Fun_type_ctx.mem sym fun_types)) bindings
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
  let z_defs, z_types = List.concat_map ~f:z_fun_info (List.dedup !zts) |> List.split in
  let z_defs = cleanup z_defs |> Sym_defs.of_list in
  let z_types = cleanup z_types |> Fun_type_ctx.of_list in
  let facts =
    List.map
      (concat_facts @ cast_facts @ const_facts)
      ~f:(CV_fact.make (Fun_type_ctx.disjoint_union [fun_types; z_types]))
  in
  facts, z_defs, z_types

(********************************************************)
(** {1 Auxiliary Test Properties} *)
(********************************************************)

let prime = function
  | Fun (s, n) -> Fun (s ^ "_prime", n)
  | sym -> fail "auxiliary_facts: impossible auxiliary symbol: %s" (Sym.to_string sym)

let add_auxiliary_primed auxiliary fun_types =
  let auxiliary_primed =
    Sym_defs.to_list auxiliary
    |> List.map ~f:(fun (sym, def) -> (prime sym, def))
    |> Sym_defs.of_list
  in
  let types_primed =
    Sym_defs.to_list auxiliary
    |> List.map ~f:(fun (sym, _) -> (prime sym, Fun_type_ctx.find sym fun_types))
    |> Fun_type_ctx.of_list
  in
  Sym_defs.disjoint_union [auxiliary; auxiliary_primed],
  Fun_type_ctx.disjoint_union [fun_types; types_primed]

(*
  There are two ways to check
    (len(x) = len(y)) => (def[x/arg] = def[y/arg]).

  The first way is to do length substitutions and then check syntactic equality.
  One needs to expand lengths because of things like
    !(cast_to_int[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + cast_to_int[false,4,false,8](len55)))

  The other way is to use the solver directly, but then you need to show overflow safety as well.
  When formalising, you need to replace auxiliary facts by hardened facts that check overflow safety.

  The second option is conceptually simpler, but less efficient.
  Another problem with the second option is that it is tricky to tell the solver to assume overflow
  safety for an expression. One cannot just extract the overflow safety fact, because that itself
  may not be overflow safe. For these reasons I'm using the first option now.
*)
let auxiliary_facts
    (concats : bitstring Sym_defs.t)
    (auxiliary : bool Sym_defs.t)
    (fun_types : Fun_type_ctx.t) : cvfact list =

  (* facts for a single auxiliary test *)
  let facts sym def arg_types =

    let num_args = List.length arg_types in

    let zero_of v t = Sym (zero_fun_sym t, [Var (v, Kind.Bitstring)]) in

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
      debug "can_erase: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
      def_x = def_y
    in

    let concat_pairs arg =
      let pair c =
        match Fun_type_ctx.maybe_find c fun_types with
          | Some (ts, t') (* when t = t' *) ->
            let c_def = Sym_defs.find c concats in

            (* Rename args of c_def to avoid collision with args of def. *)
            let c_args = List.map ~f:(fun _ -> Var.fresh "c_arg") (1 -- (Sym.arity c)) in
            let c_def = E.subst_v (mk_formal_args (Sym.arity c)) c_args c_def in
            (* For simplifcation. *)
            S.add_fact (S.is_defined c_def);

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
            debug "concat_pairs: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
            if def_x = def_y then
                let zxs = List.map2 ~f:zero_of xs ts in
                let xs = List.map ~f:E.var xs in
                Some (Typing.cast t' Bitstring (Sym (c, xs)),
                      Typing.cast t' Bitstring (Sym (c, zxs)))
            else None
          | _ -> None
      in
      List.filter_map ~f:pair (Sym_defs.keys concats)
     in

    let rec arg_pairs xs ts : (bterm * bterm) list list =
      match xs, ts with
        | [], [] -> [[]]
        | x :: xs, t :: ts when can_erase x ->
          List.map ~f:(fun args ->
            (Var (x, Kind.Bitstring), zero_of x t) :: args) (arg_pairs xs ts)
        | x :: xs, _ :: ts ->
          let pairs =
            (Var (x, Kind.Bitstring), Var (x, Kind.Bitstring)) :: concat_pairs x
          in
          List.cross_product (fun pair args -> pair :: args) pairs (arg_pairs xs ts)
        | _ -> fail "arg_pairs: impossible"
    in

    let mk_fact (args1, args2) =
      Sym (Logical Logical.Eq, [Sym (sym, args1); Sym (prime sym, args2)])
      |> CV_fact.make fun_types
    in

    arg_pairs (mk_formal_args num_args) arg_types
      (* remove trivial equations *)
    |> List.map ~f:List.split
    |> List.filter ~f:(fun (args1, args2) -> args1 <> args2)
    |> List.map ~f:mk_fact
  in

  S.reset_facts ();
  Sym_defs.to_list auxiliary
  |> List.concat_map ~f:(fun (sym, def) ->
    debug "Auxiliary facts: checking %s: %s" (Sym.to_string sym) (E.to_string def);
    let (ts, _) = Fun_type_ctx.find sym fun_types in
    facts sym def ts)


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

    auxiliary_facts : cvfact list;
    zero_facts : cvfact list;
    parsing_eqs : parsing_eq list;
    encoder_facts : encoder_fact list;
  }
end

open Model

(*************************************************)
(** {1 CV Output} *)
(*************************************************)

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
        (String.concat ", " (List.map ~f:show_exp_body es))
    | Annotation (_, e) -> show_exp_body e
    | e -> "unexpected{" ^ E.dump e ^ "}"
  and show_in_var t name = name ^ ": " ^ Type.to_string t
  in

  match s with
    | In [v] ->
      "in(c_in, " ^ show_in_var Bitstring v ^ ");";

    | In vs ->
      "in(c_in, (" ^ String.concat ", " (List.map ~f:(show_in_var Bitstring) vs) ^ "));";

    | New (v, t) ->
      "new " ^ show_in_var t v ^ ";";

    | Out [e] ->
      "out(c_out, " ^ show_exp_body e ^ ");";

    | Out es ->
      "out(c_out, (" ^ String.concat ", " (List.map ~f:show_exp_body es) ^ "));";

    | Eq_test (e1, e2) ->
      "if " ^ show_exp_body e1 ^ " = " ^ show_exp_body e2 ^ " then "

    | Aux_test e ->
      "if " ^ show_exp_body e ^ " then "

    | Fun_test e ->
      "if " ^ show_exp_body e ^ " then "

    | Assume e ->
      Printf.sprintf "assume %s in" (show_exp_body e)

    | Event (name, es) ->
      "event " ^ name ^ "(" ^ String.concat ", " (List.map ~f:show_exp_body es) ^ ");"

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
  let result = String.concat "\n" (List.map ~f:show_cv_stmt p) ^ zero in
  result

let print_indent s = print_endline ("  " ^ s)

(*
  FIXME: we aren't even printing the parsing rules, are we?
*)
let write_cv model =

  let casts = List.dedup (Typing.casts model.client @ Typing.casts model.server) in

  let print_fun_def is_injective sym def =
    if Template.is_defined model.template sym
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
        let _, t = Fun_type_ctx.find sym model.fun_types in
        print_endline ("const " ^ s ^ ": " ^ Type.to_string t ^ ".");
        print_endline ""
      | sym ->
        print_endline ("fun "
                       ^ Sym.cv_declaration sym (Fun_type_ctx.find sym model.fun_types)
                       ^ compos);
        print_endline ""
    end
  in

  let print_concat sym def =
    print_fun_def (is_injective_concat sym def) sym def;
  in

  let print_cast (t, t') =
    print_endline ("fun " ^ Sym.to_string (Cast (t, t'))
                   ^ "(" ^ Type.to_string t ^ "): " ^ Type.to_string t' ^ " [compos].")
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

  let print_relation c1 c2 op =
    try
    begin
        let id = ref 0 in

        let formal_arg _ =
          id := !id + 1;
          "var" ^ string_of_int !id
        in
        let show_arg v t =
          v ^ ": " ^ Type.to_string t
        in
        let (arg_types1, t1) = Fun_type_ctx.find c1 model.fun_types in
        let (arg_types2, t2) = Fun_type_ctx.find c2 model.fun_types in

        (* FIXME: should this be made part of transformations? *)
        if t1 = t2 && (op = "<>" || arg_types1 = arg_types2)
        then begin
          let args1 = List.map ~f:formal_arg arg_types1 in
          let args2 =
            if op = "<>" then List.map ~f:formal_arg arg_types2
            else args1
          in
          let all_args =
            List.dedup (List.map2 ~f:show_arg args1 arg_types1
                      @ List.map2 ~f:show_arg args2 arg_types2)
          in
          printf "forall %s;\n" (String.concat ", " all_args);
          printf "  %s(%s) %s %s(%s).\n\n"
            (Sym.to_string c1) (String.concat ", " args1)
            op
            (Sym.to_string c2) (String.concat ", " args2);
        end
    end with Not_found -> ()
  in

  let print_encoder_fact = function
    | Disjoint (s, s') -> print_relation s s' "<>"
    | Equal    (s, s') -> print_relation s s' "="
  in

  let print_cv_fact fact = print_endline (CV_fact.to_string fact) in

  let client_proc = show_cv_process model.client in
  let server_proc = show_cv_process model.server in

  List.iter ~f:print_endline (Template.crypto model.template);

  (*
  print_endline "\n(*************************** \n Constants \n***************************)\n";
  Var.Map.iter print_constant model.constants;
  *)

  print_endline "\n(*************************** \n  Formatting Functions \n***************************)\n";
  Sym_defs.iter ~f:print_concat model.concats;
  Sym_defs.iter ~f:(print_fun_def false) model.parsers;
  print_endline "";
  List.iter ~f:print_encoder_fact model.encoder_facts;

  print_endline "\n(*************************** \n  Arithmetic Functions \n***************************)\n";
  Sym_defs.iter ~f:(print_fun_def false) model.arith;

  print_endline "\n(*************************** \n  Auxiliary Tests \n***************************)\n";
  Sym_defs.iter ~f:(print_fun_def false) model.auxiliary;

  print_endline "\n(*************************** \n  Zero Functions \n***************************)\n";
  Sym_defs.iter ~f:(print_fun_def false) model.zero_funs;

  print_endline "\n(*************************** \n  Typecasting \n***************************)\n";
  List.iter ~f:print_cast casts;
  List.iter ~f:print_cast_eq casts;

  print_endline "\n(*************************** \n  Auxiliary Facts \n***************************)\n";
  List.iter ~f:print_cv_fact model.auxiliary_facts;

  print_endline "\n(*************************** \n  Zero Facts \n***************************)\n";
  List.iter ~f:print_cv_fact model.zero_facts;

  print_endline "";

  List.iter ~f:print_endline (Template.crypto2 model.template);
  List.iter ~f:print_endline (Template.query model.template);

  print_endline "\n(*************************** \n  Model \n***************************)\n";
  print_endline "let client = ";
  print_endline client_proc;
  print_endline "let server = ";
  print_endline server_proc;

  List.iter ~f:print_endline (Template.envp model.template)

(*************************************************)
(** {1 Main} *)
(*************************************************)

let verbose = true

let rec remove_casts : type a. a exp -> a exp = function
  | Sym (Op (Sym.Op.Cast_to_int, _), [e]) -> remove_casts e
  | e -> E.descend {E.descend = remove_casts} e

let debug_iml client server title =
  if verbose then prerr_title title;
  if verbose then prerr_endline "Client = ";
  if verbose then prerr_endline (Iml.to_string client);
  if verbose then prerr_endline "Server = ";
  if verbose then prerr_endline (Iml.to_string server)

let setup_debug () =
  set_debug (fun labels ->
    let at_most_n_under n l =
      match List.find_index ((=) l) labels with
      | None -> false
      | Some i -> i <= n
    in
    false
    || List.length labels <= 1
    || at_most_n_under (-1) "Typing.check"
    || at_most_n_under (-1) "Typing.check_robust_safety"
    || at_most_n_under (-1) "parsing_eqs"
    || at_most_n_under (-1) "auxiliary_facts"
    || at_most_n_under (-1) "parsing_safety"
    || at_most_n_under (-1) "inrange"
    || false)

let main () =

  setup_debug ();

  let (client, server) = Symex.raw_in (open_in_bin Sys.argv.(1)) in

  let server = server |> remove_comments in
  let client = client |> remove_comments in

  debug_iml client server "initial IML";

  let server = remove_trailing_computations server in
  let client = remove_trailing_computations client in
  debug_iml client server "IML after removing trailing computations";

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

  (************************
    Formatting facts
  *************************)

  let parsing_eqs = with_debug "parsing_eqs" (compute_parsing_rules fun_types parsers) concats in

  prerr_title "Parsing Equations";
  List.iter ~f:(fun eq -> prerr_endline (show_parsing_eq ~fun_types eq)) parsing_eqs;

  let parsers = cleanup_defs (client @ server) parsers in
  let parsing_eqs = cleanup_parsing_eqs (client @ server) parsing_eqs in

  let encoder_facts = encoder_facts (Sym_defs.to_list concats) in

  (************************
    Pattern matching
  *************************)

  let client = match_inverse client in
  let server = match_inverse server in

  push_debug "parsing_safety";
  let client = match_safe_parsers parsers concats parsing_eqs [] client in
  let server = match_safe_parsers parsers concats parsing_eqs [] server in
  pop_debug "parsing_safety";

  let client = merge_patterns client in
  let server = merge_patterns server in

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
  let auxiliary, fun_types = add_auxiliary_primed auxiliary fun_types in
  let client = remove_auxiliary client in
  let server = remove_auxiliary server in
  debug_iml client server "IML after removing auxiliary ifs";

  (************************
    Zero facts
  *************************)

  let casts = List.dedup (Typing.casts client @ Typing.casts server) in
  let zero_facts, zero_funs, zero_types = zero_facts concats casts fun_types in
  let fun_types = Fun_type_ctx.disjoint_union [fun_types; zero_types] in

  write_cv {
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
    encoder_facts }

;;

(*
  Trying to get both the full text of the exception and
  the backtrace. Waiting for a fix for
  http://caml.inria.fr/mantis/view.php?id=5040
*)

Printexc.register_printer (function
  | Failure s -> Some s
  | _ -> None);
;;

Printexc.print main ()

