(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

module Core_map = Map

open Iml
open Iml.Type
open Iml.Sym
open Iml.Sym.Op
open Iml.Sym.Arith
open Iml.Sym.Logical
open Iml.Sym.Cmp
open Iml.Exp

module E = Iml.Exp

(*************************************************)
(** {1 Types} *)
(*************************************************)

type answer = Yes | No | Maybe

(**
    [true] means definitely true, [false] means we don't know.
*)
type pbool = bool

(*************************************************)
(** {1 State} *)
(*************************************************)

let ctx : Yices.context = Yices.mk_context ()

let cache : pbool Int_map.t ref = ref Int_map.empty

(* accelerated cache for eq queries *)
module Int_pair =
struct
  type t = int * int
  let compare = Pervasives.compare
end
module Pair_map = Core_map.Make (Int_pair)
let eq_cache: pbool Pair_map.t ref = ref Pair_map.empty

let warn_cache = ref E.Set.empty

(*************************************************)
(** {1 Naming} *)
(*************************************************)

(*
  The naming should be separate from the naming used by output routines,
  we want the names to persist continuously, no reset.

  At the same time this ending may, if necessary, be made to respect
  output names when they are available.
*)

let mk_exp_name (type a) (e : a Exp.t) =
  let result = match e with
    | Var (v, _) -> "var_" ^ v
    | String _ as e ->
      let escaped =
        E.to_string e |> String.map (function
        | '\\' -> '_'
        | c -> c)
      in
      "string_" ^ escaped
    | _ -> "var" ^ (string_of_int (E.id e))
  in
  `Mangled result

(*************************************************)
(** {1 Yices theory} *)
(*************************************************)

let theory =
  "\n\
(define-type bitstringbot)\n\
(define bottom:: bitstringbot)\n\
(define-type bitstring (subtype (x::bitstringbot) (/= x bottom)))\n\
\n\
; These correspond to val and bs functions in the paper\n\
(define value_unsigned:: (-> bitstringbot nat))\n\
(define value_signed::   (-> bitstringbot int))\n\
(define bs_unsigned::    (-> int nat bitstringbot))\n\
(define bs_signed::      (-> int nat bitstringbot))\n\
\n\
; In theory we should have two functions, one using C interpretation of truth, the other\n\
; using IML interpretation, but these two would be indistinguishable from yices point of\n\
; view. See the translation function.\n\
(define truth:: (-> bitstringbot bool))\n\
\n\
; The length of bottom is arbitrary.\n\
(define len::   (-> bitstringbot nat))\n\
(define range:: (-> bitstringbot nat nat bitstringbot))\n\
\n\
(define defined :: (-> bitstringbot bool))\n\
"
(*
  (define ptr::   (-> nat nat nat))
  (assert
  (forall (base1::nat offset1::nat base2::nat offset2::nat)
  (=> (/= base1 base2)
  (/= (ptr base1 offset1) (ptr base2 offset2)))))
*)

;;
Yices.parse_command ctx theory
;;

let range () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "range")

let len () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "len")

let value = function
  | `Unsigned -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "value_unsigned")
  | `Signed -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "value_signed")

let truth () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "truth")

let bs = function
  |  `Unsigned -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_unsigned")
  |  `Signed -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_signed")

(*
let ptr () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "ptr")
*)

let defined () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "defined")

(*************************************************)
(** {1 Building facts} *)
(*************************************************)

let eq_bitstring es = Sym (Bs_eq, es)
let eq_int es = Sym (Int_cmp Eq, es)
let not_e (e : fact) : fact =
  match e with
  | Sym (Logical Not, [e]) -> e
  | e -> Sym (Logical Not, [e])
let gt a b = Sym (Int_cmp Gt, [a; b])
let ge a b = Sym (Int_cmp Ge, [a; b])

let true_fact: fact = Sym (Logical True, [])

let is_defined e = Sym (Defined, [e])

let rec in_type (e : bterm) (t : bitstring Type.t) : fact =
  let module T = Iml.Type in
  match t with
    | T.Bitstringbot -> true_fact
    | T.Bitstring    -> is_defined e
    | T.Fixed n      -> eq_int [E.int n; Len e]
    | T.Bounded n    -> ge (E.int n) (Len e)
    | T.Bs_int _ | T.Ptr ->
      begin match e with
      | Sym (Op (_, (_, t')), _) when t = t' -> is_defined e
      | e -> Sym (In_type t, [e])
      (* fail "%s" (E.to_string (Sym (In_type t, [e]))) *)
      end
    | T.Named (_, Some t) -> in_type e t
    | T.Named (_, None) -> Sym (In_type t, [e])

(*
  We don't represent integer ranges directly because they are too big for OCaml int64.
*)
module Range = struct
  type t = Int_type.t

  (* Don't raise to the power explicitly, to avoid overflow *)
  let pow a n =
    if n = 0 then E.one else
    E.prod (List.replicate n (E.int a))

  let subset itype itype' =
    Int_type.signedness itype = Int_type.signedness itype'
    && Int_type.width itype <= Int_type.width itype'

  let contains itype e =
    match E.itype e with
    | Some itype' when subset itype' itype -> [true_fact]
    | _ ->
      let w = Int_type.width itype in
      let a, b = match Int_type.signedness itype with
        | `Unsigned ->
          let n = pow 256 w in
          E.zero, Sym (Int_op Minus, [n; E.int 1])
        | `Signed ->
          let n = E.prod [E.int 128; pow 256 (w - 1)] in
          Sym (Int_op Neg, [n]), Sym (Int_op Minus, [n; E.int 1])
      in
      [Sym (Int_cmp Ge, [e; a]); Sym (Int_cmp Le, [e; b])]

end

(*************************************************)
(** {1 Debug} *)
(*************************************************)

let warn_on_failed_conditions_ref = ref true

let warn_on_failed_conditions b =
  warn_on_failed_conditions_ref := b

let debug_expr s e =
  if debug_enabled () then begin
    prerr_string (decorate_debug s);
    flush stderr;
    Yices.pp_expr e;
    prerr_endline "";
    flush stderr;
  end;

(*************************************************)
(** {1 Checking facts} *)
(*************************************************)

;;
Yices.enable_type_checker true
;;

let rec rewrite_ptr : type a. a Exp.t -> a Exp.t = fun e ->
  (*
    To deal with
      <<stack null_ptr; index 0(i8), index 0(i1)>> == <<stack null_ptr; index 0(i1)>>
  *)
  let not_zero = function
    | (Flat (E.Int 0L), _) -> false
    | (Index 0, _) -> false
    | _ -> true
  in
  match e with
  | Ptr (pb, eo) ->
    Var ("ptr_" ^ E.to_string (Ptr (pb, List.filter ~f:not_zero eo)), Kind.Bitstring)
  | e -> E.descend {E.descend = rewrite_ptr} e

let rec split_and (e : fact) =
  match e with
  | Sym (Logical And _, es) -> List.concat_map ~f:split_and es
  | e -> [e]

module Mode = struct
  type t = [ `Assert | `Query | `Simplify_step | `Simplify ]

  let to_string = function
    | `Assert -> "assert"
    | `Query -> "query"
    | `Simplify_step -> "simplify_step"
    | `Simplify -> "simplify"
end

module Rewrite_key = struct
  type 'a t = Mode.t * 'a exp
  module Kind = Kind
  let kind (_, e) = E.kind e
  let to_string (mode, e) = Printf.sprintf "%s, %s" (Mode.to_string mode) (E.to_string e)
end

module Rewrite_result = struct
  type 'a t = 'a exp * fact list
  module Kind = Kind
  let kind (e, _) = E.kind e
end

module Cache = Common.Map_any (Kind) (Rewrite_key) (Rewrite_result)

(* CR make this a hash table *)
let rewrite_cache = ref Cache.empty

let rewrite
    (type a)
    ~(mode : [ `Assert | `Query | `Simplify_step ])
    (e : a exp)
    : a Rewrite_result.t =

  let rec rewrite
      : type a.
        mode : Mode.t
        -> ?assume:fact list
        -> a exp -> a Rewrite_result.t = fun ~mode ?(assume = []) e ->
    match Cache.maybe_find (mode, e) !rewrite_cache with
    | Some result -> result
    | None ->
      (* We can't really push assume down into rewriting because then caching
         would be unsound. *)
      let result = do_rewrite ~mode e in
      rewrite_cache := Cache.add (mode, e) result !rewrite_cache;
      let e, conds = result in
      let assume = List.concat_map ~f:split_and assume in
      let conds = List.diff conds assume in
      e, conds

  and descend_rewrite
    : type a. mode : Mode.t -> ?assume:fact list -> a exp -> a Rewrite_result.t
    = fun ~mode ?(assume = []) e ->
    let all_conds = ref [] in
    let rewrite : type a. a exp -> a exp = fun e ->
      let e, conds = rewrite ~mode ~assume e in
      all_conds := conds @ !all_conds;
      e
    in
    let e = E.descend {E.descend = rewrite} e in
    e, !all_conds

  (* Application of the chaining rule (see thesis) *)
  and rewrite_conjunction ~mode es =
    let rec loop ~result_es ~result_conds = function
      | [] -> List.dedup result_es, (List.dedup result_conds)
      | e :: es ->
        let e', result_conds' = rewrite ~mode e in
        let result_es' = split_and e' in
        (* CR use sets *)
        let result_conds' = List.diff result_conds' result_es in
        let result_es = result_es' @ result_es in
        let result_conds = result_conds' @ result_conds in
        loop ~result_es ~result_conds es
    in
    loop ~result_es:[] ~result_conds:[] es

  (* For now I follow the principle that all transformations relating to one
     syntactic construct should be in one place. Another option would be to
     split this function into several and get rid of the mode argument. *)
  and do_rewrite
      : type a. mode : Mode.t -> a exp -> a Rewrite_result.t = fun ~mode e ->
    let rewritten_conds = ref Fact_set.empty in
    let raw_conds = ref Fact_set.empty in
    let queued_conds = Queue.create () in
    let add_conditions ?(already_rewritten = false) conds =
      let conds = List.concat_map conds ~f:split_and in
      let conds = Fact_set.of_list conds in
      if already_rewritten
      then rewritten_conds := Fact_set.union !rewritten_conds conds
      else begin
        let conds = Fact_set.diff conds !raw_conds in
        raw_conds := Fact_set.union !raw_conds conds;
        List.iter (Fact_set.to_list conds) ~f:(fun cond -> Queue.add cond queued_conds)
      end
    in
    let e_top = e in
    let rec collect : type a. mode : Mode.t -> a exp -> a exp = fun ~mode e ->
      let collect_even_if_simplifying e = collect ~mode e in
      let collect : type a. ?mode : Mode.t -> a exp -> a exp = fun ?(mode = mode) e ->
        match mode with
        | `Query | `Assert | `Simplify -> collect ~mode e
        | `Simplify_step -> Fn.id e
      in
      let make_opaque e =
        begin match mode with
        | `Simplify | `Simplify_step -> e
        | `Assert | `Query -> Sym (Opaque, [e])
        end
      in
      let fail_already_rewritten e =
        fail "Rewriting an expression that is already rewritten: %s" (E.to_string e)
      in
      let default e =
        E.descend {E.descend = collect} e
      in
      let e_top = e in
      let (result : a exp) =
        match e with
        (*
          Rewriting of binary arithmetic to integer arithmetic.
        *)
        | Sym (Truth_of_bs,
               [Sym ((Op (Op_cmp cmp, ([Bs_int t1; Bs_int t2], _))), [e1; e2])]) ->
          let sym' = Int_cmp cmp in
          add_conditions [is_defined e1; is_defined e2];
          collect (Sym (sym', [Val (e1, t1); Val (e2, t2)]))

        | Sym (Int_cmp _, [e1; e2]) as e ->
          let defined = [is_defined e1; is_defined e2] in
          (* The chaining rule only matters for assert. *)
          begin match mode with
          | `Assert ->
            let defined, defined_conds = rewrite_conjunction ~mode defined in
            let e, e_conds = descend_rewrite ~mode ~assume:defined e in
            add_conditions ~already_rewritten:true (defined_conds @ e_conds);
            E.conj (defined @ [e])
          | `Simplify | `Simplify_step ->
            E.descend {E.descend = collect} e
          | `Query ->
            (* For queries rewrite into a weaker form that allows us to give better
               warnings.  (we get a warning if a side condition does not hold.) *)
            add_conditions defined;
            E.descend {E.descend = collect} e
          end

        | Val ((Sym (Op (Op_arith op, _), [e1; e2])) as e, itype) ->
          let sym' = Int_op op in
          let e'= Sym (sym', [Val (e1, itype); Val (e2, itype)]) in
          add_conditions (is_defined e :: Range.contains itype e');
          collect e'

        | Val ((Sym (Op (Cast_to_int, ([Bs_int itype_from], Bs_int itype_to)), [e])) as cast_e, itype_to') ->
          if itype_to <> itype_to' then
            fail "itype of Val not the same as itype of cast: %s" (E.to_string e_top);
          let e' = Val (e, itype_from) in
          let range_cond =
            if Range.subset itype_from itype_to then []
            else Range.contains itype_to e'
          in
          add_conditions (is_defined cast_e :: range_cond);
          collect e'

        | Val (BS (e, itype) as e_bs, itype') ->
          if itype <> itype'
          then fail "incompatible Val of BS: %s" (E.to_string e_top)
          else begin
            add_conditions [is_defined e_bs];
            collect e
          end

        | BS (Val (e, itype), itype') as e_bs ->
          if itype <> itype'
          then default e
          (*  fail "incompatible BS of Val: %s" (E.to_string e_top); *)
          (* Not failing since in normal form we try to see if "msg" is equal to, say
             ((msg{4, 8})_[u,8])^[u,3] *)
          else begin
            add_conditions [is_defined e_bs];
            collect e
          end

        | Char c ->
          E.int (Char.code c)

        | Len e as e_top ->
          let unexpected e =
            fail "Unexpected len argument: %s" (E.to_string e)
          in
          let default e =
            match mode with
            | `Simplify | `Simplify_step ->
              e_top
            | `Assert | `Query ->
              add_conditions [is_defined e];
              Sym (Len_y, [collect e])
          in
          begin match e with
          | BS (_, itype) as e_bs ->
            add_conditions [is_defined e_bs];
            collect (E.int (Int_type.width itype))

          | Sym (BS_of_truth width, _) as e_bs ->
            add_conditions [is_defined e_bs];
            E.int width

          | Sym (Op (_, (_, Bs_int itype)), _) as e_bin ->
            add_conditions [is_defined e_bin];
            collect (E.int (Int_type.width itype))

          | Sym (Op _, _) ->
            assert false

          | Concat es ->
            collect (E.sum (List.map ~f:(fun e -> Len e) es))

          | Range (_, _, l) as e ->
            add_conditions [is_defined e];
            collect l

          | String b ->
            E.int (List.length b)

          (* This will become unnecessary once pointers are rewritten into vanilla
             expressions, as per thesis *)
          | Ptr _ as e ->
            add_conditions [is_defined e];
            Sym (Ptr_len, [])

          | Struct (_, _, l, _) as e ->
            add_conditions [is_defined e];
            collect l

          | Annotation (_, e) ->
            collect_even_if_simplifying (Len e)

          | Sym ((Opaque), _) as e -> unexpected e

          | Sym (Replicate, _) as e -> default e
          | Sym (Cmp, _) as e -> default e
          | Sym (Ztp, _) as e -> default e
          | Sym (Ztp_safe, _) as e -> default e
          | Sym (Undef _, _) as e -> default e
          | Sym (Fun _, _) as e -> default e
          | Sym (Cast _, _) as e -> default e
          | Var _ as e -> default e
          | Array _ as e -> default e
          | Unknown _ as e -> default e
          end

        | Sym (Defined, [e]) ->
          let default e =
            Sym (Defined, [collect e])
          in
          begin match e with
          (* Here and below we do not list defined() conditions because those are
             implied by the comparison operators *)
          | Range (e, p, l) ->
            E.conj [ge (Len e) (E.sum [p; l]);
                    ge p E.zero;
                    ge l E.zero;] |> collect

          | BS (e, itype) ->
            E.conj (Range.contains itype e) |> collect

          | Val (e, itype) ->
            eq_int [E.int (Int_type.width itype); E.len e] |> collect

          | Sym (Op (_, (ts, _)), es) ->
            let conds =
              List.combine ts es
              |> List.filter_map ~f:(function
                | Bs_int itype, e -> Some (eq_int [E.int (Int_type.width itype); E.len e])
                | Type.Ptr, Ptr _ -> None
                | t, e ->
                  fail "unexpected type of op argument: %s: %s"
                    (E.to_string e) (Type.to_string t))
            in
            collect (E.conj conds)

          | Sym (sym, es) ->
            if Sym.never_fails sym
            then true_fact
            else if not (Sym.may_fail sym)
            then E.conj (List.map ~f:is_defined es) |> collect
            else begin match mode with
            | `Simplify | `Simplify_step | `Query ->
              E.descend {E.descend = collect} e_top
            | `Assert ->
              let e' = is_defined (collect (Sym (sym, es))) in
              E.conj (e' :: List.map ~f:collect (List.map ~f:is_defined es))
            end

          | Len e ->
            Sym (Defined, [e]) |> collect

          | Int _ -> true_fact
          | Char _ -> true_fact
          | String _ -> true_fact
          | Concat [] -> true_fact

          | Concat es ->
            E.conj (List.map ~f:is_defined es) |> collect

          (* This will become unnecessary once pointers are rewritten into vanilla
             expressions, as per thesis *)
          | Ptr (_, pos) ->
            let defined_offset (offset, _) =
              match offset with
              | Flat e -> Some (is_defined e)
              | Index _ | Attr _ | Field _ -> None
            in
            E.conj (List.filter_map ~f:defined_offset pos) |> collect

          | Struct (fields, _, _, e) ->
            E.conj (is_defined e :: List.map ~f:is_defined (Str_map.values fields)) |> collect

          | Annotation (_, e) ->
            Sym (Defined, [e]) |> collect_even_if_simplifying

          | Var _ as e -> default e
          | Unknown _ as e -> default e
          | Array _ as e -> default e
          end

        | Sym (Defined, _) -> assert false

        (* Unlike for val and len, we don't need to replace BS by a yices compatible form,
           because it is defined with bitstringbot as domain in yices, so returning bottom
           is not a problem.  *)
        | BS (e, itype) ->
          let e' = collect ~mode:`Simplify e in
          if e <> e'
          (* Re-collecting to deal with things like
             (len(msg{12, (msg{4, 8})_[u,8]}:fixed_20_nonce))^[u,8] *)
          then collect (BS (e', itype))
          (* Need to appply again with our own mode to make sure all yices-compatibility
             transformations are applied. *)
          else BS (collect ~mode e', itype)

        (*
          Replacing vals by their Yices versions.
        *)
        | Val (e, itype) ->
          begin match mode with
          | `Simplify | `Simplify_step ->
            e_top
          | `Query | `Assert ->
            add_conditions [is_defined e];
            Sym (Val_y itype, [collect e])
          end

        (*
          Falling through or turning into opaque.
        *)

        | Annotation (a, e) ->
          Annotation (a, collect_even_if_simplifying e)

        (* TODO: inline, once GADT pattern matching is sorted. *)
        (* I suppose everything of type bitstringbot can be turned into opaque here. *)
        | Sym (Fun _, _) as e -> make_opaque e
        | Sym (Ztp, _) as e -> make_opaque e
        | Sym (Ztp_safe, _) as e -> make_opaque e
        | Sym (Undef _, _) as e -> make_opaque e
        | Sym (Cmp, _) as e -> make_opaque e
        | Sym (Op _, _) as e -> make_opaque e
        | Struct _ as e -> make_opaque e
        | Array _ as e -> make_opaque e
        | Concat _ as e -> make_opaque e

        | Sym (Opaque, _) as e -> fail_already_rewritten e
        | Sym (Len_y, _) as e -> fail_already_rewritten e
        | Sym (Val_y _, _) as e -> fail_already_rewritten e

        | Sym (Bs_eq, _) as e -> default e
        | Sym (Int_op _, _) as e -> default e
        | Sym (Int_cmp _, _) as e -> default e
        | Sym (Logical _, _) as e -> default e
        | Sym (Ptr_len, _) as e -> default e
        | Sym (Cast _, _) as e -> default e
        | Sym (Replicate, _) as e -> default e
        | Sym (Field_offset _, _) as e -> default e
        | Sym (In_type _, _) as e -> default e
        | Sym (BS_of_truth _, _) as e -> default e
        | Sym (Truth_of_bs, _) as e -> default e
        | Int _ as e -> default e
        | String _ as e -> default e
        | Var _ as e -> default e
        | Range _ as e -> default e
        | Ptr _ as e -> default e
        | Unknown _ as e -> default e
      in
      push_debug "collect";
      debug "collect(%s) %s ~> %s"
        (Mode.to_string mode) (E.to_string e) (E.to_string result);
      pop_debug "collect";
      result
    in
    let e = collect ~mode e in
    while not (Queue.is_empty queued_conds) do
      let cond = Queue.pop queued_conds in
      let cond = collect ~mode:`Query cond in
      add_conditions ~already_rewritten:true [cond]
    done;
    let conds = Fact_set.to_list !rewritten_conds in
    let conds =
      match E.kind e with
      | Kind.Bool -> List.diff conds (split_and e)
      | Kind.Int -> conds
      | Kind.Bitstring -> conds
    in
    push_debug "rewrite";
    debug "%s: %s |- %s ~> %s"
      (Mode.to_string mode) (E.list_to_string conds) (E.to_string e_top) (E.to_string e);
    pop_debug "rewrite";
    e, conds
  in

  debug "rewriting %s" (E.to_string e);
  push_debug "rewrite";
  let e, conds = rewrite ~mode:(mode :> Mode.t) e in
  let conds = List.map conds ~f:rewrite_ptr in
  let e =
    match mode with
    | `Simplify_step -> e
    | `Assert | `Query -> rewrite_ptr e
  in
  pop_debug "rewrite";
  debug "resulting e = %s" (E.to_string e);
  debug "resulting conds = %s" (E.list_to_string conds);
  e, conds

let rewrite_facts ~mode es: fact list * fact list =
  let es, conds = List.map ~f:(rewrite ~mode) es |> List.split in
  let es = List.dedup (List.concat_map ~f:split_and es) in
  let conds = List.dedup (List.concat conds) in
  es, conds

let is_opaque (type a) (e : a Exp.t) =
  match rewrite ~mode:`Assert e with
  | Sym (Opaque, _), _ -> true
  | _ -> false

module Kind = struct
  include Kind

  let to_yices_type (type a) (t : a t) =
    match t with
    | Bitstring      -> Yices.mk_type ctx "bitstringbot" (* sic *)
    | Int            -> Yices.mk_type ctx Yices.int_type_name
    | Bool           -> Yices.mk_type ctx Yices.bool_type_name
end

let add_fact_raw ?(check_consistent = true) y_e =
  push_debug "add_fact_raw";
  debug_expr "asserting_y " y_e;
  Yices.assert_simple ctx y_e;

  if check_consistent && Yices.inconsistent ctx = 1 then
  begin
    (* dump_context ctx; *)
    debug_expr "add_fact: the context has become inconsistent: " y_e;
    fail "inconsistent context";
  end;
  pop_debug "add_fact_raw"

let reset_cache () =
  cache := Int_map.empty;
  eq_cache := Pair_map.empty

let reset_facts : unit -> unit = fun () ->
  Yices.reset ctx;
  Yices.parse_command ctx theory;
  reset_cache ()

let get_decl kind (`Mangled name) =
  try Yices.get_var_decl_from_name ctx name
  with Failure _ -> Yices.mk_var_decl ctx name (Kind.to_yices_type kind)

let translate (e_top : fact) =

  let module A = Array in

  let mk_var e =
    let k = E.kind e in
    Yices.mk_var_from_decl ctx (get_decl k (mk_exp_name e))
  in

  let rec tr : type a. a Exp.t -> Yices.expr = fun e ->
    debug "translating %s" (E.dump e);
    match e with
      | Int i                  -> Yices.mk_num ctx (Int64.to_int i)
      | String _               -> mk_var e
      (* All variables are Bitstringbot except for in eval *)
      | Var _                  -> mk_var e
      | Range (e, pos, len)    -> Yices.mk_app ctx (range ()) [| tr e; tr pos; tr len |]
      | Sym (Opaque, [_]) as e -> mk_var e
      | Annotation(_, e)       -> tr e
      | BS (e, itype)          ->
        let sg = Int_type.signedness itype in
        let width = Int_type.width itype in
        Yices.mk_app ctx (bs sg) [| Yices.mk_num ctx width; tr e |]
      | Sym (sym, es) ->
        begin match sym, es with
          | (Logical True, [])         -> Yices.mk_true ctx
          | (Logical Not, [a])         -> Yices.mk_not ctx (tr a)
          | (Logical (And _), [])      ->
            fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Logical (And _), es)      -> Yices.mk_and ctx (A.map tr (A.of_list es))
          | (Logical (Or _), [])       ->
            fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Logical (Or _), es)       -> Yices.mk_or  ctx (A.map tr (A.of_list es))
          | (Logical Implies, [a; b])  -> Yices.mk_ite ctx (tr a) (tr b) (Yices.mk_true ctx)
          | (Int_cmp Eq, [a; b])       -> Yices.mk_eq ctx (tr a) (tr b)
          | (Int_cmp Ne, [a; b])       -> Yices.mk_diseq ctx (tr a) (tr b)
          | (Int_cmp Gt, [a; b])       -> Yices.mk_gt ctx (tr a) (tr b)
          | (Int_cmp Ge, [a; b])       -> Yices.mk_ge ctx (tr a) (tr b)
          | (Int_cmp Lt, [a; b])       -> Yices.mk_lt ctx (tr a) (tr b)
          | (Int_cmp Le, [a; b])       -> Yices.mk_le ctx (tr a) (tr b)

          | (Bs_eq, [a; b])   -> Yices.mk_eq ctx (tr a) (tr b)
          | (In_type _, _)    -> mk_var e
          | (Defined, [e])    -> Yices.mk_app ctx (defined ()) [| mk_var e |]

          (* C interpretation of truth *)
          | (Truth_of_bs, [e]) -> Yices.mk_app ctx (truth ()) [| mk_var e |]
          (* IML interpretation of truth *)
          | (Opaque, _)        -> Yices.mk_app ctx (truth ()) [| mk_var e |]

          | Int_op Neg, [a]        -> Yices.mk_sub ctx [| Yices.mk_num ctx 0; tr a |]
          | Int_op Minus, [e1; e2] -> Yices.mk_sub ctx [| tr e1; tr e2 |]
          | Int_op Minus, _        ->
            fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | Int_op (Plus _), []    ->
            fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | Int_op (Plus _), es    -> Yices.mk_sum ctx (A.map tr (A.of_list es))
          | Int_op (Mult _), []    ->
            fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | Int_op (Mult _), es    -> Yices.mk_mul ctx (A.map tr (A.of_list es))
          | Ptr_len, []           -> mk_var e

          | Len_y, [e]            -> Yices.mk_app ctx (len ())   [| tr e |]
           (* Not sure this is necessary, perhaps could just make it opaque. *)
          | Val_y itype, [e]      -> Yices.mk_app ctx (value (Int_type.signedness itype))  [| tr e |]

          | _ ->
            fail "Solver.translate: unexpected expression %s in fact %s"
              (E.dump e) (E.dump e_top)
        end

      | e ->
        fail "Solver.translate: unexpected expression %s in fact %s"
          (E.dump e) (E.dump e_top)

  in
  with_debug "Solver.translate" tr e_top

let is_true_raw ?warn_if_false e =
  debug "checking (with auxiliary facts) %s" (E.to_string e);
  push_debug "is_true_raw.translate";
  let ye = translate (not_e e) in
  pop_debug "is_true_raw.translate";
  debug_expr "checking (yices expression)" ye;
  Yices.push ctx;
  Yices.assert_simple ctx ye;
  let result = match Yices.check ctx with
    | Yices.False -> true
    | Yices.Undef -> false
    | Yices.True  -> false
  in
  Yices.pop ctx;
  debug "check result = %s" (string_of_bool result);
  begin match warn_if_false with
  | None -> ()
  | Some err ->
    if !warn_on_failed_conditions_ref && not result && not (E.Set.mem e !warn_cache) then
      begin
        warn "cannot prove %s %s" (E.to_string e) err;
        (*
          Returns NULL model:
          push ctx;
          assert_simple ctx (silent translate (not_e e));
          let model = get_model ctx in
          display_model model;
          pop ctx;
        *)
        warn_cache := E.Set.add e !warn_cache;
      end;
  end;
  result

let rec simplify_bool (e : fact) =
  let is_true = function
    | Sym (Logical And _, []) -> true
    | Sym (Logical True, []) -> true
    | _ -> false
  in
  match e with
  | Sym (Logical Implies, [e1; e2]) when is_true e1 -> simplify_bool e2
  | Sym (Logical And _, [e]) -> simplify_bool e
  | Sym (Logical op, es) -> Sym (Logical op, List.map ~f:simplify_bool es)
  | e -> e

let add_fact (e : fact) =
  push_debug "add_fact";
  reset_cache ();
  let es', conds = rewrite_facts ~mode:`Assert [e] in
  let warn_if_false = Printf.sprintf "arising from assuming %s" (E.to_string e) in
  List.iter ~f:(fun cond -> is_true_raw ~warn_if_false cond |> ignore) conds;
  let e = Sym (Logical Implies, [E.conj conds; E.conj es'] ) |> simplify_bool in
  debug "assuming %s" (E.to_string e);
  add_fact_raw (translate e);
  pop_debug "add_fact"

let is_true e: pbool =
  debug "checking %s" (E.to_string e);
  let id = E.id e in
  let result =
    match Option.try_with (fun () -> Int_map.find id !cache) with
    | Some result ->
      (* This debug is 25 % performance penalty: *)
      debug "result (from cache) = %s" (string_of_bool result);
      result
    | None ->
      push_debug "is_true";
      let es', conds = rewrite_facts ~mode:`Query [e] in
      let warn_if_false = Printf.sprintf "arising from querying %s" (E.to_string e) in
      let result =
           List.for_all ~f:(is_true_raw ~warn_if_false) conds
        && List.for_all ~f:(is_true_raw) es'
      in
      pop_debug "is_true";
      debug "result (not from cache): %b" result;
      result
  in
  cache := Int_map.add id result !cache;
  result

let implies facts hypotheses =

  debug "checking implication: \n  %s\n  =>\n  %s" (E.list_to_string facts) (E.list_to_string hypotheses);

  push_debug "implies";
  Yices.push ctx;
  List.iter ~f:add_fact facts;
  let result = List.for_all ~f:(is_true) hypotheses in
  Yices.pop ctx;
  pop_debug "implies";

  debug "implication result: %b" result;

  result

(* TODO: change back to equal when it stabilizes *)
let equal_bitstring (a : bterm) (b : bterm) =
  let a_id, b_id = E.id a, E.id b in
  try Pair_map.find (a_id, b_id) !eq_cache
  with Not_found ->
    let result = is_true (eq_bitstring [a; b]) in
    eq_cache := Pair_map.add (a_id, b_id) result !eq_cache;
    result

let not_equal_bitstring (a : bterm) (b : bterm) =
  is_true (not_e (eq_bitstring [a; b]))

let greater_equal (a : iterm) (b : iterm) =
  is_true (ge a b)

let equal_int ?(facts = []) a b =
  if facts = [] then is_true (eq_int [a; b])
  else implies facts [eq_int [a; b]]

let greater_equal_len (a : iterm) (b : iterm) =
  greater_equal a b
  (* match (a, b) with
    | (All, _) -> true
    | (_, All) -> false
    | (Unknown, _) | (_, Unknown) -> false
    | (x, y) -> greater_equal x y *)

let greater_equal_len_answer (a : iterm) (b : iterm) =
  if greater_equal_len a b then
    Yes
  else if greater_equal_len b a then
    No
  else
    Maybe

(*************************************************)
(** {1 Evaluation.} *)
(*************************************************)

(* TODO: cache? *)
let eval e =
  push_debug "eval";

  let warn_if_false = Printf.sprintf "arising from evaluation of %s" (E.to_string e) in
  let e, conds = rewrite ~mode:`Query e in
  debug "eval: e = %s, conds = %s" (E.to_string e) (E.list_to_string conds);
  let result =
    if not (List.for_all ~f:(is_true_raw ~warn_if_false) conds)
    then begin
      debug "eval: conditions not satisfied";
      None
    end
    else begin
      Yices.push ctx;
      let v = Var (Var.fresh "int_val", Kind.Int) in
      Yices.assert_simple ctx (translate (eq_int [v; e]));
      let result =
        match Yices.check ctx with
        | Yices.False | Yices.Undef ->
          debug "eval: could not find a value";
          None
        | Yices.True ->
          let model = Yices.get_model ctx in
          let vy = get_decl Kind.Int (mk_exp_name v) in
          (*
          debug "eval: got a model:";
          Yices.display_model model;
          *)
          match Option.try_with (fun () -> Yices.get_int_value model vy) with
          | None ->
            debug "eval: could not extract value";
            None
          | Some value ->
            let value = Int32.to_int value in
            debug "eval: a possible value is %d" value;
            (* Make sure the value is unique *)
            add_fact_raw ~check_consistent:false (translate (not_e (eq_int [v; E.int value])));
            (*
            increase_debug_depth ();
            debug "eval: context for checking uniqueness:";
            if debug_enabled () then Yices.dump_context ctx;
            decrease_debug_depth ();
            *)
            match Yices.check ctx with
            | Yices.False -> Some value
            | Yices.Undef
            | Yices.True  ->
              debug "value is not unique";
              None
      in
      Yices.pop ctx;
      result
    end
  in
  pop_debug "eval";
  result

(*************************************************)
(** {1 Simplification.} *)
(*************************************************)

(* TODO: cache? *)
let simplify e =
  debug "Solver.simplify %s" (E.to_string e);
  push_debug "Solver.simplify";
  let e', conds = rewrite ~mode:`Simplify_step e in
  let warn_if_false = Printf.sprintf "arising from simplification of %s" (E.to_string e) in
  let result =
    if List.for_all ~f:(is_true_raw ~warn_if_false) conds then e' else e
  in
  pop_debug "Solver.simplify";
  debug "result: %s" (E.to_string result);
  result

let not = not_e

(*************************************************)
(** {1 Testing.} *)
(*************************************************)

let test_implication () =
  let nonce = Var ("nonce", Kind.Bitstring) in
  let bs e = BS (e, Int_type.create `Unsigned 4) in
  assert
    (implies
       [eq_int [Len nonce; Int 20L ]]
       [eq_int [Len nonce; Int 20L ]]);
  assert
    (implies
       [eq_int [Len nonce; Int 20L ]]
       [eq_bitstring [bs (Len nonce); bs (Int 20L)]])

let test_bs_cancellation1 () =
  let itype = Int_type.create `Unsigned 4 in
  let eight = BS (Int 8L, itype) in
  let e = BS (Annotation (Name "eight", Val (eight, itype)), itype) in
  assert (is_true (eq_bitstring [e; eight]))

(*
  msg{4, 8} = (len(msg{12, (msg{4, 8})_[u,8]}:fixed_20_nonce))^[u,8]

  CR: speak about different ways of assuming defined.
*)
let test_bs_cancellation2 () =
  let t = Named ("nonce", Some (Fixed 20)) in
  let itype = Int_type.create `Unsigned 8 in
  let l1 = Range (var "msg", Int 4L, Int 8L) in
  let e1 = Range (var "msg", Int 12L, Val (l1, itype)) in
  let e2 = Annotation (Type_hint t, e1) in
  let e3 = BS (Len e2, itype) in
  assert (implies
            [is_defined e2]
            [eq_bitstring [l1; e3]])

let test_annot_equality () =
  let l =
    Val (Range (Var ("msg", Kind.Bitstring), Int 4L, Int 8L),
         Int_type.create `Unsigned 8)
  in
  let e =
    Annotation (Type_hint (Named ("nonce", Some (Fixed 20))),
                Range (Var ("msg", Kind.Bitstring), Int 12L, l))
  in
  assert (implies [is_defined e] [eq_int [Len e; l]])

let test_eval () =
  assert (eval (Int 42L) = Some 42)

let with_ctx f =
  Yices.push ctx;
  f ();
  Yices.pop ctx

let test () =
  with_ctx test_implication;
  with_ctx test_annot_equality;
  with_ctx test_eval;
  with_ctx test_bs_cancellation1;
  with_ctx test_bs_cancellation2

(* 870 lines *)
