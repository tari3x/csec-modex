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

module E = struct
  include Iml.Exp
  include Iml.Exp.T
end

(*************************************************)
(** {1 Types} *)
(*************************************************)

type answer = Yes | No | Maybe

(**
    [true] means definitely true, [false] means we don't know.
*)
type pbool = bool

type fact = exp

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
module Pair_map = Map.Make (Int_pair)
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

let mk_exp_name e =
  let result = match e with
    | Var v -> "var_" ^ v
    | String s -> "string" ^ s
    | _ -> "var" ^ (string_of_int (E.id e))
  in
  `Mangled result

(*************************************************)
(** {1 Yices theory} *)
(*************************************************)

let theory =
  "
(define-type bitstringbot)
(define bottom:: bitstringbot)
(define-type bitstring (subtype (x::bitstringbot) (/= x bottom)))

; These correspond to val and bs functions in the paper
(define value_unsigned:: (-> bitstringbot nat))
(define value_signed::   (-> bitstringbot int))
(define bs_unsigned::    (-> int nat bitstringbot))
(define bs_signed::      (-> int nat bitstringbot))

; In theory we should have two functions, one using C interpretation of truth, the other
; using IML interpretation, but these two would be indistinguishable from yices point of
; view. See the translation function.
(define truth:: (-> bitstringbot bool))

; The length of bottom is arbitrary.
(define len::   (-> bitstringbot nat))
(define range:: (-> bitstringbot nat nat bitstringbot))

(define defined:: (-> bitstringbot bool))
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

let bs = function
  |  `Unsigned -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_unsigned")
  |  `Signed -> Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bs_signed")

let truth () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "truth")

let bottom () =
    Yices.mk_var_from_decl ctx (Yices.get_var_decl_from_name ctx "bottom")

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
let eq_int es = Sym (Eq_int, es)
let not_e = function
  | Sym (Not, [e]) -> e
  | e -> Sym (Not, [e])
let gt a b = Sym (Gt_int, [a; b])
let ge a b = Sym (Ge_int, [a; b])

let true_fact: fact = Sym (True, [])

let is_defined e = Sym (Defined, [e])

let rec in_type e t =
  let module T = Iml.Type.T in
  match t with
    | T.Bitstringbot -> true_fact
    | T.Bitstring    -> is_defined e
    | T.Fixed n      -> eq_int [E.int n; Len e]
    | T.Bounded n    -> ge (E.int n) (Len e)
    | T.Bool | T.Int | T.Bs_int _ | T.Ptr ->
      begin match e with
        | Sym (sym, _) when Sym.result_type sym = t -> is_defined e
        | e -> Sym (In_type t, [e])
          (* fail "%s" (E.to_string (Sym (In_type t, [e]))) *)
       end
    | T.Named (name, Some t) -> in_type e t
    | T.Named (name, None) -> Sym (In_type t, [e])

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
    match E.type_of e with
    | Bs_int itype' when subset itype' itype -> [true_fact]
    | _ ->
      let w = Int_type.width itype in
      let a, b = match Int_type.signedness itype with
        | `Unsigned ->
          let n = pow 256 w in
          E.zero, Sym (Minus_int, [n; E.int 1])
        | `Signed ->
          let n = E.prod [E.int 128; pow 256 (w - 1)] in
          Sym (Neg_int, [n]), Sym (Minus_int, [n; E.int 1])
      in
      [Sym (Ge_int, [e; a]); Sym (Le_int, [e; b])]

end

(*************************************************)
(** {1 Debug} *)
(*************************************************)

let warn_on_failed_conditions_ref = ref true

let warn_on_failed_conditions b =
  warn_on_failed_conditions_ref := b

let debug_expr ?(raise_by = 0) s e =
  if debug_enabled () then begin
    prerr_string (decorate_debug s); flush stderr; Yices.pp_expr e; prerr_endline ""; flush stderr;
  end;

(*************************************************)
(** {1 Checking facts} *)
(*************************************************)

;;
Yices.enable_type_checker true
;;

let rec rewrite_ptr e =
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
  | Ptr (pb, eo) -> Var ("ptr_" ^ E.to_string (Ptr (pb, List.filter not_zero eo)))
  | e -> E.descend rewrite_ptr e

let rec split_and = function
  | Sym (And _, es) -> List.concat_map split_and es
  | e -> [e]

let rewrite ~(mode:[`Assert | `Query | `Simplify]) e: exp * fact list =
  (* List of conditions that are already accounted for and don't need to be added again. *)
  let seen = ref [] in

  let rewrite_once ~mode e =
    let conds = ref [] in

    let rec collect e =
      push_debug "collect";
      let collect_even_if_simplifying = collect in
      let collect =
        match mode with
        | `Query | `Assert -> collect
        | `Simplify -> Fn.id
      in
      let facts, e' =
        let e_top = e in
        (* This is fine by the chaining rule: if the expression itself contains the
           condition, then we don't need to add the condition in any subsequent
           rewritings.

           This implies that the order of subexpressions generation in the matching below
           matters.  For instance, in (e <= e') clause we genereate and rewrite the
           defined(e), defined(e') clauses first, so they can be reused when rewriting e
           and e'.

           Of course, no order would violate soundness.  *)
        seen := e :: !seen;
        match e with
        (*
          Rewriting of binary arithmetic to integer arithmetic.
        *)
        | Sym ((Op (op, ([Bs_int t1; Bs_int t2], _))) as sym, [e1; e2])
            when Sym.is_binary_comparison sym ->
          let sym' =
            begin match op with
            | Eq -> Eq_int
            | Ne -> Ne_int
            | Ge -> Ge_int
            | Gt -> Gt_int
            | Le -> Le_int
            | Lt -> Lt_int
            | _ -> fail "impossible: binary comparsion %s" (E.to_string e)
            end
          in
          [is_defined e1; is_defined e2],
          Sym (sym', [Val (e1, t1); Val (e2, t2)]) |> collect

        | Sym (sym, [e1; e2]) when Sym.is_integer_comparison sym ->
          let defined = [is_defined e1; is_defined e2] in
          begin match mode with
          | `Assert ->
            (* Enforce order of evaluation, for assertions only (conditions are
               rewritten on the outside). *)
            let defined = List.map collect defined in
            let e' = E.descend collect e in
            [], E.conj (defined @ [e'])
          | `Query | `Simplify ->
            (* For queries rewrite into a weaker form that allows us to give better
               warnings.  (we get a warning if a side condition does not hold.) *)
            defined, E.descend collect e
          end

        | Val ((Sym (sym, [e1; e2])) as e, itype) when Sym.is_binary_arithmetic sym ->
          let sym' =
            begin match sym with
            | Op (Plus_a, _) -> Plus_int 2
            | Op (Minus_a, _) -> Minus_int
            | Op (Mult, _) -> Mult_int 2
            | Op (Div, _) -> fail "solver: support for division not activated: %s" (E.to_string e)
            | _ -> fail "unexpected binary arithmetic %s" (Sym.to_string sym)
            end
          in
          let e'= Sym (sym', [Val (e1, itype); Val (e2, itype)]) in
          is_defined e :: Range.contains itype e', collect e'

        | Val ((Sym (Op (Cast_to_int, ([Bs_int itype_from], Bs_int itype_to)), [e])) as cast_e, itype_to') ->
          if itype_to <> itype_to' then
            fail "itype of Val not the same as itype of cast: %s" (E.to_string e_top);
          let e' = Val (e, itype_from) in
          let range_cond =
            if Range.subset itype_from itype_to then []
            else Range.contains itype_to e'
          in
          is_defined cast_e :: range_cond, collect e'

        | Val (BS (e, itype) as e_bs, itype') ->
          if itype <> itype' then
            fail "incompatible Val of BS: %s" (E.to_string e_top);
          [is_defined e_bs], collect e

        | BS (Val (e, itype), itype') as e_bs ->
          if itype <> itype' then
            fail "incompatible BS of Val: %s" (E.to_string e_top);
          [is_defined e_bs], collect e

        | Char c ->
          [], E.int (Char.code c)

        | Len e ->
          begin match e with

          | BS (_, itype) as e_bs ->
            [is_defined e_bs], collect (E.int (Int_type.width itype))

          | Sym (BS_of_truth width, _) as e_bs ->
            [is_defined e_bs], E.int width

          | Sym (Op (_, (_, Bs_int itype)), _) as e_bin ->
            [is_defined e_bin], collect (E.int (Int_type.width itype))

          | Sym (Op _, _) ->
            assert false

          | Concat es ->
            [], collect (E.sum (List.map (fun e -> Len e) es))

          | Range (_, _, l) as e ->
            [is_defined e], collect l

          | String b ->
            [], E.int (String.length b / 2)

          (* This will become unnecessary once pointers are rewritten into vanilla
             expressions, as per thesis *)
          | Ptr _ as e ->
            [is_defined e], Sym (Ptr_len, [])

          | Annotation (a, e) ->
            [], collect_even_if_simplifying (Len e)

          | Sym ((Bs_eq | Minus_int | Plus_int _ | Mult_int _ | Neg_int | Le_int | Ge_int
                     | Lt_int | Gt_int | Eq_int | Ne_int
                     | Implies | And _ | Or _
                     | Not | True | Ptr_len | Field_offset | Const _ | Truth_of_bs | Len_y
                     | Val_y _ | Opaque | Defined | In_type _), _)
          | Char _ | Val _ | Len _ ->
            fail "Unexpected len argument: %s" (E.to_string e_top)

          | Sym ((Replicate | Cmp | Ztp | Ztp_safe | Undef _ | Fun _ | Nondet_fun _ | Cast _), _)
          | Int _ | Var _ | Unknown | Struct _ | Array _ as e ->
            match mode with
            | `Simplify ->
              [], e_top
            | `Assert | `Query ->
              [is_defined e], Sym (Len_y, [collect e])
          end

        | Sym (Defined, [e]) ->
          begin match e with
          (* Here and below we do not list defined() conditions because those are
             implied by the comparison operators *)
          | Range (e, p, l) ->
            [], E.conj [ge (Len e) (E.sum [p; l]);
                        ge p E.zero;
                        ge l E.zero;] |> collect

          | BS (e, itype) ->
            [], E.conj (Range.contains itype e) |> collect

          | Val (e, itype) ->
            [], eq_int [E.int (Int_type.width itype); E.len e] |> collect

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
            [], E.conj conds |> collect

          | Sym (sym, es) ->
            if Sym.never_fails sym then
              [], true_fact
            else if not (Sym.may_fail sym) then
              [], E.conj (List.map is_defined es) |> collect
            else
              begin match mode with
              | `Simplify | `Query ->
                [], E.descend collect e_top
              | `Assert ->
                let e' = Sym (Defined, [Sym (sym, es) |> collect]) in
                [], E.conj (e' :: List.map collect (List.map is_defined es))
              end

          | Len e ->
            [], Sym (Defined, [e]) |> collect

          | Int _ | Char _ | String _ | Concat [] ->
            [], true_fact

          | Concat es ->
            [], E.conj (List.map is_defined es) |> collect

          (* This will become unnecessary once pointers are rewritten into vanilla
             expressions, as per thesis *)
          | Ptr (_, pos) ->
            let defined_offset (offset, _) =
              match offset with
              | Flat e -> Some (is_defined e)
              | Index _ | Attr _ | Field _ -> None
            in
            [], E.conj (List.filter_map defined_offset pos) |> collect

          | Struct (fields, _, _, e) ->
            [], E.conj (List.map is_defined (is_defined e :: Str_map.values fields)) |> collect

          | Annotation (a, e) ->
            [], Sym (Defined, [e]) |> collect_even_if_simplifying

          | Var _ | Unknown | Array _ as e->
            [], Sym (Defined, [collect e])
          end

        | Sym (Defined, _) -> assert false

        (*
          Replacing vals by their Yices versions.
        *)

        | Val (e, itype) ->
          begin match mode with
          | `Simplify ->
            [], e_top
          | `Query | `Assert ->
            [is_defined e], Sym (Val_y itype, [collect e])
          end

        (*
          Falling through or turning into opaque.
        *)

        | Annotation (a, e) ->
          begin match mode with
          | `Query | `Assert ->
            [], collect e
          | `Simplify ->
            [], Annotation (a, collect_even_if_simplifying e)
          end

        (* I suppose everything of type bitstringbot can be turned into opaque here. *)
        | Sym ((Fun _ | Nondet_fun _ | Ztp | Ztp_safe | Undef _ | Cmp), _)
        | Sym (Op _, _)
        | BS _
        | Struct _ | Array _
        | Concat _ ->
          begin match mode with
          | `Simplify ->
            [], e_top
          | `Assert | `Query ->
            [], Sym (Opaque, [e])
          end

        | Sym ((Opaque | Len_y | Val_y _), _) as e ->
          fail "Rewriting an expression that is already rewritten: %s" (E.to_string e)

        | Sym ((Bs_eq | Minus_int | Plus_int _ | Mult_int _ | Neg_int | Le_int
                   | Ge_int | Lt_int | Gt_int | Eq_int | Ne_int
                   | Implies | And _ | Or _
                   | Not | True | Ptr_len | Cast _ | Replicate | Field_offset
                   | In_type _ | BS_of_truth _ | Truth_of_bs | Const _), _)
        | Int _ | String _ | Var _ | Range _ | Ptr _ | Unknown ->
          [], E.descend collect e
      in
      pop_debug "collect";
      debug "collect: %s |- %s ~> %s" (E.list_to_string facts) (E.to_string e) (E.to_string e');
      conds := facts @ !conds;
      e'
    in
    let e = collect e in
    let conds = List.diff !conds !seen |> List.nub in
    seen := conds @ !seen;
    e, conds
  in

  let cond_mode =
    match mode with
    | `Simplify -> `Query
    | `Query | `Assert -> mode
  in

  let rec rewrite_cond e =
    let e, es = rewrite_once ~mode:cond_mode e in
    split_and e @ List.concat_map rewrite_cond es
  in

  debug "rewriting %s" (E.to_string e);
  push_debug "rewrite";
  let e, conds = rewrite_once ~mode e in
  let conds =
    conds
    |> List.concat_map ~f:rewrite_cond
    |> List.nub
    |> List.map ~f:rewrite_ptr
  in
  let e =
    match mode with
    | `Simplify -> e
    | `Assert | `Query -> rewrite_ptr e
  in
  pop_debug "rewrite";
  debug "resulting e = %s" (E.to_string e);
  debug "resulting conds = %s" (E.list_to_string conds);
  e, conds

let rewrite_facts ~mode es: fact list * fact list =
  let es, conds = List.map (rewrite ~mode) es |> List.split in
  let es = List.nub (List.concat_map split_and es) in
  let conds = List.nub (List.concat conds) in
  List.iter (E.typecheck Bool) (es @ conds);
  es, conds

let is_opaque e =
  match rewrite ~mode:`Assert e with
  | Sym (Opaque, _), _ -> true
  | _ -> false

module Type = struct
  include Type

  let to_yices_type = function
    | Bitstringbot   -> Yices.mk_type ctx "bitstringbot"
    | Bitstring      -> Yices.mk_type ctx "bitstring"
    | Bs_int _        -> Yices.mk_type ctx "bitstring"
    | Type.T.Int     -> Yices.mk_type ctx Yices.int_type_name
    | Bool           -> Yices.mk_type ctx Yices.bool_type_name
    | t              -> fail "to_yices_type: unexpected type: %s" (to_string t)
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

let get_decl t (`Mangled name) =
  try Yices.get_var_decl_from_name ctx name
  with Failure _ -> Yices.mk_var_decl ctx name (Type.to_yices_type t)

let translate e_top =

  let module A = Array in

  let mk_var t e =
    Yices.mk_var_from_decl ctx (get_decl t (mk_exp_name e))
  in

  let rec tr t e =
    debug "translating %s" (E.dump e);
    match e, t with
      | Int i,                   Type.Int       -> Yices.mk_num ctx (Int64.to_int i)
      | String s,                Bitstringbot   -> mk_var Bitstring e
      (* All variables are Bitstringbot except for in eval *)
      | Var _,                   t              -> mk_var t e
      (* TODO: mk_var Bool *)
      | Sym (sym, es), Bool ->
        begin
        match sym, es with
          | (True, [])         -> Yices.mk_true ctx
          | (Not, [a])         -> Yices.mk_not ctx (tr Bool a)
          | (And _, [])        -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (And _, es)        -> Yices.mk_and ctx (A.map (tr Bool) (A.of_list es))
          | (Or _, [])         -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Or _, es)         -> Yices.mk_or  ctx (A.map (tr Bool) (A.of_list es))
          | (Implies, [a; b])  -> Yices.mk_ite ctx (tr Bool a) (tr Bool b) (Yices.mk_true ctx)
          | (Eq_int, [a; b])   -> Yices.mk_eq ctx (tr Type.Int a) (tr Type.Int b)
          | (Ne_int, [a; b])   -> Yices.mk_diseq ctx (tr Type.Int a) (tr Type.Int b)
          | (Gt_int, [a; b])   -> Yices.mk_gt ctx (tr Type.Int a) (tr Type.Int b)
          | (Ge_int, [a; b])   -> Yices.mk_ge ctx (tr Type.Int a) (tr Type.Int b)
          | (Lt_int, [a; b])   -> Yices.mk_lt ctx (tr Type.Int a) (tr Type.Int b)
          | (Le_int, [a; b])   -> Yices.mk_le ctx (tr Type.Int a) (tr Type.Int b)

          | (Bs_eq, [a; b])    ->
                Yices.mk_eq ctx (tr Bitstringbot a) (tr Bitstringbot b)

          | (Defined, [e])     -> Yices.mk_app ctx (defined ()) [| tr Bitstringbot e |]
          | (In_type _, _)     -> mk_var Type.Bool e

          (* C interpretation of truth *)
          | (Truth_of_bs, [e]) -> Yices.mk_app ctx (truth ()) [| mk_var Bitstringbot e |]
          (* IML interpretation of truth *)
          | (Opaque, _)        -> Yices.mk_app ctx (truth ()) [| mk_var Bitstringbot e |]

          | _ ->
            fail "Solver.translate: unexpected type %s of expression %s in fact %s"
              (Type.to_string t) (E.dump e) (E.dump e_top)
        end

      | Sym (sym, es), Type.Int ->
        begin
        match sym, es with
          | Neg_int, [a]          -> Yices.mk_sub ctx [| Yices.mk_num ctx 0; tr Type.Int a |]
          | (Minus_int), [e1; e2] -> Yices.mk_sub ctx [| tr Type.Int e1; tr Type.Int e2 |]
          | (Minus_int), _        -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Plus_int _), []      -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Plus_int _), es      -> Yices.mk_sum ctx (A.map (tr Type.Int) (A.of_list es))
          | (Mult_int _), []      -> fail "wrong number of arguments: %s in fact %s" (E.dump e) (E.dump e_top)
          | (Mult_int _), es      -> Yices.mk_mul ctx (A.map (tr Type.Int) (A.of_list es))
          | Ptr_len, []           -> mk_var Type.Int e

          | Len_y, [e]            -> Yices.mk_app ctx (len ())   [| tr Bitstringbot e |]
           (* Not sure this is necessary, perhaps could just make it opaque. *)
          | Val_y itype, [e]      -> Yices.mk_app ctx (value (Int_type.signedness itype))  [| tr Bitstringbot e |]

          | _ ->
            fail "Solver.translate: unexpected type %s of expression %s in fact %s" (Type.to_string t) (E.dump e) (E.dump e_top)
        end

      | Range (e, pos, len),     Bitstringbot -> Yices.mk_app ctx (range ()) [| tr Bitstringbot e;
                                                                                tr Type.Int pos; tr Type.Int len |]
      | Sym (Opaque, [_]),       Bitstringbot -> mk_var Bitstringbot e

      | Annotation(_, e),        t            -> tr t e

      | e, t ->
        fail "Solver.translate: unexpected type %s of expression %s in fact %s" (Type.to_string t) (E.dump e) (E.dump e_top)

  in
  with_debug "Solver.translate" (tr Bool) e_top

let is_true_raw ?warn_if_false e =
  debug "checking (with auxiliary facts) %s" (E.to_string e);
  push_debug "is_true_raw.translate";
  let ye = translate (not_e e) in
  pop_debug "is_true_raw.translate";
  debug_expr ~raise_by:0 "checking (yices expression)" ye;
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

let rec simplify_bool =
  let is_true = function
    | Sym (And _, []) | Sym (True, []) -> true
    | _ -> false
  in
  function
  | Sym (Implies, [e1; e2]) when is_true e1 -> simplify_bool e2
  | Sym (And _, [e]) -> simplify_bool e
  | Sym (sym, _) as e when Sym.is_logical sym -> E.descend simplify_bool e
  | e -> e

let add_fact : exp -> unit = fun e ->
  push_debug "add_fact";
  reset_cache ();
  let es', conds = rewrite_facts ~mode:`Assert [e] in
  let warn_if_false = Printf.sprintf "arising from assuming %s" (E.to_string e) in
  List.iter (fun cond -> is_true_raw ~warn_if_false cond |> ignore) conds;
  let e = Sym (Implies, [E.conj conds; E.conj es'] ) |> simplify_bool in
  pop_debug "add_fact";
  debug "assuming %s" (E.to_string e);
  add_fact_raw (translate e)

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
           List.for_all (is_true_raw ~warn_if_false) conds
        && List.for_all (is_true_raw) es'
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
  List.iter add_fact facts;
  let result = List.for_all (is_true) hypotheses in
  Yices.pop ctx;
  pop_debug "implies";

  debug "implication result: %b" result;

  result

(* TODO: change back to equal when it stabilizes *)
let equal_bitstring : exp -> exp -> pbool = fun a b ->
  if a = Unknown || b = Unknown then
    fail "equal: trying to apply to special length values (Unknown or All)";
  let a_id, b_id = E.id a, E.id b in
  try Pair_map.find (a_id, b_id) !eq_cache
  with Not_found ->
    let result = is_true (eq_bitstring [a; b]) in
    eq_cache := Pair_map.add (a_id, b_id) result !eq_cache;
    result

let not_equal_bitstring : exp -> exp -> pbool = fun a b ->
  is_true (not_e (eq_bitstring [a; b]))

let greater_equal : exp -> exp -> pbool = fun a b ->
  is_true (ge a b)

let equal_int ?(facts = []) a b =
  if facts = [] then is_true (eq_int [a; b])
  else implies facts [eq_int [a; b]]

let greater_equal_len : exp -> exp -> pbool = fun a b ->
  greater_equal a b
  (* match (a, b) with
    | (All, _) -> true
    | (_, All) -> false
    | (Unknown, _) | (_, Unknown) -> false
    | (x, y) -> greater_equal x y *)

let greater_equal_len_answer : len -> len -> answer = fun a b ->
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
  let result =
    if not (List.for_all (is_true_raw ~warn_if_false) conds)
    then None
    else begin
      Yices.push ctx;
      let v = Var.fresh "int_val" in
      Yices.assert_simple ctx (translate (eq_int [Var v; e]));
      let result =
        match Yices.check ctx with
        | Yices.False | Yices.Undef -> None
        | Yices.True ->
          let model = Yices.get_model ctx in
          let vy = get_decl Type.Int (mk_exp_name (Var v)) in
          (*
          debug "eval: got a model:";
          increase_debug_depth ();
          if debug_enabled () then Yices.display_model model;
          decrease_debug_depth ();
          *)
          match Option.try_with (fun () -> Yices.get_int_value model vy) with
          | None -> None
          | Some value ->
            let value = Int32.to_int value in
            debug "eval: a possible value is %d" value;
            (* Make sure the value is unique *)
            add_fact_raw ~check_consistent:false (translate (not_e (eq_int [Var v; E.int value])));
            (*
            increase_debug_depth ();
            debug "eval: context for checking uniqueness:";
            if debug_enabled () then Yices.dump_context ctx;
            decrease_debug_depth ();
            *)
            match Yices.check ctx with
            | Yices.False -> Some value
            | Yices.Undef -> None
            | Yices.True  -> None
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
  let e', conds = rewrite ~mode:`Simplify e in
  let warn_if_false = Printf.sprintf "arising from simplification of %s" (E.to_string e) in
  let result =
    if List.for_all (is_true_raw ~warn_if_false) conds then e' else e
  in
  pop_debug "Solver.simplify";
  debug "result: %s" (E.to_string result);
  result

let not = not_e

(*************************************************)
(** {1 Testing.} *)
(*************************************************)

let test_annot_equality () =
  let l =
    Val (Range (Var "msg", Int 4L, Int 8L),
         Int_type.create `Unsigned 8)
  in
  let e =
    Annotation (Type_hint (Named ("nonce", Some (Fixed 20))),
                Range (Var "msg", Int 12L, l))
  in
  assert (implies [is_defined e] [eq_int [Len e; l]])

let test () =
  Yices.push ctx;
  test_annot_equality ();
  Yices.pop ctx

(* 870 lines *)
