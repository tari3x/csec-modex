(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Printf
open Scanf

(*************************************************)
(** {1 Types} *)
(*************************************************)

module Ptr = Int64
module Ptr_map = Custom_map (struct include Ptr let to_string = to_string end)
module Int_map = Custom_map (struct type t = int let compare = Pervasives.compare let to_string = string_of_int end)
module Str_map = Custom_map (struct include String let to_string s = s end)

module Type = struct

  module T = struct

    module Int_type = struct
      module Signedness = struct
        type t = [ `Signed | `Unsigned ]

        let to_string = function
          | `Signed -> "s"
          | `Unsigned -> "u"
      end
      type signedness = Signedness.t
      type width = int

      type t = signedness * width

      let to_string (sd, w) =
        match sd with
        | `Signed -> sprintf "[s,%d]" w
        | `Unsigned -> sprintf "[u,%d]" w

      let of_string s =
        let s = trim s in
        let toks = Str.split (Str.regexp "[][,]") s in
        match toks with
        | ["u"; w] ->  (`Unsigned, int_of_string w)
        | ["s"; w] ->  (`Signed,   int_of_string w)
        | _ -> fail "Int_type.of_string: %s" s

      let is_valid (_, w) = w <> 0

      let () = Cil.initCIL ()

      let int =
        match Cil.intType with
        | Cil.TInt (ikind, _) -> (`Signed, Cil.bytesSizeOfInt ikind)
        | _ -> assert false

      let size_t =
        (* TODO: check that this is the right type *)
        match !Cil.typeOfSizeOf with
        | Cil.TInt (ikind, _) -> (`Unsigned, Cil.bytesSizeOfInt ikind)
        | _ -> assert false

      let signedness (s, w) = s
      let width (s, w) = w
      let create s w = (s, w)
    end

    (*
      Not using CV typet, because it contains options that we don't care about,
      and so is not equatable.
    *)
    type t =
      | Bitstringbot               (** All strings and bottom. *)
      | Bitstring                  (** All machine-representable strings *)
      | Fixed of int               (** All strings of a given length *)
      | Bounded of int             (** All strings up to a given length *)
      | Bool
      | Int
      | Ptr
      | Bs_int of Int_type.t
      | Named of string * t option (** A named type with an optional type definition.
                                       Named (_, None) may not contain bottom. *)
  end

  include T

  let of_string s =
    try Bs_int (Int_type.of_string s) with
    _ ->
    match List.map String.trim (Str.bounded_split (Str.regexp "_") s 3) with
      | ["bitstringbot"]     -> Bitstringbot
      | ["bitstring"]        -> Bitstring
      | ["bitstring"; name]  -> Named (name, Some Bitstring)
      | ["fixed"; n]         -> Fixed (int_of_string n)
      | ["fixed"; n; name]   -> Named (name, Some (Fixed (int_of_string n)))
      | ["bounded"; n]       -> Bounded (int_of_string n)
      | ["bounded"; n; name] -> Named (name, Some (Bounded (int_of_string n)))
      | ["bool"]             -> Bool
      | ["int"]              -> Int
      | ["ptr"]              -> Ptr
      | _                    -> Named (s, None)

  let rec to_string = function
    | Bitstringbot         -> "bitstringbot"
    | Bitstring            -> "bitstring"
    | Fixed n              -> "fixed_" ^ string_of_int n
    | Bounded n            -> "bounded_" ^ string_of_int n
    | Bool                 -> "bool"
    | Int                  -> "int"
    | Ptr                  -> "ptr"
    | Bs_int itype          -> Int_type.to_string itype
    | Named (name, Some t) -> to_string t ^ "_" ^ name
    | Named (name, None)   -> name

  let rec strip_name = function
    | Named (_, Some t) -> strip_name t
    | t -> t

  let subtype t t' =
    match strip_name t, strip_name t' with
    | Int, _ | _, Int -> t = t'
    | _, Bitstringbot -> true
    | Bitstringbot, _ -> false
    | _, Bitstring    -> true
    | Bitstring, _    -> false
    | Bounded i, Bounded i' -> i <= i'
    | Fixed i, Bounded i'   -> i <= i'
    | Fixed i, Fixed i'     -> i = i'
    | t, t' -> t = t'

  let intersection t t' =
    if subtype t t' then t
    else if subtype t' t then t'
    else fail "cannot compute intersection of types %s and %s" (to_string t) (to_string t')

  let union t t' =
    if subtype t t' then t'
    else if subtype t' t then t
    else fail "cannot compute union of types %s and %s" (to_string t) (to_string t')

  (* Could return true for more types, but this is enough for now. *)
  let has_fixed_length t =
    match strip_name t with
    | Fixed _ -> true
    | _ -> false
end

type imltype = Type.t

module Fun_type = struct
  type t = Type.t list * Type.t

  let to_string (ts, t) =
    let ts = List.map Type.to_string ts in
    let t = Type.to_string t in
    sprintf "%s -> %s" (String.concat " * " ts) t

  let of_string s =
    if not (Str.string_match (Str.regexp "\\(.*\\) -> \\(.*\\)") s 0)
    then fail "Op_type.of_string: %s" s
    else try
      (* Call matched_group before calling split. *)
      let result_type = Str.matched_group 2 s in
      let arg_types = Str.matched_group 1 s |> Str.split (Str.regexp "\\*") in
      (List.map Type.of_string arg_types, Type.of_string result_type)
    with
      e -> fail "Op_type.of_string: %s: %s" s (Printexc.to_string e)
end

module Sym = struct
  open Type.T

  module Op = struct
    module T = struct
      (* TODO: import these directly from CIL *)
      type op =
          Neg                                 (** Unary minus *)
        | BNot                                (** Bitwise complement (~) *)
        | LNot                                (** Logical Not (!) *)

        | Plus_a                               (** arithmetic + *)
        | Plus_PI                              (** pointer + integer *)

        | Minus_a                              (** arithmetic - *)
        | Minus_PI                             (** pointer - integer *)
        | Minus_PP                             (** pointer - pointer *)
        | Mult                                (** * *)
        | Div                                 (** / *)
        | Mod                                 (** % *)
        | Shiftlt                             (** shift left *)
        | Shiftrt                             (** shift right *)

        | Lt                                  (** <  (arithmetic comparison) *)
        | Gt                                  (** >  (arithmetic comparison) *)
        | Le                                  (** <= (arithmetic comparison) *)
        | Ge                                  (** >  (arithmetic comparison) *)
        | Eq                                  (** == (arithmetic comparison) *)
        | Ne                                  (** != (arithmetic comparison) *)
        | BAnd                                (** bitwise and *)
        | BXor                                (** exclusive-or *)
        | BOr                                 (** inclusive-or *)

        | LAnd                                (** logical and. Unlike other
                                               * expressions this one does not
                                               * always evaluate both operands. If
                                               * you want to use these, you must
                                               * set {!Cil.use_logical_operators}. *)
        | LOr                                 (** logical or. Unlike other
                                               * expressions this one does not
                                               * always evaluate both operands.  If
                                               * you want to use these, you must
                                               * set {!Cil.use_logical_operators}. *)

        | Cast_to_int
        | Cast_to_ptr
        | Cast_to_other
    end

    open T
    type t = T.op

    let to_string = function
      | Neg -> "neg"  | BNot -> "~"  |  LNot -> "!"

      | Plus_a   -> "+"   | Minus_a  ->  "-"   | Mult  -> "*"    | Div   -> "/"
      | Mod     -> "%"   | BAnd    ->  "&"   | BOr   -> "BOR"  | BXor  -> "XOR"
      | Shiftlt -> "<<"  | Shiftrt ->  ">>"  | LAnd  -> "&&"   | LOr   -> "LOR"

      | Eq -> "=="
      | Ne ->  "!="
      | Gt -> ">"
      | Le -> "<="
      | Lt -> "<"
      | Ge ->  ">="

      | Plus_PI  -> "PlusPI"
      | Minus_PI -> "MinusPI"
      | Minus_PP -> "MinusPP"

      | Cast_to_int -> "CastToInt"
      | Cast_to_ptr -> "CastToPtr"
      | Cast_to_other -> "CastToOther"

    let of_string = function
      | "+" -> Plus_a
      | "-" -> Minus_a
      | "*" -> Mult
      | "/" -> Div
      | "%" -> Mod
      | "neg" -> Neg    | "~" -> BNot     | "!" -> LNot
      | "&" -> BAnd     | "BOR" -> BOr  | "XOR" -> BXor
      | "<<" -> Shiftlt | ">>" -> Shiftrt | "&&" -> LAnd  | "LOR" -> LOr
      | "==" -> Eq
      | "!=" -> Ne
      | ">" -> Gt
      | "<=" -> Le
      | "<" -> Lt
      | ">=" -> Ge

      | "PlusPI" -> Plus_PI
      | "MinusPP" -> Minus_PP
      | "CastToInt" -> Cast_to_int
      | "CastToPtr" -> Cast_to_ptr
      | "CastToOther" -> Cast_to_other

      | s -> fail "Op.to_string: %s" s

     let is_binary_comparison = function
      | Eq | Ne | Ge | Gt | Le | Lt -> true
      | _ -> false
  end

  open Op.T

  module T = struct
    open Op.T

    type name = string
    type arity = int
    type invocation_id = int

    type sym =
    | Op of op * Fun_type.t

    | Bs_eq                               (** Bitstring comparison *)
    | Cmp                                (** Bitstring comparison returning bitstring result.
                                             Bs_eq(x, y) = Truth(Cmp(x, y)) *)


    | Minus_int                           (** Operators without overflow. Think of them as widening their result
                                              if necessary *)
    | Plus_int of arity
    | Mult_int of arity
    | Neg_int

    | Lt_int                               (** <  (arithmetic comparison) *)
    | Gt_int                               (** >  (arithmetic comparison) *)
    | Le_int                               (** <= (arithmetic comparison) *)
    | Ge_int                               (** >  (arithmetic comparison) *)
    | Eq_int                               (** == (arithmetic comparison) *)
    | Ne_int                               (** != (arithmetic comparison) *)

    | Implies
    | And of arity
    | Or of arity
    | Not
    | True

    | Ptr_len

    | Cast of Type.t * Type.t

    (**
       Zero-terminated prefix - up to but not including the first 0.
       Bottom if the bitstring does not contain zero.
    *)
    | Ztp
    (**
       Same as Ztp, but returns the argument unchanged instead of bottom.
    *)
    | Ztp_safe

    | Replicate
    | Field_offset
    | Opaque                             (** Used only in Solver *)
    | Defined
    | In_type of Type.t                   (** Defined is the same as (In_type Bitstring) *)

    (* TODO: downgrade Val and BS to symbols. *)
    | Truth_of_bs
    | BS_of_truth of Int_type.width

    (* The yices versions of len and val, see thesis. *)
    | Len_y
    | Val_y of Int_type.t

    | Const of name

    (* FIXME: unify with unknown? *)
    | Undef of invocation_id             (** With a tag to distinguish different undefs.
                                             Do not create explicitly, use Expr.undef. *)

    (* TODO: why not pull function types from the template from the very beginning? *)
    | Fun of name * arity
    (* FIXME: make non-determinism explicit by random sampling, or check that there are no
       such funs in final output *)
    | Nondet_fun of name * invocation_id * arity
  end

  open T
  type t = T.sym

  let is_arithmetic = function
    | Op (Plus_a, _) | Op (Minus_a, _) | Op (Mult, _) | Op (Div, _) | Plus_int _ | Minus_int | Mult_int _ -> true
    | _ -> false

  let is_binary_arithmetic = function
    | Op (Plus_a, _) | Op (Minus_a, _) | Op (Mult, _) | Op (Div, _) -> true
    | _ -> false

  let is_binary_comparison = function
    | Op (op, _) -> Op.is_binary_comparison op
    | _    -> false

  let is_integer_comparison = function
    | Lt_int
    | Gt_int
    | Le_int
    | Ge_int
    | Eq_int
    | Ne_int -> true
    | _ -> false

  let is_logical = function
    | Not | And _ | Or _ | Implies -> true
    | _ -> false

  let is_unary_op = function
      | Neg
      | BNot
      | LNot -> true
      | _ -> false

  let is_infix = function
      | Op (op, _) -> not (is_unary_op op)

      | Plus_int _
      | Minus_int
      | Mult_int _

      | Lt_int
      | Gt_int
      | Le_int
      | Ge_int
      | Eq_int
      | Ne_int

      | Implies
      | And _
      | Or _

      | Bs_eq -> true

      | _ -> false

  let to_string_hum ?(show_types = true) = function
    | Op (op, t) ->
      if show_types
      then sprintf "(%s : %s)" (Op.to_string op) (Fun_type.to_string t)
      else sprintf "%s" (Op.to_string op)

    | Eq_int -> "="
    | Ne_int -> "<>"
    | Ge_int -> ">="
    | Gt_int -> ">"
    | Le_int -> "<="
    | Lt_int -> "<"

    | Plus_int _ -> "+"
    | Minus_int -> "-"
    | Mult_int _ -> "*"
    | Neg_int -> "-"

    | Implies -> "=>"
    | And _ -> "/\\"
    | Or _ -> "\\/"
    | Not -> "¬"
    | True -> "True"

    | Bs_eq -> "="
    | Ptr_len -> "ptrLen"

    | Cast (t, t') -> "cast_" ^ Type.to_string t ^ "_" ^ Type.to_string t'

    | Ztp -> "ztp"
    | Ztp_safe -> "ztpSafe"

    | Truth_of_bs -> "truth_of_bs"
    | BS_of_truth width -> sprintf "bs_of_truth[%d]" width

    | Len_y -> "len_y"
    | Val_y t -> sprintf "val_y%s" (Int_type.to_string t)

    | Cmp -> "cmp"

    | Replicate -> "replicate"
    | Field_offset -> "field_offset"
    | Opaque -> "opaque"
    | Defined -> "defined"
    | In_type t -> sprintf "InType[%s]" (Type.to_string t)
    | Undef i -> Printf.sprintf "undef[%d]" i
    | Const s -> s
    | Fun (s, _) -> sprintf "%s" s
    | Nondet_fun (s, id, _) -> Printf.sprintf "%s[%d]" s id

  let to_string t = to_string_hum t

  let cv_declaration f (ts, t) =
    to_string f ^ "(" ^ String.concat ", " (List.map Type.to_string ts) ^ "): " ^ Type.to_string t

  let of_string s =
    if Str.string_match (Str.regexp "(\\(.+\\) *: \\(.+\\))") s 0
    then begin
      let op = Str.matched_group 1 s in
      let t = Str.matched_group 2 s in
      match Option.try_with (fun () -> Fun_type.of_string t) with
      | None ->
        fail "Sym.of_string: failed parsing symbol type %s" t
      | Some t ->
        match Option.try_with (fun () -> Op.of_string op) with
        | Some op -> Op (op, t)
        | None ->
          fail "Sym.of_string: failed parsing symbol %s" op
    end
    else if (Str.string_match (Str.regexp "\\(.+\\)/\\([0-9]+\\)") s 0)
    then begin
      let sym = Str.matched_group 1 s in
      let nargs = int_of_string (Str.matched_group 2 s) in
      match sym with
      | "=" -> Bs_eq
      | "EqInt" -> Eq_int
      | "ptrLen" -> Ptr_len
      | "ztp" -> Ztp
      | "ztpSafe" -> Ztp_safe
      | "cmp" -> Cmp
      | "truth_of_bs" -> Truth_of_bs
      | s when Str.string_match (Str.regexp "bs_of_truth\\[\\(.+\\)\\]") s 0 ->
        let width = int_of_string (Str.matched_group 1 s) in
        BS_of_truth width
      | s -> Fun (sym, nargs)
    end
    else fail "Sym.of_string: %s" s

  let itype_exn = function
    | Op (_, (_, itype)) -> itype
    | sym -> fail "itype of symbol not defined: %s" (to_string sym)

  let may_fail sym =
    match sym with
    | Op _
    | Ztp
    | Fun _
    | Val_y _
    | Nondet_fun _ -> true

    | Field_offset -> fail "Sym.may_fail: not so sure about %s" (to_string sym)

    | Eq_int
    | Ne_int
    | Ge_int
    | Gt_int
    | Le_int
    | Lt_int

    | Plus_int _
    | Minus_int
    | Mult_int _
    | Neg_int

    | Implies
    | And _
    | Or _
    | Not
    | True

    | Bs_eq
    | Ptr_len

    | Cast _

    | Ztp_safe

    | Truth_of_bs
    | BS_of_truth _
    | Cmp

    | Len_y

    | Replicate
    | Defined
    | In_type _
    | Undef _
    | Opaque
    | Const _ -> false

  let never_fails sym =
    match sym with
    | Bs_eq
    | In_type _
    | True
    | Implies
    | And _
    | Or _
    | Not
    | Defined -> true

    | Op _
    | Ztp
    | Fun _
    | Nondet_fun _

    | Field_offset

    | Eq_int
    | Ne_int
    | Ge_int
    | Gt_int
    | Le_int
    | Lt_int

    | Plus_int _
    | Minus_int
    | Mult_int _
    | Neg_int

    | Ptr_len

    | Cast _

    | Ztp_safe

    | Truth_of_bs
    | BS_of_truth _
    | Cmp

    | Len_y
    | Val_y _

    | Replicate
    | Undef _
    | Opaque
    | Const _ -> false


  (** The return type ignoring bottoms *)
  let result_type = function
    | Plus_int _
    | Minus_int
    | Mult_int _
    | Neg_int
    | Len_y
    | Val_y _
    | Ptr_len -> Int

    | Truth_of_bs
    | Not
    | And _
    | Or _
    | True
    | Eq_int
    | Ne_int
    | Ge_int
    | Gt_int
    | Le_int
    | Lt_int
    | Implies
    | Bs_eq
    | In_type _
    | Defined -> Bool

    | Ztp
    | Opaque
    | Fun _
    | Nondet_fun _

    | Field_offset

    | Ztp_safe

    | Cmp

    | Replicate
    | Undef _
    | Const _ -> Bitstring

    | BS_of_truth width -> Bs_int (Int_type.create `Unsigned width)

    | Cast (_, t) -> t

    | Op (_, (_, t)) -> t

  (** The expected argument type ignoring bottoms *)
  let argument_types = function
    | Eq_int
    | Ne_int
    | Ge_int
    | Gt_int
    | Le_int
    | Lt_int

    | Minus_int -> [Int; Int]

    | Plus_int n
    | Mult_int n -> List.replicate n Int

    | Neg_int -> [Int]

    | And n
    | Or n -> List.replicate n Bool

    | Not -> [Bool]
    | Implies -> [Bool; Bool]

    | BS_of_truth _ -> [Bool]

    | True
    | Const _
    | Undef _
    | Ptr_len -> []

    | Truth_of_bs
    | Ztp
    | Ztp_safe
    | Field_offset
    | Opaque
    | In_type _
    | Len_y
    | Defined -> [Bitstring]

    | Cmp
    | Bs_eq -> [Bitstring; Bitstring]

    | Replicate -> [Bitstring; Int]

    | Cast (t, _) -> [t]

    | Val_y t -> [Bs_int t]

    | Fun (_, nargs) | Nondet_fun (_, _, nargs) ->
      List.replicate nargs Bitstring

    | Op (_, (ts, _)) -> ts

  let arity t = List.length (argument_types t)

  module Key = struct
    type t = sym
    let compare = Pervasives.compare
    let to_string = to_string
  end

  module Map = Custom_map(Key)
end

type intval = int64
type ptr    = int64


(** Hex representation: each byte corresponds to two characters. Length is the number of bytes. *)
type bitstring = string


type id = int

type var = string

module Var = struct
  type t = var

  let id = ref 0

  let used_names = ref []

  let unfresh names =
    used_names := !used_names @ names

  let reset_fresh () =
    used_names := []

  let rec unused stem i =
    let name = stem ^ (string_of_int i) in
    if List.mem name !used_names then
      unused stem (i + 1)
    else
    begin
      used_names := name :: !used_names;
      i, name
    end

  let fresh name =
    let name = if name = "" then "var" else name in
    unused name 1 |> snd

  let fresh_id name =
    let name = if name = "" then "var" else name in
    unused name 1 |> fst

  module Key = struct
    type t = var
    let compare = Pervasives.compare
    let to_string t = t
  end

  module Map = Custom_map(Key)
end


module Exp = struct

  open Type.T
  open Sym.T
  open Sym.Op.T

  module T = struct
    type len = exp

    (* TODO: use [Abs 0] for NULL pointers. *)
    (** Not the same as lhost in CIL *)
    and base =
      | Stack of string
        (** (Old) Name and unique id of variable. Note that this way variables from different calls of the same function will be mapped
            to the same base, but not variables from different functions. *)
      | Heap of id * len
      | Abs of intval
         (** An absolute pointer value to deal with cases like:
            {[
            // signal.h:
            typedef void ( *__sighandler_t) (int);
            // signum.h:
            /* Fake signal functions.  */
            #define SIG_ERR ((__sighandler_t) -1)       /* Error return.  */
            #define SIG_DFL ((__sighandler_t) 0)        /* Default action.  */
            #define SIG_IGN ((__sighandler_t) 1)        /* Ignore signal.  */
            ]}
         *)


    and offset_val =
      | Field of string
      | Attr of string
      | Index of int (* Not intval, cause ocaml is really clumsy with that - you can't even subtract it easily *)
      | Flat of len
        (** Flat offsets always measured in bytes *)

    (** Offset value together with offset step *)
    and offset = offset_val * len

    and pos = offset list

    (* FIXME: replace information lens with width option. Possibly use named width or some other
       mechanism to make sure that output is the same on all architectures. The best thing
       is to implement get_len_value by evaluating the length expression in the yices model (with cache).
       But this does rely a bit too much on global state - think again!

       Lens and Ints should have a width field, Vars and Syms should be covered by a width
       annotation. The reason for the difference is that width changes the meaning of
       Int and Len and is necessary to reconstruct the bitstring that they represent,
       but not so for Vars and Syms.

      Do we actually need any width information on vars and syms? It is only used for treating arithmetic expressions
      in the solver, but then you should just add width information to the arithmetic symbols.
    *)

    (* TODO: use GADTs to enforce well-formedness *)

    (**
      The type of symbolic expressions.
      b exp are expressions that evaluate to bitstrings, i exp evaluate to (mathematical) integers.
    *)
    and exp =
      | Int of intval

      | Char of char
        (** An integer with given ascii value. *)

        (* FIXME: have a separate case for literal strings *)
      | String of bitstring
        (** A concrete bitstring in hex representation: each byte corresponds to two characters. *)


      | Var of var

      | Sym of sym * exp list
        (** [Sym s es] is an application of a symbolic function [s(e1, e2, ...)].
          *)

      | Range of exp * len * len
        (** A substring of a given expression with given start position and length.
            A position is a point between two characters or at the beginning or end of the string.
            Given a string of length [l], the first position is [0], the last is [l].
         *)

      | Concat of exp list

      | Len of exp

      | BS of exp * Int_type.t

      | Val of exp * Int_type.t

      | Struct of (exp Str_map.t) * (exp Str_map.t) * len * exp
        (** The first component are the real fields, the second are the crypto attributes.
            The last component is the value of underlying memory at the time the struct has been created.
            This will get removed as soon as I transition to static implementation. *)

      | Array of (exp Int_map.t) * len * len
        (** Contains total length and element length.

            A good alternative is to use native array, but it only makes sense if I know the number of elements in advance.
            This can be done, but I don't see overwhelming advantages and I'm too lazy to change right now,
            thus sticking to a sparse representation.

            At some point might have to use [Map] here, if there is need to generalise indices to arbitrary expressions.
         *)
        (* FIXME: find out how to use Map here *)

      | Ptr of base * pos
        (** Invariants (being reviewed):
            - The offset list is never empty.
            - The sequence of offset steps is decreasing, except that step may be [Unknown] for attribute offsets.
            - An attribute offset always comes last.
            - The first field or context offset is preceded by an index offset.
            - A field, context, or index offset is never preceded by a flat offset.
        *)

      | Unknown
        (** Used in length context only, where the value is not known or is not relevant. *)
        (* FIXME: shouldn't unknown be given an index to prevent it being equal to other unknowns? *)

      | Annotation of annotation * exp

    and annotation =
      | Type_hint of imltype
      | Name of string
  end

  open T
  type t = exp



  (*************************************************)
  (** {1 Show} *)
  (*************************************************)

  let show_types = ref false

  (**
    Does an expression need a bracket in context?

    In expressions "|" binds less tightly than any infix operator.
  *)
  let needs_bracket : exp -> bool = function
    | Concat _ -> true
    | Sym (s, _) when Sym.is_infix s -> true
    | _ -> false

  let is_free_len : len -> bool = function
    | Unknown -> true
    | _ -> false

  let base_to_string : base -> string = function
    | Stack name    -> "stack " ^ name (* ^ "[" ^ string_of_int id ^ "]" *)
    | Heap (id, _)  -> "heap " ^ string_of_int id
    | Abs i         -> "abs " ^ Int64.to_string i

  let rec show_iExp_body t =
    let show_types = !show_types in
    match t with
    | Int ival -> Int64.to_string ival
    | String s ->
      begin try
          let l = String.length s / 2 in
          let hex = List.map (fun i -> String.sub s (2 * i) 2) (0 -- (l - 1)) in
          let asc = List.map (fun s -> Scanf.sscanf s "%x" (fun i -> i)) hex in
          let rep = List.map (fun i -> Char.escaped (Char.chr i)) asc in
          "\"" ^ String.concat "" rep ^ "\""
      with Scanf.Scan_failure _ -> "\"" ^ s ^ "\""
      end

    | Char c -> sprintf "'%s'" (Char.escaped c)

    | Sym (Const s, []) -> s
    | Sym (s, es) when Sym.is_infix s && List.length es > 1 ->
        let bodies = List.map (show_iExp ~bracket:true) es in
        if bodies = [] then Sym.to_string_hum ~show_types s ^ "()"
                       else String.concat (" " ^ Sym.to_string_hum ~show_types s ^ " ") bodies
    | Sym (s, es) ->
        let bodies = List.map show_iExp es in
        Sym.to_string_hum ~show_types s ^ "(" ^ String.concat ", " bodies ^ ")"

    | Range (e, f, l) ->
        let body = show_iExp ~bracket:true e in
        let f_body = show_len f in
        let l_body = show_len l in
        body ^ "{" ^ f_body ^ ", " ^ l_body ^ "}"
    | Concat [] -> "<empty concat>"
    | Concat es ->
        let bodies = List.map show_iExp es in
        let body = String.concat "|" bodies
        in body
    | Ptr (b, pos) ->
        let pos_bodies = List.map (offset_to_string) pos in
        (* let (step_defs, step_body) = show_len step in *)
        let body = "<<" ^ base_to_string b ^ "; " ^ String.concat ", " pos_bodies ^ ">>"
        in body
    | Struct (fields, _, _, _) ->
        let show_field name e =
          let field_body = show_iExp e in
          name ^ ": " ^ field_body
        in
        let field_bodies = fold2list Str_map.fold show_field fields in
        "<{" ^ String.concat "; " field_bodies ^ "}>"
    | Array (cells, len, _) ->
        let show_cell (i, e) =
          let cell_body = show_iExp e in
          string_of_int i ^ " ~> " ^ cell_body
        in
        begin
        match fold2list Int_map.fold (fun i e -> (i, e)) cells with
          | [0, e] -> show_iExp e
          | cells ->
            let cell_bodies = List.map show_cell cells in
            "[|" ^ String.concat "; " cell_bodies ^ "|]"
             (* ^ "<" ^ E.dump len ^ ">" *)
        end

    | Var v -> v

    | Len e -> "len(" ^ show_iExp_body e ^ ")"

    | BS (e, itype) -> sprintf "(%s)^%s" (show_iExp e) (Int_type.to_string itype)

    | Val (e, t) -> sprintf "(%s)_%s" (show_iExp e) (Int_type.to_string t)

    | Annotation (Type_hint t, e) -> show_iExp_body  e  ^ ":" ^ Type.to_string t
    (* | Annotation (Width w, e) -> sprintf "%s<%d>" (show_iExp_body e) w *)
    | Annotation (Name name, e) -> sprintf "%s (* named %s *)" (show_iExp_body e) name

    | Unknown -> "?"

  and show_len = function
    | Unknown -> "?"
    | Int (ival) -> Int64.to_string ival
    | e -> show_iExp e

  and offset_to_string : offset -> string = function (os, step) ->
    let os_body = show_offset_val os in
    let step_body = show_iExp step in
    os_body ^ "(" ^ step_body ^ ")"

  and show_offset_val : offset_val -> string = function
    | Field s -> "field " ^ s
    | Attr s -> "attr " ^ s
    | Index i -> "index " ^ (string_of_int i)
    | Flat e -> show_iExp e

  and show_iExp ?(bracket = false) e =
    match e with
      | Var s -> s
      | e ->
        if bracket && (needs_bracket e) then "(" ^ show_iExp_body e ^ ")"
        else show_iExp_body e

  let list_to_string es =
    show_types := false;
    "[" ^ String.concat "; " (List.map (show_iExp ~bracket:false) es) ^ "]"

  let to_string e =
    show_types := false;
    show_iExp ~bracket:false e

  let dump_list es =
    show_types := true;
    "[" ^ String.concat "; " (List.map (show_iExp ~bracket:false) es) ^ "]"

  let dump e =
    show_types := true;
    show_iExp ~bracket:false e

  (*************************************************)
  (** {1 Traversal} *)
  (*************************************************)

  (**
      Does not include lengths for non-range expressions.
  *)
  let children: t -> t list = function
    | Sym (_, es) -> es
    | Range (e, pos, len) -> [e; pos; len]
    | Concat es -> es
    | Annotation(_, e) -> [e]
    | Len e -> [e]
    | BS (e, _) -> [e]
    | Val (e, _) -> [e]
    | Var _ | Int _ | String _ | Char _ | Struct _ | Array _ | Ptr _ | Unknown -> []


  (**
      Not going into lengths for non-range expressions.
  *)
  let descend: (t -> t) -> t -> t = fun f e ->
    match e with
      | Var _ | String _ | Char _ | Int _ | Unknown -> e
      | Ptr _ -> e
      | Len e -> Len (f e)
      | Val (e, itype) -> Val (f e, itype)
      | BS (e, itype) -> BS (f e, itype)
      | Sym (sym, es) -> Sym (sym, List.map f es)
      | Range (e, pos, len) -> Range  (f e, f pos, f len)
      | Concat es -> Concat (List.map f es)
      | Struct (fields, attrs, len, e_old) -> Struct (Str_map.map f fields, Str_map.map f attrs, f len, e_old)
      | Array (cells, len, step) -> Array (Int_map.map f cells, len, step)
      | Annotation(a, e) -> Annotation(a, f e)

  (*
  let rec replace e1 e2 = function
    | e when e = e1 -> e2
    | e -> descend (replace e1 e2) e
  *)

  let rec vars e =
    match e with
      | Var v -> [v]
      | e -> List.concat_map ~f:vars (children e) |> List.nub

  let rec refcount v = function
    | Var v' when v = v' -> 1
    | e -> List.sum_with (refcount v) (children e)


  (*************************************************)
  (** {1 Map} *)
  (*************************************************)

  module Key = struct
    type t = exp
    let compare = Pervasives.compare
    let to_string = to_string
  end

  module Base =
  struct
    type t = base
    let compare = Pervasives.compare
  end

  module Base_map = Map.Make (Base)
  module Map = Custom_map(Key)
  module Set = Set.Make (Key)

  (*************************************************)
  (** {1 IDs} *)
  (*************************************************)

  let ids = ref Map.empty
  let last_id = ref 0

  let id e =
    match Map.maybe_find e !ids with
      | Some id -> id
      | None ->
        let id = increment last_id in
        ids := Map.add e id !ids;
        id

  let serialize_state c =
    output_value c !ids;
    output_value c !last_id

  let deserialize_state c =
    ids := input_value c;
    last_id := input_value c

  (*************************************************)
  (** {1 Well-formedness} *)
  (*************************************************)

  let typecheck t e_top =
    let module T = Type.T in
    let rec typecheck t e =
      debug "typechecking %s: %s" (to_string e) (Type.to_string t);
      match e, t with
        | Len e, T.Int -> typecheck T.Bitstring e
        | Val (e, _), T.Int -> typecheck T.Bitstring e
        | BS (e, t), t' when Type.subtype (T.Bs_int t) t' && Int_type.is_valid t ->
          typecheck T.Int e
        | Sym (Opaque, [e]), t when Type.subtype t T.Bitstringbot ->
          typecheck t e
        (* An escape hatch for functions which actually return Bs_int types or bools, like
           check_key(). *)
        | Sym (((Fun _ | Nondet_fun _ ) as sym), es), t
          when Type.subtype t T.Bitstringbot ->
          List.iter2 typecheck (Sym.argument_types sym) es
        | Sym (sym, es), t when Type.subtype (Sym.result_type sym) t ->
          List.iter2 typecheck (Sym.argument_types sym) es
        (* Not too strict here, because some ranges are interpreted as bitstring
           integers. *)
        | Range (e, pos, len), t when Type.subtype t T.Bitstring ->
          typecheck T.Bitstring e;
          typecheck T.Int pos;
          typecheck T.Int len
        | Concat es, T.Bitstring ->
          List.iter (typecheck T.Bitstring) es
        | Struct (fields, attrs, len, e_old), T.Bitstring ->
          Str_map.iter (fun _ e -> typecheck T.Bitstring e) fields;
          Str_map.iter (fun _ e -> typecheck T.Bitstring e) attrs
        | Array (cells, len, step), T.Bitstring ->
          Int_map.iter (fun _ e -> typecheck T.Bitstring e) cells
        | Annotation(_, e), t  -> typecheck t e
        | Ptr _, t when Type.subtype T.Ptr t  -> ()
          (* This is very lax because we can't tell the width of the variable here,
             so we trust the type as long as it is a subtype of bitstring. *)
        | Var _, t when Type.subtype t T.Bitstring -> ()
        | String _, T.Bitstring
        | Int _, T.Int
        | Char _, T.Int
        | Unknown, T.Bitstring -> ()
        | e, _ -> fail "typecheck: wrong type %s of expression %s in %s" (Type.to_string t) (to_string e) (to_string e_top)
    in
    push_debug "E.typecheck";
    typecheck t e_top;
    pop_debug "E.typecheck"

  let rec type_of = function
    | Char _
    | Int _
    | Len _
    | Val _ -> Type.Int

    | Var _
    | String _
    | Concat _
    | Range _
    | Array _
    | Struct _
    | Unknown -> Bitstring

    | Ptr _ -> Type.Ptr

    | BS (_, itype) -> Bs_int itype

    | Sym (Opaque, [e]) -> type_of e

    | Sym (sym, _) -> Sym.result_type sym

    | Annotation (_, e) -> type_of e

  let itype_exn = function
    | Sym (sym, _) as e ->
      begin match Sym.result_type sym with
        | Bs_int itype -> itype
        | t -> fail "sym result type not Bs_int: (%s : %s)" (to_string e) (Type.to_string t)
      end
    | String s -> (`Unsigned, String.length s / 2)
    | BS (_, itype) (* | Val (_, itype) *) -> itype
    | e -> fail "expression itype undefined: %s" (to_string e)

  (*************************************************)
  (** {1 Misc} *)
  (*************************************************)


  let concat : exp list -> exp = fun es -> Concat es

  let range : exp -> len -> len -> exp = fun e f l -> Range (e, f, l)

  let var v = Var v

  let int i = Int (Int64.of_int i)

  let zero : exp = Int 0L
  let one  : exp = Int 1L
  let zero_byte signedness = BS (Int 0L, (signedness, 1))

  let sum = function
    | [] -> zero
    | [e] -> e
    | es -> Sym (Plus_int (List.length es), es)

  let prod = function
    | [] -> one
    | [e] -> e
    | es -> Sym (Mult_int (List.length es), es)

  let conj es = Sym (And (List.length es), es)
  let disj es = Sym (Or  (List.length es), es)

  let rec is_concrete : exp -> bool = function
    | Var _ -> false
    | e -> List.for_all is_concrete (children e)

  let is_length : exp -> bool = fun e ->
    match e with
    | Len _ -> true
    | _ -> false

  let is_integer : exp -> bool = function
    | Int _ -> true
    | _     -> false

  let is_string : exp -> bool = function
    | String _ -> true
    | _     -> false

  let rec contains_sym s = function
    | Sym (s', _) when s' = s -> true
    | e -> List.exists (contains_sym s) (children e)

  let rec replace es es' e =
    match List.find_index ((=) e) es with
      | Some i -> List.nth es' i
      | None -> descend (replace es es') e

  let subst vs es e =
    replace (List.map (fun v -> Var v) vs) es e

  let subst_v vs vs' e = subst vs (List.map var vs') e

  let rec remove_annotations = function
    | Annotation(_, e) -> remove_annotations e
    | e -> descend remove_annotations e

  (* TODO: Consider making this part of Solver.rewrite *)
  let rec truth = function
    | Sym (BS_of_truth _, [e]) -> e
    | BS (Int i, _) ->
      if i = 0L then Sym (Not, [Sym (True, [])]) else Sym (True, [])
    | Ptr _ as p -> Sym (Truth_of_bs, [p])
    | Sym (Op (LAnd, _), es) -> conj (List.map truth es)
    | Sym (Op (LOr, _), es) -> disj (List.map truth es)
    | Sym (Op (LNot, _), [e]) -> Sym (Not, [truth e])
    | e when type_of e = Bool -> e
    | Sym (Op (op, (ts, t)), es) when Sym.Op.is_binary_comparison op ->
      Sym (Op (op, (ts, Bool)), es)
    | Sym (Cmp, [e1; e2]) -> Sym (Not, [Sym (Bs_eq, [e1; e2])])
    | Var v as e -> Sym (Truth_of_bs, [e])
    | Sym (Fun _, _) as e -> Sym (Truth_of_bs, [e])
    | e -> fail "Exp.truth: unexpected: %s" (to_string e)

  let len e = Len e
end


module Pat = struct
  open Sym.T

  module T = struct
    type pat =
      | VPat of var
      | FPat of sym * pat list
      | Underscore
  end

  open T
  type t = T.pat

  let rec vars = function
    | FPat (_, pats) -> List.concat_map vars pats
    | VPat v -> [v]
    | Underscore -> []

  let rec dump = function
    | VPat v -> v
    | FPat (f, ps) -> Sym.to_string f ^ "(" ^ String.concat ", " (List.map dump ps) ^ ")"
    | Underscore -> "_"
end


module Stmt = struct

  open Exp.T
  open Pat.T

  module T = struct
    type stmt =
      | Let of pat * exp
        (** [Test e; P = if e then P else 0] *)
      | Aux_test of exp
      | Test of exp
      | Test_eq of exp * exp
      | Assume of exp
      | In of var list
      | Out of exp list
      | New of var * imltype
      | Event of string * exp list
      | Yield
      | Comment of string
  end

  type t = T.stmt
  open T

  let to_string t =
    match t with
      | In [v] ->
        "in(c, " ^ v ^ ");";

      | In vs ->
        "in(c, (" ^ String.concat ", " vs ^ "));";

      | New (v, t) ->
        "new " ^ v ^ ": " ^ Type.to_string t ^ ";"

      | Out [e] ->
        "out(c, " ^ Exp.show_iExp e ^ ");";

      | Out es ->
        "out(c, (" ^ String.concat ", " (List.map Exp.show_iExp es) ^ "));";

      | Test_eq (e1, e2) ->
        "ifeq " ^ Exp.show_iExp e1 ^ " = " ^ Exp.show_iExp e2 ^ " then "

      | Test e ->
        "if " ^ Exp.show_iExp e ^ " then "

      | Aux_test e ->
        "ifaux " ^ Exp.show_iExp e ^ " then "

      | Assume e ->
        Printf.sprintf "assume %s in" (Exp.show_iExp e)

      | Event (name, es) ->
        "event " ^ name ^ "(" ^ String.concat ", " (List.map Exp.show_iExp es) ^ ");"

      | Let (pat, e) ->
        "let " ^ Pat.dump pat ^ " = " ^ Exp.show_iExp e ^ " in"

      | Yield -> "yield ."

      | Comment s -> sprintf "(* %s *)" s


  let children: t -> exp list = function
    | Let (_, e) -> [e]
    | Aux_test e -> [e]
    | Test e -> [e]
    | Test_eq (e1, e2) -> [e1; e2]
    | Assume e -> [e]
    | In vs -> []
    | Out es -> es
    | New (v, t) -> []
    | Event (ev, es) -> es
    | Yield -> []
    | Comment _ -> []


  let descend: (exp -> exp) -> t -> t = fun f -> function
    | Let (pat, e) -> Let(pat, f e)
    | Aux_test e -> Aux_test (f e)
    | Test e -> Test (f e)
    | Test_eq (e1, e2) -> Test_eq (f e1, f e2)
    | Assume e -> Assume (f e)
    | In vs -> In vs
    | Out es -> Out (List.map f es)
    | New (v, t) -> New (v, t)
    | Event (ev, es) -> Event (ev, List.map f es)
    | Yield -> Yield
    | Comment s -> Comment s

  let subst vs es t = descend (Exp.subst vs es) t

  let vars s = List.concat_map ~f:Exp.vars (children s)

  let remove_annotations t = descend (Exp.remove_annotations) t
end

open Pat.T
open Stmt.T

type iml = Stmt.t list

type t = iml

let map f p = List.map (Stmt.descend f) p
let iter f p = List.iter (fun s -> List.iter f (Stmt.children s)) p

let refcount v p = List.sum_with (fun s -> List.sum_with (Exp.refcount v) (Stmt.children s)) p

let vars p = List.concat_map ~f:Stmt.vars p

let rec free_vars = function
  | Let (VPat v, e) :: p ->
    List.remove v (Exp.vars e @ free_vars p)
  | New (v, t) :: p ->
    List.remove v (free_vars p)
  | In vs :: p ->
    List.diff (free_vars p) vs
  | s :: p ->
    Stmt.vars s @ free_vars p
  | [] -> []

let rec subst vs es =

  let subst_under_binding p v =
    let vs, es =
         List.combine vs es
      |> List.filter ~f:(fun (v', e) ->
          if v' = v then false
          else if List.mem v (Exp.vars e) && refcount v' p > 0 then
            fail "subst: variable %s captures a variable in substitution %s ~> %s" v v' (Exp.to_string e)
          else true)
      |> List.split
    in
    subst vs es p
  in

  function
  | [] -> []
  | s :: p ->
    let s = Stmt.subst vs es s in
    match s with
      | New (v, _) ->
        s :: subst_under_binding p v
      | Let (pat, _) ->
        let vs' = Pat.vars pat in
        s :: List.fold_left subst_under_binding p vs'
      | In vs' ->
        s :: List.fold_left subst_under_binding p vs'
      | s -> s :: subst vs es p

let subst_v vs vs' e =  subst vs (List.map Exp.var vs') e

let to_string p =
  String.concat "\n" (List.map Stmt.to_string p) ^ "\n"


(* 1180 lines *)

