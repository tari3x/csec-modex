(*
  Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
  This file is distributed as part of csec-tools under a BSD license.
  See LICENSE file for copyright notice.
*)

open Common

open Printf

(*************************************************)
(** {1 Types} *)
(*************************************************)

module Ptr = Int64
module Ptr_map = Custom_map (struct include Ptr let to_string = to_string end)
module Int_map = Custom_map (struct type t = int
                                    let compare = Pervasives.compare
                                    let to_string = string_of_int end)
module Str_map = Custom_map (struct include String let to_string s = s end)

(** Hex representation: each byte corresponds to two characters. Length is the
    number of bytes. *)
type bitstring = string

type intval = int64
type ptr    = int64

type id = int

module Kind = struct
  type 'a t =
  | Bool : bool t
  | Int : int t
  | Bitstring : bitstring t

  let equal_kind (type a) (type b) (t1 : a t) (t2 : b t) : (a, b) Type_equal.t option =
    let open Type_equal in
    match t1, t2 with
    | Bitstring, Bitstring -> Some Equal
    | Bool, Bool           -> Some Equal
    | Int, Int             -> Some Equal
    | _                    -> None

  let to_string (type a) (t : a t) =
    match t with
    | Bool -> "Bool"
    | Int -> "Int"
    | Bitstring -> "Bitstring"
end

module Type = struct

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
      let s = String.trim s in
      let toks = Str.split (Str.regexp "[][,]") s in
      match toks with
      | ["u"; w] ->  (`Unsigned, int_of_string w)
      | ["s"; w] ->  (`Signed,   int_of_string w)
      | _ -> fail "Int_type.of_string: %s" s

    let invariant (_, w) =
      if w = 0
      then fail "Int_type: width cannot be 0"

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

    let signedness (s, _) = s
    let width (_, w) = w
    let create s w =
      let t = (s, w) in
      invariant t;
      t
  end

  type 'a t =
  | Bitstringbot : bitstring t               (** All strings and bottom. *)
  | Bitstring : bitstring t                  (** All machine-representable strings *)
  | Fixed : int -> bitstring t               (** All strings of a given length *)
  | Bounded : int -> bitstring t             (** All strings up to a given length *)
  | Ptr : bitstring t
  | Bs_int : Int_type.t -> bitstring t
  (* A named type with an optional type definition. Named (_, None) may not contain
     bottom. *)
  | Named : string * bitstring t option -> bitstring t
  | Bool : bool t
  | Int : int t

  type 'a imltype = 'a t

  module Kind = Kind

  let kind (type a) (t : a t) : a Kind.t =
    match t with
    | Bitstringbot      -> Kind.Bitstring
    | Bitstring         -> Kind.Bitstring
    | Fixed _           -> Kind.Bitstring
    | Bounded _         -> Kind.Bitstring
    | Ptr               -> Kind.Bitstring
    | Bs_int _          -> Kind.Bitstring
    | Named _           -> Kind.Bitstring
    | Bool              -> Kind.Bool
    | Int               -> Kind.Int

  type any = Any : 'a t -> any

  let of_string_bitstring s =
    try Bs_int (Int_type.of_string s)
    with _ ->
      match List.map ~f:String.trim (Str.bounded_split (Str.regexp "_") s 3) with
      | ["bitstringbot"]     -> Bitstringbot
      | ["bitstring"]        -> Bitstring
      | ["bitstring"; name]  -> Named (name, Some Bitstring)
      | ["fixed"; n]         -> Fixed (int_of_string n)
      | ["fixed"; n; name]   -> Named (name, Some (Fixed (int_of_string n)))
      | ["bounded"; n]       -> Bounded (int_of_string n)
      | ["bounded"; n; name] -> Named (name, Some (Bounded (int_of_string n)))
      | ["ptr"]              -> Ptr
      | ["bool"]             -> fail "Unexpected in Type.of_string_bitstring: bool"
      | _                    -> Named (s, None)

  let of_string = function
    | "bool" -> Any Bool
    | s -> Any (of_string_bitstring s)

  let rec to_string : type a. a t -> string = function
    | Bitstringbot         -> "bitstring"
    | Bitstring            -> "bitstring"
    | Fixed n              -> "fixed_" ^ string_of_int n
    | Bounded n            -> "bounded_" ^ string_of_int n
    | Bool                 -> "bool"
    | Int                  -> "int"
    | Ptr                  -> "ptr"
    | Bs_int itype         -> Int_type.to_string itype
    | Named (name, Some t) -> to_string t ^ "_" ^ name
    | Named (name, None)   -> name

  let rec strip_name : type a. a t -> a t = function
    | Named (_, Some t) -> strip_name t
    | t -> t

  let subtype (type a) (t : a t) (t' : a t) =
    match strip_name t, strip_name t' with
    | Int, Int -> true
    | Bool, Bool -> true
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

module Fun_type = struct
  type ('a, 'b) t = 'a Type.t list * 'b Type.t

  type any = Any : (bitstring, 'b) t -> any

  let to_string (ts, t) =
    let ts = List.map ~f:Type.to_string ts in
    let t = Type.to_string t in
    sprintf "%s -> %s" (String.concat " * " ts) t

  let of_string s : any =
    if not (Str.string_match (Str.regexp "\\(.*\\) -> \\(.*\\)") s 0)
    then begin
      let Type.Any t = Type.of_string s in
      Any ([], t)
    end
    else try begin
      (* Call matched_group before calling split (which is also called in
         Type.of_string). *)
      let t = Str.matched_group 2 s in
      let ts =
        Str.matched_group 1 s
        |> Str.split (Str.regexp "\\*")
        |> List.map ~f:Type.of_string_bitstring
      in
      let Type.Any t = Type.of_string t in
      Any (ts, t)
    end with
      e -> fail "Op_type.of_string: %s: %s" s (Printexc.to_string e)

  let arity (ts, _) = List.length ts

  let kind (_, t) = Type.kind t
end

module Sym = struct
  open Type

  module Cmp = struct
    type t = Lt | Gt | Le | Ge | Eq | Ne
  end

  module Arith = struct
    type t = Plus of int | Minus | Mult of int | Div | Neg

    let is_infix = function
      | Neg -> false
      | Plus _ | Minus | Mult _ | Div -> true

    let arity = function
      | Plus n | Mult n -> n
      | Minus | Div -> 2
      | Neg -> 1
  end

  module Logical = struct
    type t = And of int | Or of int | Not | Implies | True | Eq

    let is_infix = function
      | And _ | Or _ | Implies | Eq -> true
      | Not | True -> false

    let arity = function
      | And n | Or n -> n
      | Implies | Eq -> 2
      | Not -> 1
      | True -> 0
  end

  module Op = struct
    open Cmp
    open Arith

    type t =
      BNot                                (** Bitwise complement (~) *)
    | LNot                                (** Logical Not (!) *)

    | Op_arith of Arith.t                 (** arithmetic + *)
    | Op_cmp of Cmp.t                     (** <  (arithmetic comparison) *)

    | Plus_PI                              (** pointer + int *)

    | Minus_PI                             (** pointer - int *)
    | Minus_PP                             (** pointer - pointer *)
    | Mod                                  (** % *)

    | Shiftlt                              (** shift left *)
    | Shiftrt                              (** shift right *)

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

    let to_string = function
      | BNot -> "~"  |  LNot -> "!"

      | Mod     -> "%"   | BAnd    ->  "&"   | BOr   -> "BOR"  | BXor  -> "XOR"
      | Shiftlt -> "<<"  | Shiftrt ->  ">>"  | LAnd  -> "&&"   | LOr   -> "LOR"

      | Op_arith arith ->
        begin match arith with
        | Neg -> "neg"
        | Plus _  -> "+"
        | Minus ->  "-"
        | Mult _ -> "*"
        | Div -> "/"
        end

      | Op_cmp cmp ->
        begin match cmp with
        | Eq -> "=="
        | Ne ->  "!="
        | Gt -> ">"
        | Le -> "<="
        | Lt -> "<"
        | Ge ->  ">="
        end

      | Plus_PI  -> "PlusPI"
      | Minus_PI -> "MinusPI"
      | Minus_PP -> "MinusPP"

      | Cast_to_int -> "CastToInt"
      | Cast_to_ptr -> "CastToPtr"
      | Cast_to_other -> "CastToOther"

    let of_string = function
      | "+" -> Op_arith (Plus 2)
      | "-" -> Op_arith Minus
      | "*" -> Op_arith (Mult 2)
      | "/" -> Op_arith Div
      | "neg" -> Op_arith Neg
      | "%" -> Mod
      | "~" -> BNot     | "!" -> LNot
      | "&" -> BAnd     | "BOR" -> BOr  | "XOR" -> BXor
      | "<<" -> Shiftlt | ">>" -> Shiftrt | "&&" -> LAnd  | "LOR" -> LOr
      | "==" -> Op_cmp Eq
      | "!=" -> Op_cmp Ne
      | ">" -> Op_cmp Gt
      | "<=" -> Op_cmp Le
      | "<" -> Op_cmp Lt
      | ">=" -> Op_cmp Ge

      | "PlusPI" -> Plus_PI
      | "MinusPP" -> Minus_PP
      | "CastToInt" -> Cast_to_int
      | "CastToPtr" -> Cast_to_ptr
      | "CastToOther" -> Cast_to_other

      | s -> fail "Op.to_string: %s" s

    let is_unary = function
      | Op_arith Neg
      | BNot
      | LNot -> true
      | _ -> false
  end

  type name = string
  type arity = int
  type invocation_id = int

  type ('a, 'b) t =
  (* TODO: should take Int_type.t *)
  | Op : Op.t * (bitstring, bitstring) Fun_type.t -> (bitstring, bitstring) t

  | Bs_eq : (bitstring, bool) t
  (** Bitstring comparison, works on bottoms too. *)
  | Cmp : (bitstring, bitstring) t
  (** Bitstring comparison returning bitstring result.  Bs_eq(x, y) = Truth(Cmp(x, y)) *)

  | Int_op : Arith.t -> (int, int) t
  | Int_cmp : Cmp.t -> (int, bool) t

  | Logical : Logical.t -> (bool, bool) t

  | Ptr_len : (_, int) t

  | Cast : bitstring Type.t * bitstring Type.t -> (bitstring, bitstring) t

  | Ztp : (bitstring, bitstring) t
    (**
       Zero-terminated prefix - up to but not including the first 0.
       Bottom if the bitstring does not contain zero.
    *)

  | Ztp_safe : (bitstring, bitstring) t
  (**
     Same as Ztp, but returns the argument unchanged instead of bottom.
  *)

  | Replicate : (bitstring, bitstring) t
  (** Field_offset is only there for CSur, in which network data is treated as a
      structure directly. We don't try to prove safety of this. *)
  | Field_offset : string -> (_, int) t
  | Opaque : ('a, 'a) t
  (** Used only in Solver *)
  | Defined : ('a, bool) t
  | In_type : 'a Type.t -> ('a, bool) t
  (** Defined is the same as (In_type Bitstring) *)

  | Truth_of_bs : (bitstring, bool) t
  | BS_of_truth : Int_type.width -> (bool, bitstring) t

  (* The yices versions of len and val, see thesis. *)
  | Len_y : (bitstring, int) t
  | Val_y : Int_type.t -> (bitstring, int) t

  (* FIXME: unify with unknown? *)
  | Undef : invocation_id -> (_, bitstring) t
  (** With a tag to distinguish different undefs.
      FIXME: Do not create explicitly, use Expr.undef. *)

  (* We assume that a boolean function cannot generate a bottom from non-bottom
     arguments. *)
  | Fun : name * (arity * 'b Kind.t) -> (bitstring, 'b) t

  type ('a, 'b) sym = ('a, 'b) t

  type bfun = (bitstring, bitstring) t

  type any = Any : ('a, 'b) t -> any
  let any s = Any s

  let is_infix (type a) (type b) (t : (a, b) t) =
    match t with
    | Op (op, _) -> not (Op.is_unary op)

    | Int_op arith -> Arith.is_infix arith

    | Int_cmp _ -> true

    | Logical op -> Logical.is_infix op

    | Bs_eq -> true

    | _ -> false

  let to_string_hum (type a) (type b) ?(show_types = true) (t : (a, b) t) =
    match t with
    | Op (op, t) ->
      if show_types
      then sprintf "(%s : %s)" (Op.to_string op) (Fun_type.to_string t)
      else sprintf "%s" (Op.to_string op)

    | Int_cmp cmp ->
      let open Cmp in
      begin match cmp with
      | Eq -> "="
      | Ne -> "<>"
      | Ge -> ">="
      | Gt -> ">"
      | Le -> "<="
      | Lt -> "<"
      end

    | Int_op op ->
      let open Arith in
      begin match op with
      | Plus _ -> "+"
      | Minus -> "-"
      | Mult _ -> "*"
      | Neg -> "-"
      | Div -> "/"
      end

    | Logical op ->
      let open Logical in
      begin match op with
      | Implies -> "=>"
      | And _ -> "/\\"
      | Or _ -> "\\/"
      | Not -> "¬"
      | True -> "True"
      | Eq -> "="
      end

    | Bs_eq -> "="
    | Ptr_len -> "ptrLen"

    | Cast (t, t') -> "cast_" ^ Type.to_string t ^ "_" ^ Type.to_string t'

    | Ztp -> "Ztp"
    | Ztp_safe -> "ZtpSafe"

    | Truth_of_bs -> "Truth_of_bs"
    | BS_of_truth width -> sprintf "Bs_of_truth[%d]" width

    | Len_y -> "Len_y"
    | Val_y t -> sprintf "Val_y%s" (Int_type.to_string t)

    | Cmp -> "Cmp"

    | Replicate -> "Replicate"
    | Field_offset s -> sprintf "Field_offset[%s]" s
    | Opaque -> "Opaque"
    | Defined -> "Defined"
    | In_type t -> sprintf "InType[%s]" (Type.to_string t)
    | Undef i -> Printf.sprintf "Undef[%d]" i
    | Fun (s, _) ->
      (* CR-someday: enforce this *)
      (*

        let c = String.get s 0 in
        if Char.lowercase c <> c
        then fail "function names must start with lowercase letters: %s" s;
      *)
      sprintf "%s" s

  let to_string t = to_string_hum t

  let cv_declaration f (ts, t) =
    to_string f ^ "(" ^ String.concat ", " (List.map ~f:Type.to_string ts) ^ "): " ^ Type.to_string t

  let of_string s =
    if Str.string_match (Str.regexp "(\\(.+\\) *: \\(.+\\))") s 0
    then begin
      let sym = String.trim (Str.matched_group 1 s) in
      let t = Str.matched_group 2 s in
      let Fun_type.Any t = Fun_type.of_string t in
      let kind = Fun_type.kind t in
      match Option.try_with (fun () -> Op.of_string sym) with
      | None ->
        (* CR-someday: enforce this *)
        (*
        let c = String.get sym 0 in
        if Char.lowercase c <> c
        then fail "function names must start with lowercase letters: %s" sym;
        *)
        Any (Fun (sym, (Fun_type.arity t, kind)))
      | Some op ->
        match kind with
        | Kind.Bitstring -> Any (Op (op, t))
        | _ -> fail "Sym.of_string: %s" s
    end
    else if (Str.string_match (Str.regexp "\\(.+\\)/\\([0-9]+\\)") s 0)
    then begin
      let sym = String.trim (Str.matched_group 1 s) in
      let n = int_of_string (Str.matched_group 2 s) in
      match sym with
      | "=" -> Any Bs_eq
      | "EqInt" -> Any (Int_cmp Cmp.Eq)
      | "ptrLen" -> Any Ptr_len
      | "ztp" -> Any Ztp
      | "ztpSafe" -> Any Ztp_safe
      | "cmp" -> Any Cmp
      | "truth_of_bs" -> Any Truth_of_bs
      | s when Str.string_match (Str.regexp "bs_of_truth\\[\\(.+\\)\\]") s 0 ->
        let width = int_of_string (Str.matched_group 1 s) in
        Any (BS_of_truth width)
      | s ->
        Any (Fun (s, (n, Kind.Bitstring)))
    end
    else fail "Sym.of_string: %s" s

  let may_fail (type a) (type b) (t : (a, b) t) =
    match t with
    | Ztp -> true

    | Op _ -> true
    | Val_y _ -> true

    | Field_offset _ -> false

    | Int_cmp _ -> false

    | Int_op _ -> false

    | Logical _ -> false

    | Bs_eq -> false
    | Ptr_len -> false

    | Cast _ -> false

    | Ztp_safe -> false

    | Truth_of_bs -> false
    | BS_of_truth _ -> false
    | Cmp -> false

    | Len_y -> false

    | Replicate -> false
    | Defined -> false
    | In_type _ -> false
    | Undef _ -> false
    | Opaque -> false

    | Fun (_, (_, kind)) ->
      begin match kind with
      | Kind.Bool -> false
      | _ -> true
      end

  let never_fails (type a) (type b) (t : (a, b) t) =
    match t with
    | Bs_eq -> true
    | In_type _ -> true

    | Logical _ -> true

    | Defined -> true

    | Field_offset _ -> true

    | Op _ -> false
    | Ztp -> false
    | Fun _ -> false

    | Int_cmp _ -> false
    | Int_op _ -> false

    | Ptr_len -> false

    | Cast _ -> false

    | Ztp_safe -> false

    | Truth_of_bs -> false
    | BS_of_truth _ -> false
    | Cmp -> false

    | Len_y -> false
    | Val_y _ -> false

    | Replicate -> false
    | Undef _ -> false
    | Opaque -> false

  let result_itype (type a) (type b) (t : (a, b) t) : Int_type.t option =
    match t with
    | BS_of_truth width -> Some (Int_type.create `Unsigned width)
    | Cast (_, Bs_int t) -> Some t
    | Op (_, (_, Bs_int t)) -> Some t
    | _ -> None

  let arity  (type a) (type b) (t : (a, b) t) =
   match t with
    | Int_cmp _ -> 2

    | Int_op op -> Arith.arity op

    | Logical op -> Logical.arity op

    | BS_of_truth _ -> 1

    | Undef _ -> 0
    | Ptr_len -> 0

    | Truth_of_bs -> 1
    | Ztp -> 1
    | Ztp_safe -> 1
    | Field_offset _ -> 0
    | Opaque -> 1
    | In_type _ -> 1
    | Len_y -> 1
    | Defined -> 1

    | Cmp -> 2
    | Bs_eq -> 2

    | Replicate -> 2

    | Cast _ -> 1

    | Val_y _ -> 1

    | Fun (_, (arity, _)) -> arity

    | Op (_, (ts, _)) -> List.length ts

  module Key = struct
    type 'a t = (bitstring, 'a) sym
    module Kind = Kind

    let kind (type a) (sym : a t) : a Kind.t =
      match sym with
      | Fun (_, (_, kind)) -> kind
        (* Can be added if necessary. *)
      | sym -> fail "No kind for %s" (to_string sym)

    let to_string = to_string
  end

  module Map_any = Common.Map_any (Kind) (Key)

  module Map (Value : GADT) = struct
    type 'a sym = (bitstring, 'a) t
    module type Map = sig
      type kind
      module Ops : Custom_map with type key = kind sym
      val value : kind Value.t Ops.t
    end
    type 'a t = (module Map with type kind = 'a)

    let mem (type a) sym t =
      let module M = (val t : Map with type kind = a) in
      M.Ops.mem sym M.value

    let add (type a) sym value t : a t =
      let module M = (val t : Map with type kind = a) in
      (module struct
        type kind = a
        module Ops = M.Ops
        let value = Ops.add sym value M.value
      end)

    let maybe_find (type a) sym t =
      let module M = (val t : Map with type kind = a) in
      M.Ops.maybe_find sym M.value

    let find (type a) sym t =
      let module M = (val t : Map with type kind = a) in
      M.Ops.find sym M.value

    let of_list (type a) xs : a t =
      (module struct
        type kind = a
        module Key = struct
          type t = kind sym
          let compare = Pervasives.compare
          let to_string = to_string
        end
        module Ops = Custom_map(Key)
        let value = Ops.of_list xs
      end)

    let to_list (type a) t =
      let module M = (val t : Map with type kind = a) in
      M.Ops.to_list M.value

    let keys t =
      to_list t |> List.map ~f:fst

    let values t =
      to_list t |> List.map ~f:snd

    (* Looks like with this implementation empty needs to take unit. *)
    let empty () = of_list []

    (* The downside of this implementation is that we can't prove that Ops in
       two maps are the same, so we need to rebuild the map from scratch. That's
       where Core would be good *)
    let disjoint_union (type a) ts : a t =
      match ts with
      | [] -> empty ()
      | t :: _ as ts ->
        let module M = (val t : Map with type kind = a) in
        let bindings = List.map ts ~f:to_list |> List.concat in
        (module struct
          type kind = a
          module Ops = M.Ops
          let value =
            List.fold_left bindings ~init:Ops.empty ~f:(fun map (sym, value) ->
              if Ops.mem sym map
              then fail "Map.disjoint_union: maps are not disjoint, both contain %s"
                (to_string sym)
              else Ops.add sym value map)
        end)

    let iter (type a) ~f t =
      let module M = (val t : Map with type kind = a) in
      M.Ops.iter f M.value

    let filter (type a) ~f t : a t =
      let module M = (val t : Map with type kind = a) in
      (module struct
        type kind = a
        module Ops = M.Ops
        let value = Ops.filter f M.value
      end)
  end
end

module Var = struct
  type t = string
  type var = t

  let used_names = ref []

  let unfresh names =
    used_names := !used_names @ names

  let reset_fresh () =
    used_names := []

  let rec unused stem i =
    let name = stem ^ (string_of_int i) in
    if List.mem name ~set:!used_names then
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
    type t = string
    let compare = Pervasives.compare
    let to_string t = t
  end

  module Map = Custom_map(Key)
end


module Exp = struct
  module Core_map = Map
  open Type
  open Sym

  type var = Var.t

  type 'a t =
  | Int : intval -> int t

  | Char : char -> int t
  (** An int with given ascii value. *)

  | String : char list -> bitstring t

  | Var : Var.t * 'a Kind.t -> 'a t

  | Sym : ('a, 'b) Sym.t * 'a t list -> 'b t
  (** [Sym s es] is an application of a symbolic function [s(e1, e2, ...)].  *)

  | Range : bitstring t * int t * int t -> bitstring t
  (** A substring of a given expression with given start position and length.  A
      position is a point between two characters or at the beginning or end of the
      string.  Given a string of length [l], the first position is [0], the last is
      [l].  *)

  | Concat : bitstring t list -> bitstring t

  | Len : bitstring t -> int t

  | BS : int t * Int_type.t -> bitstring t

  | Val : bitstring t * Int_type.t -> int t

  | Struct
      :  (bitstring t Str_map.t) * (bitstring t Str_map.t) * int t * bitstring t
      -> bitstring t
  (** The first component are the real fields, the second are the crypto attributes.
      The last component is the value of underlying memory at the time the struct
      has been created.  This will get removed as soon as I transition to static
      implementation. *)

  | Array : (bitstring t Int_map.t) * int t * int t -> bitstring t
  (** Contains total length and element length.

      A good alternative is to use native array, but it only makes sense if I know the
      number of elements in advance.  This can be done, but I don't see overwhelming
      advantages and I'm too lazy to change right now, thus sticking to a sparse
      representation.

      At some point might have to use [Map] here, if there is need to generalize indices
      to arbitrary expressions.  *)
    (* FIXME: find out how to use Map here *)

  | Ptr : base * pos -> bitstring t
  (** Invariants (being reviewed):

      - The offset list is never empty.

      - The sequence of offset steps is decreasing, except that step may be
      [Unknown] for attribute offsets.

      - An attribute offset always comes last.

      - The first field or context offset is preceded by an index offset.

      - A field, context, or index offset is never preceded by a flat offset.
  *)

  (* FIXME: get rid of Unknown *)
  | Unknown : 'a Kind.t -> 'a t
  | Annotation : 'a annotation * 'a t -> 'a t

  and 'a annotation =
  | Type_hint : 'a Type.t -> 'a annotation
  | Name of string
  (* | Width of width *)

    (** Not the same as lhost in CIL *)
  and base =
  | Stack of string
    (** (Old) Name and unique id of variable. Note that this way variables from
        different calls of the same function will be mapped to the same base, but not
        variables from different functions. *)
  | Heap of id * int t
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
    (* For now flat offsets are true ints, unlike in the thesis *)
  | Flat of int t
    (** Flat offsets always measured in bytes *)

    (** Offset value together with offset step *)
  and offset = offset_val * int t

  and pos = offset list

  type 'a exp = 'a t

  type iterm = int t
  type bterm = bitstring t
  type fact = bool t

  type any = Any : 'a t -> any

  (*************************************************)
  (** {1 Show} *)
  (*************************************************)

  let show_types = ref false

  (**
    Does an expression need a bracket in context?

    In expressions "|" binds less tightly than any infix operator.
  *)
  let needs_bracket : type a. a t -> bool = function
    | Concat _ -> true
    | Sym (s, _) when Sym.is_infix s -> true
    | _ -> false

  let base_to_string : base -> string = function
    | Stack name    -> "stack " ^ name (* ^ "[" ^ string_of_int id ^ "]" *)
    | Heap (id, _)  -> "heap " ^ string_of_int id
    | Abs i         -> "abs " ^ Int64.to_string i

  let rec show_iexp_body : type a. a t -> string = fun t ->
    let show_types = !show_types in
    match t with
    | Int ival -> Int64.to_string ival
    | String bs ->
      let rep = List.map bs ~f:Char.escaped in
      "\"" ^ String.concat "" rep ^ "\""
    | Char c -> sprintf "'%s'" (Char.escaped c)
    | Sym (s, es) when Sym.is_infix s && List.length es > 1 ->
      let bodies = List.map ~f:(show_iexp ~bracket:true) es in
      if bodies = [] then Sym.to_string_hum ~show_types s ^ "()"
      else String.concat (" " ^ Sym.to_string_hum ~show_types s ^ " ") bodies
    | Sym (s, es) ->
      let bodies = List.map ~f:show_iexp es in
      Sym.to_string_hum ~show_types s ^ "(" ^ String.concat ", " bodies ^ ")"

    | Range (e, f, l) ->
      let body = show_iexp ~bracket:true e in
      let f_body = show_len f in
      let l_body = show_len l in
      body ^ "{" ^ f_body ^ ", " ^ l_body ^ "}"
    | Concat [] -> "<empty concat>"
    | Concat es ->
      let bodies = List.map ~f:show_iexp es in
      let body = String.concat "|" bodies
      in body
    | Ptr (b, pos) ->
      let pos_bodies = List.map ~f:(offset_to_string) pos in
        (* let (step_defs, step_body) = show_len step in *)
      let body = "<<" ^ base_to_string b ^ "; " ^ String.concat ", " pos_bodies ^ ">>"
      in body
    | Struct (fields, attrs, len, _) ->
      let show_field name e ~sep =
        sprintf "%s%s%s" name sep (show_iexp e)
      in
      let fields = fold2list Str_map.fold (show_field ~sep:": ") fields in
      let attrs = fold2list Str_map.fold (show_field ~sep:" ~> ") attrs in
      sprintf "<{%s}>[%s]" (String.concat "; " (fields @ attrs)) (show_iexp len)
    | Array (cells, _len, _) ->
      let show_cell (i, e) =
        let cell_body = show_iexp e in
        string_of_int i ^ " ~> " ^ cell_body
      in
      begin
        match fold2list Int_map.fold (fun i e -> (i, e)) cells with
        | [0, e] -> show_iexp e
        | cells ->
          let cell_bodies = List.map ~f:show_cell cells in
          "[|" ^ String.concat "; " cell_bodies ^ "|]"
        (* ^ "<" ^ E.dump len ^ ">" *)
      end

    | Var (v, _) -> v

    | Len e -> "len(" ^ show_iexp_body e ^ ")"

    | BS (e, itype) -> sprintf "(%s)^%s" (show_iexp e) (Int_type.to_string itype)

    | Val (e, t) -> sprintf "(%s)_%s" (show_iexp e) (Int_type.to_string t)

    | Annotation (Type_hint t, e) -> show_iexp_body  e  ^ ":" ^ Type.to_string t
    (* | Annotation (Width w, e) -> sprintf "%s<%d>" (show_iexp_body e) w *)
    | Annotation (Name name, e) -> sprintf "%s (* named %s *)" (show_iexp_body e) name

    | Unknown _ -> "?"

  and show_len = function
    | Int (ival) -> Int64.to_string ival
    | t -> show_iexp t

  and offset_to_string : offset -> string = function (os, step) ->
    let os_body = show_offset_val os in
    let step_body = show_iexp step in
    os_body ^ "(" ^ step_body ^ ")"

  and show_offset_val : offset_val -> string = function
    | Field s -> "field " ^ s
    | Attr s -> "attr " ^ s
    | Index i -> "index " ^ (string_of_int i)
    | Flat e -> show_iexp e

  and show_iexp : type a. ?bracket:bool ->  a t -> string = fun ?(bracket = false) t ->
    match t with
    | Var (s, _) -> s
    | t ->
      if bracket && (needs_bracket t) then "(" ^ show_iexp_body t ^ ")"
      else show_iexp_body t

  let list_to_string es =
    show_types := false;
    "[" ^ String.concat "; " (List.map ~f:(show_iexp ~bracket:false) es) ^ "]"

  let to_string e =
    show_types := false;
    show_iexp ~bracket:false e

  let dump_list es =
    show_types := true;
    "[" ^ String.concat "; " (List.map ~f:(show_iexp ~bracket:false) es) ^ "]"

  let dump e =
    show_types := true;
    show_iexp ~bracket:false e

  (*************************************************)
  (** {1 Traversal} *)
  (*************************************************)

  type 'b map = { f : 'a. 'a t -> 'b }
  type descend = { descend : 'a. 'a t -> 'a t }

  (**
     Does not include lengths for non-range expressions.
  *)
  let map_children (type a) { f } (t : a t) =
    match t with
    | Sym (_, es) -> List.map ~f es
    | Range (e, pos, len) -> [f e; f pos; f len]
    | Concat es -> List.map ~f es
    | Annotation(_, e) -> [f e]
    | Len e -> [f e]
    | BS (e, _) -> [f e]
    | Val (e, _) -> [f e]
    | Var _ -> []
    | Int _ -> []
    | String _ -> []
    | Char _ -> []
    | Struct _ -> []
    | Array _ -> []
    | Ptr _ -> []
    | Unknown _ -> []

  let iter_children map t =
    ignore (map_children map t)

  (**
     Not going into lengths for non-range expressions.
  *)
  let descend (type a) { descend } (t : a t) : a t =
    match t with
    | Var _ -> t
    | String _ -> t
    | Char _ -> t
    | Int _ -> t
    | Unknown _ -> t
    | Ptr _ -> t
    | Len e ->
      Len (descend e)
    | Val (e, itype) ->
      Val (descend e, itype)
    | BS (e, itype) ->
      BS (descend e, itype)
    | Sym (sym, es) ->
      Sym (sym, List.map ~f:descend es)
    | Range (e, pos, len) ->
      Range  (descend e, descend pos, descend len)
    | Concat es ->
      Concat (List.map ~f:descend es)
    | Struct (fields, attrs, len, e_old) ->
      Struct (Str_map.map descend fields, Str_map.map descend attrs, descend len, e_old)
    | Array (cells, len, step) ->
      Array (Int_map.map descend cells, len, step)
    | Annotation(a, e) ->
      Annotation(a, descend e)

  let rec vars : type a. a t -> Var.t list = function
    | Var (v, _) -> [v]
    | t ->
      map_children {f = vars} t |> List.concat |> List.dedup

  let refcount v =
    let rec refcount : type a. a t -> int = function
      | Var (v', _) when v = v' -> 1
      | t -> map_children {f = refcount} t |> List.sum
    in
    refcount

  (*************************************************)
  (** {1 Well-formedness} *)
  (*************************************************)

  let rec type_of : type a. a t -> a Type.t option = function
    | Int _ -> Some Type.Int
    | Char _ -> Some Type.Int
    | Val _ -> Some Type.Int
    | Len _ -> Some Type.Int
    | Var _ -> None
    | String _ -> Some Type.Bitstring
    | Range _ -> None
    | Concat _ -> Some Type.Bitstring
    | Struct _ -> Some Type.Bitstring
    | Array _ -> Some Type.Bitstring
    | BS (_, itype) -> Some (Type.Bs_int itype)
    | Ptr _ -> Some Type.Ptr
    | Sym (Op (_, (_, t)), _) -> Some t
    | Sym _ -> None
    | Unknown _ -> None
    | Annotation (_, e) -> type_of e

  let invariant e_top =
    let rec invariant : type a. a t -> unit = function
      | Sym (Op (_, (ts, _)), es) ->
        List.iter2 ts es ~f:(fun t e ->
          Option.iter (type_of e) ~f:(fun e_t ->
            if not (Type.subtype e_t t)
            then fail "Wrong type %s of %s in %s"
              (Type.to_string t) (to_string e) (to_string e_top)));
        List.iter ~f:invariant es
      | e -> iter_children {f = invariant} e
    in
    invariant e_top

  let itype = function
    | Sym (sym, _) -> Sym.result_itype sym
    (* | String bs -> Some (`Unsigned, List.length bs)
    | BS (_, itype) -> Some itype *)
    | Val (_, itype) -> Some itype
    | _ -> None

  let itype_exn t =
    match itype t with
    | Some t -> t
    | None -> fail "expression itype undefined: %s" (to_string t)

  let rec kind : type a. a t -> a Kind.t = fun e ->
    let module K = Kind in
    match e with
    | Int _ -> K.Int
    | Char _ -> K.Int
    | Unknown kind -> kind
    | String _ -> K.Bitstring
    | Var (_, kind) -> kind
    | Range _ -> K.Bitstring
    | Concat _ -> K.Bitstring
    | Len _ -> K.Int
    | BS _ -> K.Bitstring
    | Val _ -> K.Int
    | Struct _ -> K.Bitstring
    | Array _ -> K.Bitstring
    | Ptr _ -> K.Bitstring
    | Annotation (_, e) -> kind e
    | Sym (sym, es) ->
      match sym with
      | Int_op _ -> K.Int
      | Ptr_len -> K.Int
      | Len_y -> K.Int
      | Val_y _ -> K.Int
      | Field_offset _ -> K.Int

      | Defined -> K.Bool
      | In_type _ -> K.Bool
      | Int_cmp _ -> K.Bool
      | Logical _  -> K.Bool
      | Truth_of_bs -> K.Bool
      | Bs_eq -> K.Bool

      | BS_of_truth _ -> K.Bitstring
      | Undef _ -> K.Bitstring
      | Ztp -> K.Bitstring
      | Ztp_safe -> K.Bitstring
      | Cmp -> K.Bitstring
      | Replicate -> K.Bitstring
      | Cast _ -> K.Bitstring
      | Op _ -> K.Bitstring

      | Fun (_, (_, kind)) -> kind

      | Opaque ->
        match es with
        | [e] -> kind e
        | _ ->
          fail "E.kind: wrong number of opaque args: %s" (to_string e)

   let coerce (type a) (type b) (k : a Kind.t) (e : b t) : a t option =
     match Kind.equal_kind (kind e) k with
     | Some Type_equal.Equal -> Some e
     | None -> None

  (*************************************************)
  (** {1 Collections} *)
  (*************************************************)

  module Kind = Kind

  module Any = struct
    type t = any
    let compare = Pervasives.compare
    let to_string (Any e) = to_string e
  end

  module Base = struct
    type t = base
    let compare = Pervasives.compare
  end

  module Base_map = Core_map.Make (Base)

  module Fact_set = Set.Make (struct
    type t = fact
    let compare = compare
  end)

  module Set = struct
    type 'a exp = 'a t
    include Set.Make (Any)

    let add exp set = add (Any exp) set
    let mem exp set = mem (Any exp) set
  end

  module Key = struct
    type 'a t = 'a exp
    module Kind = Kind
    let kind = kind
    let to_string = to_string
  end

  module Map_any = Common.Map_any (Kind) (Key)

  (*************************************************)
  (** {1 IDs} *)
  (*************************************************)

  module Map = struct
    include Custom_map(Any)

    let add exp map value = add (Any exp) map value
    let maybe_find exp map = maybe_find (Any exp) map
  end

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
  (** {1 Cryptographic Expressions} *)
  (*************************************************)

   let rec is_cryptographic = function
     | Var _ -> true
     | Range _ -> true
     | Concat _ -> true
     | Sym (Fun _, _) -> true
     | Annotation (_, e) -> is_cryptographic e
     | _ -> false

  (*************************************************)
  (** {1 Misc} *)
  (*************************************************)

  let concat es = Concat es

  let range e f l = Range (e, f, l)

  let var v = Var (v, Kind.Bitstring)

  let int i = Int (Int64.of_int i)

  let string s = String (String.explode s)

  let zero = Int 0L
  let one  = Int 1L
  let zero_byte signedness = BS (Int 0L, (signedness, 1))

  let sum = function
    | [] -> zero
    | [e] -> e
    | es -> Sym (Sym.Int_op (Sym.Arith.Plus (List.length es)), es)

  let prod = function
    | [] -> one
    | [e] -> e
    | es -> Sym (Sym.Int_op (Sym.Arith.Mult (List.length es)), es)

  let conj es = Sym (Sym.Logical (Sym.Logical.And (List.length es)), es)
  let disj es = Sym (Sym.Logical (Sym.Logical.Or  (List.length es)), es)

  let rec is_concrete : type a. a t -> bool = function
    | Var _ -> false
    | e -> map_children {f = is_concrete} e |> List.all

  let contains_sym s =
    let rec contains_sym : type c. c t -> bool = function
      | Sym (s', _) when Sym.any s' = Sym.any s -> true
      | e -> map_children {f = contains_sym} e |> List.any
    in
    contains_sym

  let subst : type a b. Var.t list -> b t list -> a t -> a t = fun vs es ->
    let rec subst : type a. a t -> a t = function
      | Var (v, k) ->
        begin match List.find_index (fun v' -> v = v') vs with
        | None -> Var (v, k)
        | Some i ->
          let e = List.nth es i in
          match Kind.equal_kind k (kind e) with
          | Some Type_equal.Equal -> e
          | None -> fail "subst: wrong kind"
        end
      | t -> descend {descend = subst} t
    in
    subst

  let subst_v vs vs' e = subst vs (List.map ~f:var vs') e

  let rec remove_annotations : type a. a t -> a t = function
    | Annotation(_, e) -> remove_annotations e
    | e -> descend {descend = remove_annotations} e

  (* TODO: Consider making this part of Solver.rewrite *)
  let rec truth (e : bterm) : fact =
    let exp_to_string = to_string in
    let open Sym in
    let open Op in
    let open Logical in
    match e with
    | Sym (BS_of_truth _, [e]) -> e
    | BS (Int i, _) ->
      if i = 0L
      then Sym (Logical Not, [Sym (Logical True, [])])
      else Sym (Logical True, [])
    | Ptr _ as p -> Sym (Truth_of_bs, [p])
    | Sym (Op (LAnd, _), es) -> conj (List.map ~f:truth es)
    | Sym (Op (LOr, _), es) -> disj (List.map ~f:truth es)
    | Sym (Op (LNot, _), [e]) -> Sym (Logical Not, [truth e])
    | Sym (Op (Op_cmp _, _), _) as e -> Sym (Truth_of_bs, [e])
    | Sym (Cmp, [e1; e2]) -> Sym (Logical Not, [Sym (Bs_eq, [e1; e2])])
    | Var _ as e -> Sym (Truth_of_bs, [e])
    | Sym (Fun _, _) as e -> Sym (Truth_of_bs, [e])
    | e -> fail "Exp.truth: unexpected: %s" (exp_to_string e)

  let len e = Len e

  let apply (type a) (type b) (sym : (a, b) Sym.t) (es : any list) : b t =
    let list_to_string es =
      List.map es ~f:(fun (Any e) -> to_string e)
      |> String.concat ","
    in
    if List.length es <> Sym.arity sym
    then fail "Apply: arity mismatch: %s(%s)" (Sym.to_string sym) (list_to_string es);
    match es with
    | [] -> Sym (sym, [])
    | (Any e) :: _ ->
      let module K = Kind in
      let apply (sym : (a, b) Sym.t) (kind : a Kind.t) : b t =
        List.map es ~f:(fun (Any e) -> coerce kind e)
        |> Option.all
        |> function
          | None -> fail "Apply: arguments not of the same kind: %s" (list_to_string es)
          | Some es -> Sym (sym, es)
      in
      let kind = kind e in
      let apply_with_kind (sym : (a, b) Sym.t) (k : a Kind.t) : b t =
        match Kind.equal_kind k kind with
        | Some Type_equal.Equal -> apply sym kind
        | None ->
          fail "Apply: kind mismatch: %s(%s)" (Sym.to_string sym) (list_to_string es)
      in
      match sym, kind with
      | Int_op _, K.Int -> apply sym kind
      | Ptr_len, _ -> assert false
      | Len_y, K.Bitstring -> apply sym kind
      | Val_y _, K.Bitstring -> apply sym kind
      | Field_offset _, _ -> assert false

      | Defined, _ -> Sym (Defined, [e])
      | In_type t, _ -> apply_with_kind sym (Type.kind t)
      | Int_cmp _, K.Int -> apply sym kind
      | Logical _ , K.Bool -> apply sym kind
      | Truth_of_bs, K.Bitstring -> apply sym kind
      | Bs_eq, K.Bitstring -> apply sym kind

      | BS_of_truth _, K.Bool -> apply sym kind
      | Undef _, _ -> assert false
      | Ztp, K.Bitstring -> apply sym kind
      | Ztp_safe, K.Bitstring -> apply sym kind
      | Cmp, K.Bitstring -> apply sym kind
      | Replicate, K.Bitstring -> apply sym kind
      | Cast _, K.Bitstring -> apply sym kind
      | Op _, K.Bitstring -> apply sym kind

      | Opaque, _ -> fail "Apply: Opaque not supported"

      | Fun _, _ -> apply_with_kind sym Kind.Bitstring

      | _ -> fail "Apply: kind mismatch: %s(%s)" (Sym.to_string sym) (list_to_string es)
end


module Pat = struct
  type t =
  | VPat of Var.t
  | FPat : (bitstring, bitstring) Sym.t * t list -> t
  | Underscore

  let rec vars = function
    | FPat (_, pats) -> List.concat_map ~f:vars pats
    | VPat v -> [v]
    | Underscore -> []

  let rec dump = function
    | VPat v -> v
    | FPat (f, ps) ->
      Sym.to_string f ^ "(" ^ String.concat ", " (List.map ~f:dump ps) ^ ")"
    | Underscore -> "_"
end


module Stmt = struct
  open Exp

  type t =
  | Let of Pat.t * bterm
  (**
     [Test e; P = if e then P else 0]
  *)
  | Fun_test of fact
  | Eq_test of bterm * bterm
  | Aux_test of fact
  | Assume of fact
  | In of var list
  | Out of bterm list
  | New of var * bitstring Type.t
  | Event of string * bterm list
  | Yield
  | Comment of string

  type stmt = t

  let to_string t =
    match t with
    | In [v] ->
      "in(c, " ^ v ^ ");";

    | In vs ->
      "in(c, (" ^ String.concat ", " vs ^ "));";

    | New (v, t) ->
      "new " ^ v ^ ": " ^ Type.to_string t ^ ";"

    | Out [e] ->
      "out(c, " ^ Exp.show_iexp e ^ ");";

    | Out es ->
      "out(c, (" ^ String.concat ", " (List.map ~f:Exp.show_iexp es) ^ "));";

    | Eq_test (e1, e2) ->
      "ifeq " ^ Exp.show_iexp e1 ^ " = " ^ Exp.show_iexp e2 ^ " then "

    | Fun_test e ->
      "if " ^ Exp.show_iexp e ^ " then "

    | Aux_test e ->
      "ifaux " ^ Exp.show_iexp e ^ " then "

    | Assume e ->
      Printf.sprintf "assume %s in" (Exp.show_iexp e)

    | Event (name, es) ->
      "event " ^ name ^ "(" ^ String.concat ", " (List.map ~f:Exp.show_iexp es) ^ ");"

    | Let (pat, e) ->
      "let " ^ Pat.dump pat ^ " = " ^ Exp.show_iexp e ^ " in"

    | Yield -> "yield ."

    | Comment s -> sprintf "(* %s *)" s

  let map_children { Exp.f } = function
    | Let (_, e) -> [f e]
    | Aux_test e -> [f e]
    | Fun_test e -> [f e]
    | Eq_test (e1, e2) -> [f e1; f e2]
    | Assume e -> [f e]
    | In _ -> []
    | Out es -> List.map ~f es
    | New _ -> []
    | Event (_ev, es) -> List.map ~f es
    | Yield -> []
    | Comment _ -> []

  let iter_children map t =
    ignore (map_children map t)

  let exists_child map t =
    let results = map_children map t in
    List.exists results ~f:Fn.id

  let descend {Exp.descend = f} = function
    | Let (pat, e) -> Let(pat, f e)
    | Aux_test e -> Aux_test (f e)
    | Fun_test e -> Fun_test (f e)
    | Eq_test (e1, e2) -> Eq_test (f e1, f e2)
    | Assume e -> Assume (f e)
    | In vs -> In vs
    | Out es -> Out (List.map ~f es)
    | New (v, t) -> New (v, t)
    | Event (ev, es) -> Event (ev, List.map ~f es)
    | Yield -> Yield
    | Comment s -> Comment s

  let subst vs es t =
    descend {Exp.descend = (fun e -> Exp.subst vs es e)} t

  let vars s = map_children {Exp.f = Exp.vars} s |> List.concat

  let remove_annotations t =
    descend {Exp.descend = Exp.remove_annotations} t

  let make_test (e : fact) =
    let open Sym in
    match e with
    | Sym (Bs_eq, [e1; e2]) as e ->
      if Exp.is_cryptographic e1 && Exp.is_cryptographic e2
      then Eq_test (e1, e2)
      else Aux_test e
    | Sym (Fun _, _) as e -> Fun_test e
    | e -> Aux_test e
end

open Stmt
open Pat

type t = Stmt.t list
type iml = t

let map descend p = List.map ~f:(Stmt.descend descend) p
let iter f p = List.iter ~f:(fun s -> Stmt.iter_children f s) p

let refcount v p =
  List.sum_with (fun s ->
    Stmt.map_children {Exp.f = fun e -> Exp.refcount v e} s |> List.sum) p

let vars p = List.concat_map ~f:Stmt.vars p

let rec free_vars = function
  | Let (VPat v, e) :: p ->
    List.remove v (Exp.vars e @ free_vars p)
  | New (v, _t) :: p ->
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
        else if List.mem v ~set:(Exp.vars e) && refcount v' p > 0
        then
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
      s :: List.fold_left ~f:subst_under_binding ~init:p vs'
    | In vs' ->
      s :: List.fold_left ~f:subst_under_binding ~init:p vs'
    | s -> s :: subst vs es p

let subst_v vs vs' e =  subst vs (List.map ~f:Exp.var vs') e

let to_string p =
  String.concat "\n" (List.map ~f:Stmt.to_string p) ^ "\n"

(*************************************************)
(** {1 Auxiliary Statements} *)
(*************************************************)

let rec map_without_auxiliary descend = function
  | (Aux_test _ | Assume _) as s :: p -> s :: map_without_auxiliary descend p
  | s :: p ->
      (* enforce evaluation order *)
    let s' = Stmt.descend descend s in
    s' :: map_without_auxiliary descend p
  | [] -> []

let rec remove_auxiliary = function
  | (Aux_test _ | Assume _) :: p -> remove_auxiliary p
  | s :: p -> s :: remove_auxiliary p
  | [] -> []

(*************************************************)
(** {1 Comments} *)
(*************************************************)

let filter_with_comments ~f p =
  let rec filter = function
    | Comment _ :: s :: p when not (f s) -> filter p
    | s :: p when not (f s) -> filter p
    | s :: p -> s :: filter p
    | [] -> []
  in
  filter p

let rec remove_comments = function
  | Comment _ :: p -> remove_comments p
  | s :: p -> s :: remove_comments p
  | [] -> []

(* 1490 lines *)

