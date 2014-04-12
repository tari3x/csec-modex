(*
  Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
  This file is distributed as part of csec-tools under a BSD license.
  See LICENSE file for copyright notice.
*)

open Common

(*************************************************)
(** {1 Types} *)
(*************************************************)

module Ptr_map : Custom_map with type key = int64
module Int_map : Custom_map with type key = int
module Str_map : Custom_map with type key = string

(* We shall use GADTs to make sure that all our expression are well-typed with
   respect to the following 3-types: bitstring, int, and bool. There is no
   significance in int and bool being the same as the system int and bool type,
   the types are only used as phantom types. *)

(** Hex representation: each byte corresponds to two characters. Length is the
    number of bytes. *)
type bitstring = string

type intval = int64
type ptr    = int64

type id = int

module Kind : sig
  type 'a t =
  | Bool : bool t
  | Int : int t
  | Bitstring : bitstring t

  val to_string : _ t -> string

  val equal_kind : 'a t -> 'b t -> ('a, 'b) Type_equal.t option
end

module Type : sig
  module Int_type : sig
    module Signedness : sig
      type t = [ `Signed | `Unsigned ]
      val to_string : t -> string
    end
    type width = int
    type t

    val signedness : t -> Signedness.t
    val width : t -> int
    val create : Signedness.t -> int -> t

    val to_string : t -> string
    val of_string : string -> t

    val int : t
    val size_t : t
  end

  (* Not using CV typet, because it contains options that we don't care about, and so is
     not equatable.  *)
  (* TODO: use polymorphic variants to prove to the compiler that Cast_to_int may only
     contain Bs_int *)
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
  (* Bool does not include bottom *)
  (* CR: make sure you can say the same about Bitstring - right now you use it as a
     synonym for Bitstringbot. *)
  | Bool : bool t
  (* Integers and bottom. *)
  | Int : int t

  type 'a imltype = 'a t

  module Kind : module type of Kind with type 'a t = 'a Kind.t

  val kind : 'a t -> 'a Kind.t

  type any = Any : 'a t -> any

  val of_string_bitstring : string -> bitstring t
  val of_string : string -> any
  val to_string : 'a t -> string

  val subtype : 'a t -> 'a t -> bool
  val intersection : 'a t -> 'a t -> 'a t
  val union : 'a t -> 'a t -> 'a t

  val strip_name : 'a t -> 'a t

  val has_fixed_length : bitstring t -> bool
end

module Fun_type : sig
  (* TODO: introduce tuple types so that we can check arities of symbols. This
     will also allow to treat Replicate more gracefully. *)
  type ('a, 'b) t = 'a Type.t list * 'b Type.t

  val to_string : ('a, 'b) t -> string
end

module Sym : sig
  open Type

  module Cmp : sig
    type t = Lt | Gt | Le | Ge | Eq | Ne
  end

  module Arith : sig
    type t = Plus of int | Minus | Mult of int | Div | Neg
  end

  module Logical : sig
    type t = And of int | Or of int | Not | Implies | True | Eq
  end


  (** C operators *)
  module Op : sig
      (* TODO: import these directly from CIL *)
    type t =
      BNot                                (** Bitwise complement (~) *)
    | LNot                                (** Logical Not (!) *)

    | Op_arith of Arith.t                 (** arithmetic + *)
    | Op_cmp of Cmp.t                     (** <  (arithmetic comparison) *)

      (* We don't use Index_pI *)
    | Plus_PI                              (** pointer + int *)

    | Minus_PI                             (** pointer - int *)
    | Minus_PP                             (** pointer - pointer *)
    | Mod                                 (** % *)
    | Shiftlt                             (** shift left *)
    | Shiftrt                             (** shift right *)

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

    (* These are added by us, they are not defined as ops in CIL *)
    | Cast_to_int
    | Cast_to_ptr
    | Cast_to_other
  end

  open Op

  type name = string
  type arity = int
  type invocation_id = int

  (*
    TODO: use polymorphic variants and move solver-specific stuff into solver.
  *)
  type ('a, 'b) t =
  (* TODO: should take Int_type.t *)
  | Op : Op.t * (bitstring, bitstring) Fun_type.t -> (bitstring, bitstring) t

  | Bs_eq : (bitstring, bool) t
  (** Bitstring comparison, works on bottoms too. *)
  | Cmp : (bitstring, bitstring) t
  (* TODO: what about bottoms? *)
  (** Bitstring comparison returning bitstring result.  Bs_eq(x, y) = Truth(Cmp(x, y)) *)

  | Int_op : Arith.t -> (int, int) t
  | Int_cmp : Cmp.t -> (int, bool) t
  | Logical : Logical.t -> (bool, bool) t

  | Ptr_len : (_, int) t

  | Cast : bitstring imltype * bitstring imltype -> (bitstring, bitstring) t

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
  | In_type : 'a imltype -> ('a, bool) t
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

  | Fun : name * (arity * 'b Kind.t) -> (bitstring, 'b) t

  type ('a, 'b) sym = ('a, 'b) t

  type bfun = (bitstring, bitstring) t

  type any = Any : ('a, 'b) t -> any

  (**
     May return bottom even if all arguments are not bottom.
  *)
  val may_fail : (_, _) t -> bool
  val never_fails : (_, _) t -> bool

  val arity : (_, _) t -> int

  val is_infix : (_, _) t -> bool

  val to_string : (_, _) t -> string
  val of_string : string -> any

  val cv_declaration : ('a, 'b) t -> ('a, 'b) Fun_type.t -> string

  module Key : sig
    type 'a t = (bitstring, 'a) sym
    include GADT_key with type 'a t := 'a t
                     and module Kind = Kind
  end

  module Map_any : module type of Common.Map_any (Kind) (Key)

  module Map (Value : GADT) : sig
    type 'a sym = (bitstring, 'a) t
    type 'a t

    val empty : unit -> 'a t
    val add : 'a sym -> 'a Value.t -> 'a t -> 'a t
    val maybe_find : 'a sym -> 'a t -> 'a Value.t option
    val find : 'a sym -> 'a t -> 'a Value.t
    val mem : 'a sym -> 'a t -> bool
    val iter : f:('a sym -> 'a Value.t -> unit) -> 'a t -> unit
    val disjoint_union : 'a t list -> 'a t
    val of_list : ('a sym * 'a Value.t) list -> 'a t
    val to_list : 'a t -> ('a sym * 'a Value.t) list
    val keys : 'a t -> 'a sym list
    val values : 'a t -> 'a Value.t list
    val filter : f:('a sym -> 'a Value.t -> bool) -> 'a t -> 'a t
  end
end

module Var : sig
  type t = string
  type var = t

  val fresh : string -> t

  val unfresh : string list -> unit
  val reset_fresh : unit -> unit

  val fresh_id : string -> int

  module Map : Custom_map with type key = t
end

(**
   Symbolic expressions.
*)
module Exp : sig

  open Type

  type var = Var.t

  type 'a t =
  | Int : intval -> int t

  | Char : char -> int t
  (** An int with given ascii value. *)

  | String : char list -> bitstring t
  (** We use char list instead of string as a reminder to escape each character
      if it is not printable. *)

  | Var : var * 'a Kind.t -> 'a t

  | Sym : ('a, 'b) Sym.t * 'a t list -> 'b t
  (** [Sym s es] is an application of a symbolic function [s(e1, e2, ...)].  *)

  | Range : bitstring t * int t * int t -> bitstring t
  (** A substring of a given expression with given start position and length.  A
      position is a point between two characters or at the beginning or end of
      the string.  Given a string of length [l], the first position is [0], the
      last is [l].  *)

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

  | Unknown : 'a Kind.t -> 'a t
  (** Used in length context only, where the value is not known or is not relevant. *)
  (* FIXME: shouldn't unknown be given an index to prevent it being equal to other
     unknowns? *)
  | Annotation : 'a annotation * 'a t -> 'a t

  and 'a annotation =
  | Type_hint : 'a imltype -> 'a annotation
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
  | Index of int
  (* Not intval, cause ocaml is really clumsy with that - you can't even
     subtract it easily *)
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
  (** {1 Collections} *)
  (*************************************************)

  module Kind : module type of Kind with type 'a t = 'a Kind.t

  module Base_map : Map.S with type key = base

  module Fact_set : Set.S with type elt = fact

  module Set : sig
    type 'a exp = 'a t
    include Set.S with type elt = any

    val add : 'a exp -> t -> t
    val mem : 'a exp -> t -> bool
  end

  module Key : sig
    type 'a t = 'a exp
    include GADT_key with type 'a t := 'a t
                     and module Kind = Kind
  end

  module Map_any : module type of Common.Map_any (Kind) (Key)

  (*************************************************)
  (** {1 Traversal} *)
  (*************************************************)

  type 'b map = { f : 'a. 'a t -> 'b }
  type descend = { descend : 'a. 'a t -> 'a t }

  (**
     Does not include lengths for non-range expressions.
  *)
  val map_children : 'b map ->  _ t -> 'b list
  val iter_children : unit map -> _ t -> unit

  (**
     Not going into lengths for non-range expressions.
  *)
  val descend : descend -> 'a t -> 'a t

  (*************************************************)
  (** {1 Typing } *)
  (*************************************************)

  val invariant : _ t -> unit
  val itype     : int t -> Int_type.t option
  val itype_exn : int t -> Int_type.t
  val kind      : 'a t -> 'a Kind.t
  val coerce    : 'a Kind.t -> _ t -> 'a t option

  (*************************************************)
  (** {1 IDs} *)
  (*************************************************)

  val id : _ t -> int

  val serialize_state : out_channel -> unit
  val deserialize_state : in_channel -> unit

  (*************************************************)
  (** {1 Misc} *)
  (*************************************************)

  val var : var -> bterm
  val concat : bterm list -> bterm
  val range : bterm -> iterm -> iterm -> bterm
  val int : int -> int t
  val string : string -> bterm

  val zero : iterm
  val one  : iterm
  val zero_byte : Int_type.Signedness.t -> bterm

  val sum  : iterm list -> iterm
  val prod : iterm list -> iterm
  val conj : fact list -> fact
  val disj : fact list -> fact

  val is_cryptographic : bterm -> bool
  val is_concrete : _ t -> bool
  val contains_sym : (_, _) Sym.t -> _ t -> bool

  val vars : _ t -> var list

  val refcount : var -> _ t -> int

  val subst   : var list -> 'b t list  -> 'a t -> 'a t
  val subst_v : var list -> var list -> 'a t -> 'a t

  val remove_annotations : 'a t -> 'a t

  (** The truth function from the thesis that takes C bool expressions and converts
      them to expressions of type Bool.  In particular, all bool C operators (LNot,
      LAnd, ...) are replaced by "proper" bool operators (Not, And, ...).  *)
  val truth : bterm -> fact

  val len : bterm -> iterm

  val apply : ('a, 'b) Sym.t -> any list -> 'b t

  (*************************************************)
  (** {1 Show} *)
  (*************************************************)

  (*
    val clip_enabled: bool ref
  *)

  val to_string : _ t -> string
  val dump : _ t -> string
  val dump_list : _ t list -> string
  val list_to_string : _ t list -> string
  val base_to_string : base -> string
  val offset_to_string : offset -> string
end

module Pat : sig
  type t =
  | VPat of Var.t
  | FPat : (bitstring, bitstring) Sym.t * t list -> t
  | Underscore

  val dump : t -> string
end

module Stmt : sig
  open Type
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

  val to_string : t -> string

  val map_children : 'a Exp.map -> t -> 'a list
  val iter_children : unit Exp.map -> t -> unit
  val exists_child : bool Exp.map -> t -> bool

  val descend : Exp.descend -> t -> t

  val subst : var list -> Exp.bterm list -> t -> t

  val vars : t -> var list

  val remove_annotations : t -> t

  val make_test : fact -> t
end

open Exp
open Stmt

type t = stmt list
type iml = t

val map : Exp.descend -> t -> t
val iter : unit Exp.map -> t -> unit

val refcount : var -> t -> int

val vars : t -> var list

val free_vars : t -> var list

val to_string : t -> string

(**
   Fails on capture.
*)
val subst   : var list -> bterm list -> t -> t
val subst_v : var list -> var   list -> t -> t

(* TODO: looks like this might not be necessary *)
val map_without_auxiliary : Exp.descend -> t -> t
val remove_auxiliary : t -> t

val filter_with_comments : f:(stmt -> bool) -> t -> t
val remove_comments : t -> t

(* 570 lines *)
