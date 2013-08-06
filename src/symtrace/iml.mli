(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

(*************************************************)
(** {1 Types} *)
(*************************************************)

module PtrMap: CustomMap with type key = int64
module IntMap: CustomMap with type key = int
module StrMap: CustomMap with type key = string

module Type: sig
  module T: sig
  
    module IntType: sig
      type signedness = Signed | Unsigned
      type width = int
      type t = signedness * width
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
      | BsInt of IntType.t
      | Named of string * t option (** A named type with an optional type definition.
                                       Named (_, None) may not contain bottom. *)
  end

  type t = T.t =
      | Bitstringbot               (** All strings and bottom. *)
      | Bitstring                  (** All machine-representable strings *)
      | Fixed of int               (** All strings of a given length *)
      | Bounded of int             (** All strings up to a given length *)
      | Bool
      | Int
      | Ptr
      | BsInt of T.IntType.t
      | Named of string * t option (** A named type with an optional type definition.
                                       Named (_, None) may not contain bottom. *)
    
  val ofString: string -> t
  
  val toString: t -> string
  
  val subtype: t -> t -> bool
  
  val meet : t -> t -> t
  
  val stripName: t -> t
end

type imltype = Type.t

module FunType: sig
  type t = imltype list * imltype

  val toString: t -> string
end


module Sym: sig
  open Type.T

  module Op: sig
    module T: sig
      (* TODO: import these directly from CIL *)
      type op = 
          Neg                                 (** Unary minus *)
        | BNot                                (** Bitwise complement (~) *)
        | LNot                                (** Logical Not (!) *)
      
        | PlusA                               (** arithmetic + *)
          (* We don't use IndexPI *)
        | PlusPI                              (** pointer + integer *)
          
        | MinusA                              (** arithmetic - *)
        | MinusPI                             (** pointer - integer *)
        | MinusPP                             (** pointer - pointer *)
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
                                               * set {!Cil.useLogicalOperators}. *)
        | LOr                                 (** logical or. Unlike other 
                                               * expressions this one does not 
                                               * always evaluate both operands.  If 
                                               * you want to use these, you must 
                                               * set {!Cil.useLogicalOperators}. *)

          (* These are added by us, they are not defined as ops in CIL *)
        | CastToInt
        | CastToPtr
        | CastToOther 
    end
    
    type t = T.op
  end
  
  module T: sig
    open Op.T
  
    type name = string
    type arity = int
    type invocation_id = int
  
    (* 
      TODO: use polymorphic variants and move solver-specific stuff into solver.
    *)
    type sym =
      | Op of op * FunType.t
            
      | BsEq                               (** Bitstring comparison, works on bottoms too. *)
      | Cmp                                (** Bitstring comparison returning bitstring result.
                                               BsEq(x, y) = Truth(Cmp(x, y)) *)
        
      | MinusInt                           (** Operators without overflow. Think of them as widening their result
                                               if necessary *)
      | PlusInt of arity
      | MultInt of arity
      | NegInt

      | LtInt                               (** <  (arithmetic comparison) *)
      | GtInt                               (** >  (arithmetic comparison) *)  
      | LeInt                               (** <= (arithmetic comparison) *)
      | GeInt                               (** >  (arithmetic comparison) *)
      | EqInt                               (** == (arithmetic comparison) *)
      | NeInt                               (** != (arithmetic comparison) *)            

      | Implies
      | And of arity
      | Or of arity
      | Not
      | True
        
      | PtrLen

      | Cast of Type.t * Type.t
        
        (**
          Zero-terminated prefix - up to but not including the first 0. 
          Bottom if the bitstring does not contain zero.
        *)
      | Ztp
        (**
          Same as Ztp, but returns the argument unchanged instead of bottom.
        *)
      | ZtpSafe
        
      | Replicate
      | FieldOffset
      | Opaque                             (** Used only in Solver *)
      | Defined
      | InType of Type.t                   (** Defined is the same as (InType Bitstring) *)
        
      | Truth

        (* The yices versions of len and val, see thesis. *)        
      | LenY
      | ValY of IntType.t
        
        (* TODO: kill const, now that Funs carry explicit arities *)
      | Const of name
        
        (* FIXME: unify with unknown? *)
      | Undef of invocation_id             (** With a tag to distinguish different undefs. 
                                               FIXME: Do not create explicitly, use Expr.undef. *)
        
      | Fun of name * arity
        (* FIXME: make non-determinism explicit by random sampling, or check that there are no such funs in final output *)
      | NondetFun of name * invocation_id * arity
  end

  type t = T.sym
  
  (**
    Binary or integer arithmetic opeator. Cast not included.
  *)
  val isArithmetic: t -> bool
  val isBinaryArithmetic: t -> bool
  val isBinaryComparison: t -> bool
  (** A symbol that takes boolean arguments and returns a boolean result. *)
  val isLogical: t -> bool

  (**
    May return bottom even if all arguments are not bottom.
  *)
  val mayFail: t -> bool
  val neverFails: t -> bool
  
  val resultType: t -> Type.t
  val argumentTypes: t -> Type.t list
  val arity: t -> int
  
  val isInfix: t -> bool
  
  val toString: t -> string
  val ofString: string -> t
  
  val cvDeclaration: t -> FunType.t -> string
  
  module Map: CustomMap with type key = t
end


type intval = int64
type ptr    = int64 


(** Hex representation: each byte corresponds to two characters. Length is the number of bytes. *)
type bitstring = string


type id = int

type var = string

module Var: sig
  type t = var
  
  val unfresh: string list -> unit
  
  val fresh: string -> t
  val freshId: string -> int
  
  module Map: CustomMap with type key = var
end 

module Exp: sig

  open Type.T
  open Sym.T

  module T: sig
    type len = exp

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
    
    
    and offsetVal = 
      | Field of string
      | Attr of string
      | Index of int (* Not intval, cause ocaml is really clumsy with that - you can't even subtract it easily *)
        (* For now flat offsets are true integers, unlike in the thesis *)
      | Flat of len
        (** Flat offsets always measured in bytes *)
    
    (** Offset value together with offset step *)
    and offset = offsetVal * len
    
    and pos = offset list

    (* FIXME: replace information lens with width option. Possibly use named width or some other
       mechanism to make sure that output is the same on all architectures. The best thing
       is to implement getLenValue by evaluating the length expression in the yices model (with cache).
       But this does rely a bit too much on global state - think again!
      
       Lens and Ints should have a width field, Vars and Syms should be covered by a width
       annotation. The reason for the difference is that width changes the meaning of 
       Int and Len and is necessary to reconstruct the bitstring that they represent,
       but not so for Vars and Syms.
      
      Do we actually need any width information on vars and syms? It is only used for treating arithmetic expressions
      in the solver, but then you should just add width information to the arithmetic symbols.
    *) 
    
    (* TODO: use GADTs to enforce well-formedness.
       You would then need to use two different syms, a binary and an integer
     *)
    
    (**
      The type of symbolic expressions. 
      b exp are expressions that evaluate to bitstrings, i exp evaluate to (mathematical) integers.
    *) 
    and exp = 
      | Int of intval
        (** A concrete integer of given width. *) 
    
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
    
      | BS of exp * IntType.t
        
      | Val of exp * IntType.t
    
      | Struct of (exp StrMap.t) * (exp StrMap.t) * len * exp
        (** The first component are the real fields, the second are the crypto attributes.
            The last component is the value of underlying memory at the time the struct has been created.
            This will get removed as soon as I transition to static implementation. *)
    
      | Array of (exp IntMap.t) * len * len
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
      | TypeHint of imltype
      | Name of string 
      (* | Width of width *)
  end

  open T
  type t = exp

  module BaseMap: Map.S with type key = base
  module Map: CustomMap with type key = exp
  module Set: Set.S     with type elt = exp


  (*************************************************)
  (** {1 Traversal} *)
  (*************************************************)

  (**
      Does not include lengths for non-range expressions.
  *)
  val children: t -> t list
    
  (**
      Not going into lengths for non-range expressions.
  *)
  val descend: (t -> t) -> t -> t 

  (*************************************************)
  (** {1 Typing } *)
  (*************************************************)

  (**
    If [typecheck t e] is true and [e] does not evaluate to 
    bottom then [e] is of type [t].
  *)
  val typecheck: Type.t -> exp -> unit
  val itype_exn: exp -> IntType.t
  val typeOf: exp -> Type.t

  (*************************************************)
  (** {1 IDs} *)
  (*************************************************)

  val id: t -> int
  
  val serialize_state: out_channel -> unit
  val deserialize_state: in_channel -> unit 

  (*************************************************)
  (** {1 Misc} *)
  (*************************************************)
    
  val var: var -> exp
  val concat : exp list -> exp
  val range : exp -> len -> len -> exp
  val int : int -> exp
  val intVal: exp -> int
  
  val zero : exp
  val one  : exp
  val zeroByte: IntType.signedness -> exp
  
  val sum: exp list -> exp
  val prod: exp list -> exp 
  val conj: exp list -> exp
  val disj: exp list -> exp 
  
  (*
  (** Arbitrary for now *)
  val max_len : exp
  *)
  
  val isConcrete : exp -> bool
  val isLength : exp -> bool
  (* val isComparison: exp -> bool *)
  (* val isLogical: exp -> bool *)
  val isInteger : exp -> bool
  val isString: exp -> bool
  val containsSym: sym -> exp -> bool
  
  val vars: t -> var list 

  val refcount: var -> t -> int
  
  (**
    The first list must contain [Var] expressions only.
  *)
  val subst: var list -> exp list -> exp -> exp
  val substV: var list -> var list -> exp -> exp
  (* 
  val replace: exp list -> exp list -> exp -> exp
  *)
  
  val removeAnnotations: t -> t
  
  (**
    The truth function from the thesis that takes C boolean
    expressions and converts them to expressions of type Bool.
    In particular, all boolean C operators (LNot, LAnd, ...) are
    replaced by "proper" boolean operators (Not, And, ...).
  *)
  val truth: t -> t
  
  val len: t -> t
  
  (*************************************************)
  (** {1 Show} *)
  (*************************************************)

  (* 
  val clipEnabled: bool ref
  *)

  val toString: t -> string
  val dump: t -> string
  val dumpList: t list -> string
  val listToString: t list -> string
  val baseToString: base -> string
  val offsetToString: offset -> string
end 


module Pat: sig
  open Sym.T

  module T: sig
    type pat =
      | VPat of var 
      | FPat of sym * pat list
      | Underscore
  end
      
  type t = T.pat
  
  val dump: t -> string 
end


module Stmt: sig
  open Exp.T
  open Pat.T

  module T: sig
    type stmt =
      | Let of pat * exp
      | AuxTest of exp
        (** 
          [GenTest e; P = if e then P else 0]
          
          [GenTest] is never auxiliary after symex postprocessing. 
        *)
        (* FIXME: rename GenTest to Test after it stabilises *)
      | GenTest of exp
        (**
          [TestEq] is never auxiliary after symex postprocessing.
        *)
      | TestEq of exp * exp
      | Assume of exp
      | In of var list
      | Out of exp list
      | New of var * imltype
      | Event of string * exp list
      | Yield  
      | Comment of string
  end
  
  type t = T.stmt
  
  val toString: t -> string
  
  val children: t -> exp list
      
  val descend: (exp -> exp) -> t -> t 
  
  val subst: var list -> exp list -> t -> t
  
  val vars: t -> var list
  
  val removeAnnotations: t -> t
end

open Exp.T

type iml = Stmt.t list

type t = iml

val map: (exp -> exp) -> t -> t
val iter: (exp -> unit) -> t -> unit

val refcount: var -> t -> int
      
val vars: t -> var list

val freeVars: t -> var list

val toString: t -> string

(**
  Fails on capture.
*)
val subst: var list -> exp list -> t -> t
val substV: var list -> var list -> t -> t

(* 490 lines *)
