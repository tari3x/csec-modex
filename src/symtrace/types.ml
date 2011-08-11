(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(*************************************************)
(** {1 Types} *)
(*************************************************)

module Ptr = Int64
module PtrMap = Map.Make (Ptr)
module IntMap = Map.Make (struct type t = int let compare = Pervasives.compare end) 
module StrMap = Map.Make (String)

type intval = int64
type ptr    = int64 

(** Hex representation: each byte corresponds to two characters. Length is the number of bytes. *)
type bitstring = string

type fixity = Infix | Prefix
type sym = string * fixity

type id = int

type symid = 
  | Det 
  | Nondet of id

type len = exp

(** Not the same as lhost in CIL *)
and base =
  | Stack of string
    (** (Old) Name and unique id of variable. Note that this way variables from different calls of the same function will be mapped
        to the same base, but not variables from different functions. *)
  | Heap of id * len

and offsetVal = 
  | Field of string
  | Attr of string
  | Index of int (* Not intval, cause ocaml is really clumsy with that - you can't even subtract it easily *)
  | Flat of len
    (** Flat offsets always measured in bytes *)

(** Offset value together with offset step *)
and offset = offsetVal * len

and pos = offset list

(**
  The type of symbolic expressions. Invariants (old):
  - The length of an [Int], or a [Range] is never [0]. Empty [String] is allowed.
  
  - A [Range] is always within bounds.  
  
  The invariant must hold for expressions in memory and on the stack, but they may be broken in intermediate
  computations.
*) 
and exp = 
  | Int of intval * len
    (** A concrete integer of given width. Width may be symbolic *) 

  | String of bitstring
    (** A concrete bitstring in hex representation: each byte corresponds to two characters. *)

  | Sym of sym * exp list * len * symid
    (** [Sym s det es l id]  
        is a bitstring of length [l], which is an application of a symbolic function [s(e1, e2, ...)]. 
        The value [id] can be used to distinguish different applications of the same nondeterministic symbol,
        for instance in case of random number generation. For deterministic functions the [id] is [Det].
      *)

  | Range of exp * len * len
    (** A substring of a given expression with given start position and length.
        A position is a point between two characters or at the beginning or end of the string.
        Given a string of length [l], the first position is [0], the last is [l]. 
        
        The special value of [All] in place of length means that the range goes to the end.
        Position and length are always within bounds.
     *)

  | Concat of exp list

  | Struct of (exp StrMap.t) * (exp StrMap.t) * len * exp
    (** The first component are the real fields, the second are the crypto attributes.
        The last component is the value of underlying memory at the time the struct has been created.
        This will get removed as soon as I transition to static implementation. *)

  | Array of (exp IntMap.t) * len * len
    (** Contains total length and element length.
    
        A good alternative is to use native array, but it only makes sense if I know the number of elements in advance.
        This can be done, but I don't see overwhelming advantages and I'm too lazy to change right now, 
        thus sticking to a sparse representation.
    
        At some point might have to use [ExpMap] here, if there is need to generalise indices to arbitrary expressions.
     *)
    (* FIXME: find out how to use ExpMap here *)

  | Ptr of base * pos
    (** Invariants (being reviewed): 
        - The offset list is never empty. 
        - The sequence of offset steps is decreasing, except that step may be [Unknown] for attribute offsets.
        - An attribute offset always comes last.
        - The first field or context offset is preceded by an index offset.
        - A field, context, or index offset is never preceded by a flat offset.
    *)
    
  | All
    (** Used in length context only, see documentation for {!Exp.simplify}. *)
    
  | Unknown
    (** Used in length context only, where the value is not known or is not relevant. *)

(** 
  Meta information assigned to expressions.
*)
type meta =
{
  mutable name: string;
  mutable hint: string;
  (** Currently unused, names are given directly *)
  
  mutable refs: int;
  (** The number of other expressions referring to this one.
      This is used for deciding whether to inline this expression during output.
   *)
  
  mutable printed: bool;
  (** Has this expression been printed out already? *)
  
  (* This is kep here so that identical expressions get identical lengths.
     You could say instead that identical expressions should only be obtained by duplication and drop this.  *)
  mutable len: exp;
} 

module Expr =
struct
  type t = exp
  let compare = Pervasives.compare
end

module Base =
struct
    type t = base
    let compare = Pervasives.compare
end

module ExpMap = Map.Make (Expr)
module BaseMap = Map.Make (Base)

type mem = exp BaseMap.t 

(*************************************************)
(** {1 Solver Types} *)
(*************************************************)

type answer = Yes | No | Maybe

(**
    [true] means definitely not equal, [false] means we don't know.
*)
type pbool = bool

