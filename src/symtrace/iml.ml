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
module PtrMap = CustomMap (struct include Ptr let toString = to_string end)
module IntMap = CustomMap (struct type t = int let compare = Pervasives.compare let toString = string_of_int end) 
module StrMap = CustomMap (struct include String let toString s = s end)

module Type = struct

  module T = struct
  
    module IntType = struct
      module Signedness = struct
        type t = Signed | Unsigned
        
        let toString = function
          | Signed -> "s"
          | Unsigned -> "u"
      end
      type signedness = Signedness.t = Signed | Unsigned 
      type width = int
    
      type t = signedness * width

      let toString (sd, w) = 
        match sd with 
        | Signed -> sprintf "[s,%d]" w
        | Unsigned -> sprintf "[u,%d]" w

      let ofString s = 
        let s = trim s in
        let toks = Str.split (Str.regexp "[][,]") s in
        match toks with
        | ["u"; w] ->  (Unsigned, int_of_string w)
        | ["s"; w] ->  (Signed,   int_of_string w)
        | _ -> fail "IntType.ofString: %s" s
          
      let isValid (_, w) = w <> 0
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
  
  include T
        
  let ofString s =
    try BsInt (IntType.ofString s) with
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
  
  let rec toString = function
    | Bitstringbot         -> "bitstringbot"
    | Bitstring            -> "bitstring"
    | Fixed n              -> "fixed_" ^ string_of_int n 
    | Bounded n            -> "bounded_" ^ string_of_int n 
    | Bool                 -> "bool"
    | Int                  -> "int"
    | Ptr                  -> "ptr"
    | BsInt itype          -> IntType.toString itype 
    | Named (name, Some t) -> toString t ^ "_" ^ name
    | Named (name, None)   -> name

  let rec stripName = function
    | Named (_, Some t) -> stripName t
    | t -> t
      
  let subtype t t' =
    match stripName t, stripName t' with
      | Bool, _ | _, Bool 
      | Int, _ | _, Int -> t = t'
      | _, Bitstringbot -> true
      | Bitstringbot, _ -> false
      | _, Bitstring    -> true
      | Bitstring, _    -> false 
      | Bounded i, Bounded i' -> i <= i'
      | Fixed i, Bounded i'   -> i <= i'
      | Fixed i, Fixed i'     -> i = i'
      | t, t' -> t = t'
  
  let meet t t' =
    if subtype t t' then t
    else if subtype t' t then t'
    else failwith (Printf.sprintf "cannot compute intersection of types " ^ toString t ^ " and " ^ toString t')

  (* Could return true for more types, but this is enough for now. *)
  let hasFixedLength t =
    match stripName t with
    | Fixed _ -> true
    | _ -> false
end

type imltype = Type.t

module FunType = struct
  type t = Type.t list * Type.t

  let toString (ts, t) = 
    let ts = List.map Type.toString ts in
    let t = Type.toString t in
    sprintf "%s -> %s" (String.concat " * " ts) t
  
  let ofString s = 
    if not (Str.string_match (Str.regexp "\\(.*\\) -> \\(.*\\)") s 0) 
    then fail "OpType.ofString: %s" s
    else try
      (* Call matched_group before calling split. *) 
      let result_type = Str.matched_group 2 s in
      let arg_types = Str.matched_group 1 s |> Str.split (Str.regexp "\\*") in
      (List.map Type.ofString arg_types, Type.ofString result_type)
    with 
      e -> fail "OpType.ofString: %s: %s" s (Printexc.to_string e)

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
      
        | PlusA                               (** arithmetic + *)
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
                                              
        | CastToInt
        | CastToPtr
        | CastToOther
    end

    open T
    type t = T.op
    
    let toString = function
      | Neg -> "neg"  | BNot -> "~"  |  LNot -> "!"
  
      | PlusA   -> "+"   | MinusA  ->  "-"   | Mult  -> "*"    | Div   -> "/"
      | Mod     -> "%"   | BAnd    ->  "&"   | BOr   -> "BOR"  | BXor  -> "XOR"
      | Shiftlt -> "<<"  | Shiftrt ->  ">>"  | LAnd  -> "&&"   | LOr   -> "LOR"
    
      | Eq -> "=="  
      | Ne ->  "!="  
      | Gt -> ">"    
      | Le -> "<="
      | Lt -> "<"   
      | Ge ->  ">="
        
      | PlusPI  -> "PlusPI"
      | MinusPI -> "MinusPI"
      | MinusPP -> "MinusPP"
        
      | CastToInt -> "CastToInt"
      | CastToPtr -> "CastToPtr"
      | CastToOther -> "CastToOther"
        
    let ofString = function
      | "+" -> PlusA
      | "-" -> MinusA
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
        
      | "PlusPI" -> PlusPI 
      | "MinusPP" -> MinusPP
      | "CastToInt" -> CastToInt
      | "CastToPtr" -> CastToPtr
      | "CastToOther" -> CastToOther
  
      | s -> fail "Op.toString: %s" s
        
     let isBinaryComparison = function
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
      | Op of op * FunType.t
            
      | BsEq                               (** Bitstring comparison *)
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
        
      | Const of name
        
        (* FIXME: unify with unknown? *)
      | Undef of invocation_id             (** With a tag to distinguish different undefs. 
                                               Do not create explicitly, use Expr.undef. *)
        
      | Fun of name * arity
        (* FIXME: make non-determinism explicit by random sampling, or check that there are no such funs in final output *)
      | NondetFun of name * invocation_id * arity
  end
  
  open T
  type t = T.sym

  let isArithmetic = function
    | Op (PlusA, _) | Op (MinusA, _) | Op (Mult, _) | Op (Div, _) | PlusInt _ | MinusInt | MultInt _ -> true
    | _ -> false
      
  let isBinaryArithmetic = function 
    | Op (PlusA, _) | Op (MinusA, _) | Op (Mult, _) | Op (Div, _) -> true
    | _ -> false

  let isBinaryComparison = function
    | Op (op, _) -> Op.isBinaryComparison op
    | _    -> false 

  let isIntegerComparison = function
    | LtInt                               
    | GtInt                                 
    | LeInt                               
    | GeInt                               
    | EqInt                               
    | NeInt -> true
    | _ -> false            

  let isLogical = function
    | Not | And _ | Or _ | Implies -> true
    | _ -> false 
  
  let isUnaryOp = function
      | Neg
      | BNot
      | LNot -> true
      | _ -> false 
      
  let isInfix = function
      | Op (op, _) -> not (isUnaryOp op)
    
      | PlusInt _
      | MinusInt 
      | MultInt _

      | LtInt                               
      | GtInt                                
      | LeInt                              
      | GeInt                              
      | EqInt                              
      | NeInt                                            
                        
      | Implies
      | And _ 
      | Or _
            
      | BsEq -> true
        
      | _ -> false


  let toString = function
    | Op (op, t) -> sprintf "(%s : %s)" (Op.toString op) (FunType.toString t)
      
    | EqInt -> "="
    | NeInt -> "<>"
    | GeInt -> ">="
    | GtInt -> ">"
    | LeInt -> "<="
    | LtInt -> "<"

    | PlusInt _ -> "+"
    | MinusInt -> "-"
    | MultInt _ -> "*"
    | NegInt -> "-"
      
    | Implies -> "=>"
    | And _ -> "/\\"
    | Or _ -> "\\/"
    | Not -> "¬"
    | True -> "True"

    | BsEq -> "="
    | PtrLen -> "ptrLen"
      
    | Cast (t, t') -> "cast_" ^ Type.toString t ^ "_" ^ Type.toString t'
      
    | Ztp -> "ztp"
    | ZtpSafe -> "ztpSafe"

    | Truth -> "truth"
      
    | LenY -> "lenY"
    | ValY t -> sprintf "valY%s" (IntType.toString t)
      
    | Cmp -> "cmp"
                  
    | Replicate -> "replicate"
    | FieldOffset -> "field_offset"
    | Opaque -> "opaque"
    | Defined -> "defined"
    | InType t -> sprintf "InType[%s]" (Type.toString t)
    | Undef i -> Printf.sprintf "undef[%d]" i
    | Const s -> s
    | Fun (s, _) -> sprintf "%s" s
    | NondetFun (s, id, _) -> Printf.sprintf "%s[%d]" s id


  let cvDeclaration f (ts, t) = 
    toString f ^ "(" ^ String.concat ", " (List.map Type.toString ts) ^ "): " ^ Type.toString t


  let ofString s =
    if Str.string_match (Str.regexp "(\\(.+\\) *: \\(.+\\))") s 0 
    then try 
      let op = Str.matched_group 1 s in
      let t = Str.matched_group 2 s in
      Op (Op.ofString op, FunType.ofString t)
      with e -> fail "Sym.ofString: failed op: %s: %s" s (Printexc.to_string e)
    else if not (Str.string_match (Str.regexp "\\(.+\\)/\\([0-9]+\\)") s 0)
    then fail "Sym.ofString: %s" s
    else try
      let sym = Str.matched_group 1 s in
      let nargs = int_of_string (Str.matched_group 2 s) in
      match sym with
        | "=" -> BsEq
        | "EqInt" -> EqInt

        | "ptrLen" -> PtrLen
          
        | "ztp" -> Ztp
        | "ztpSafe" -> ZtpSafe
          
        | "cmp" -> Cmp
  
        | s -> Fun (sym, nargs)
    with e -> fail "Sym.ofString: failed fun: %s: %s" s (Printexc.to_string e)
   
  let itype_exn = function
    | Op (_, (_, itype)) -> itype
    | sym -> fail "itype of symbol not defined: %s" (toString sym)

  let mayFail sym = 
    match sym with
    | Op _
    | Ztp
    | Fun _ 
    | ValY _
    | NondetFun _ -> true
      
    | FieldOffset -> fail "Sym.mayFail: not so sure about %s" (toString sym)

    | EqInt
    | NeInt
    | GeInt
    | GtInt   
    | LeInt
    | LtInt  
                  
    | PlusInt _
    | MinusInt
    | MultInt _
    | NegInt
      
    | Implies 
    | And _
    | Or _
    | Not
    | True

    | BsEq
    | PtrLen
            
    | Cast _
      
    | ZtpSafe 
      
    | Truth
    | Cmp

    | LenY
                  
    | Replicate 
    | Defined
    | InType _
    | Undef _
    | Opaque
    | Const _ -> false      

  let neverFails sym = 
    match sym with
    | BsEq
    | InType _
    | True
    | Implies 
    | And _
    | Or _
    | Not
    | Defined -> true
      
    | Op _
    | Ztp
    | Fun _ 
    | NondetFun _ 
      
    | FieldOffset 

    | EqInt
    | NeInt
    | GeInt
    | GtInt   
    | LeInt
    | LtInt  
                  
    | PlusInt _
    | MinusInt
    | MultInt _
    | NegInt
      
    | PtrLen
            
    | Cast _
      
    | ZtpSafe 

    | Truth
    | Cmp

    | LenY
    | ValY _
                                                      
    | Replicate 
    | Undef _
    | Opaque
    | Const _ -> false      


  (** The return type ignoring bottoms *)
  let resultType = function
    | PlusInt _
    | MinusInt
    | MultInt _
    | NegInt
    | LenY
    | ValY _
    | PtrLen -> Int

    | Truth
    | Not 
    | And _
    | Or _
    | True
    | EqInt
    | NeInt
    | GeInt
    | GtInt   
    | LeInt
    | LtInt  
    | Implies   
    | BsEq 
    | InType _
    | Defined -> Bool

    | Ztp
    | Opaque 
    | Fun _ 
    | NondetFun _ 
      
    | FieldOffset 

    | ZtpSafe 
      
    | Cmp
      
    | Replicate 
    | Undef _
    | Const _ -> Bitstring

    | Cast (_, t) -> t
                  
    | Op (_, (_, t)) -> t

  (** The expected argument type ignoring bottoms *)
  let argumentTypes = function
    | EqInt
    | NeInt
    | GeInt
    | GtInt   
    | LeInt
    | LtInt  
    
    | MinusInt -> [Int; Int]
      
    | PlusInt n
    | MultInt n -> List2.replicate n Int
      
    | NegInt -> [Int]

    | And n 
    | Or n -> List2.replicate n Bool

    | Not -> [Bool] 
    | Implies -> [Bool; Bool]

    | True
    | Const _ 
    | Undef _ 
    | PtrLen -> []

    | Truth
    | Ztp
    | ZtpSafe 
    | FieldOffset 
    | Opaque
    | InType _
    | LenY 
    | Defined -> [Bitstring] 

    | Cmp
    | BsEq -> [Bitstring; Bitstring]

    | Replicate -> [Bitstring; Int] 

    | Cast (t, _) -> [t]
    
    | ValY t -> [BsInt t]

    | Fun (_, n) | NondetFun (_, _, n) -> List2.replicate n Bitstring
                  
    | Op (_, (ts, _)) -> ts

  let arity t = List.length (argumentTypes t)

  module Key = struct
    type t = sym
    let compare = Pervasives.compare
    let toString = toString
  end
  
  module Map = CustomMap(Key)
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

  let usedNames = ref []

  let unfresh names = 
    usedNames := !usedNames @ names

  let rec unused stem i = 
    let name = stem ^ (string_of_int i) in
    if List.mem name !usedNames then
      unused stem (i + 1)
    else 
    begin
      usedNames := name :: !usedNames; 
      i, name
    end

  let fresh name =
    let name = if name = "" then "var" else name in
    unused name 1 |> snd
    
  let freshId name = 
    let name = if name = "" then "var" else name in
    unused name 1 |> fst
    
  module Key = struct
    type t = var
    let compare = Pervasives.compare   
    let toString t = t
  end
  
  module Map = CustomMap(Key)
end


module Exp = struct

  open Type.T
  open Sym.T
  open Sym.Op.T

  module T = struct
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
    
    (* TODO: use GADTs to enforce well-formedness *)
    
    (**
      The type of symbolic expressions. 
      b exp are expressions that evaluate to bitstrings, i exp evaluate to (mathematical) integers.
    *) 
    and exp = 
      | Int of intval 
    
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
  end

  open T
  type t = exp



  (*************************************************)
  (** {1 Show} *)
  (*************************************************)
  
  (**
    Does an expression need a bracket in context?
    
    In expressions "|" binds less tightly than any infix operator.
  *)
  let needsBracket : exp -> bool = function
    | Concat _ -> true
    | Sym (s, _) when Sym.isInfix s -> true
    | _ -> false
  
  let isFreeLen : len -> bool = function
    | Unknown -> true
    | _ -> false
  
  let baseToString : base -> string = function
    | Stack name    -> "stack " ^ name (* ^ "[" ^ string_of_int id ^ "]" *)
    | Heap (id, _)  -> "heap " ^ string_of_int id
    | Abs i         -> "abs " ^ Int64.to_string i
  
  let rec showIExpBody : exp -> string = function 
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
    
    | Sym (Const s, []) -> s
    | Sym (s, es) when Sym.isInfix s && List.length es > 1 -> 
        let bodies = List.map (showIExp ~bracket: true) es in
        if bodies = [] then Sym.toString s ^ "()" 
                       else String.concat (" " ^ Sym.toString s ^ " ") bodies
    | Sym (s, es) -> 
        let bodies = List.map (showIExp) es in
        Sym.toString s ^ "(" ^ String.concat ", " bodies ^ ")"
        
    | Range (e, f, l) ->
        let body = showIExp ~bracket: true e in
        let f_body = showLen f in
        let l_body = showLen l in
        body ^ "{" ^ f_body ^ ", " ^ l_body ^ "}"
    | Concat [] -> "<empty concat>"
    | Concat es -> 
        let bodies = List.map showIExp es in
        let body = String.concat "|" bodies
        in body
    | Ptr (b, pos) -> 
        let pos_bodies = List.map (offsetToString) pos in
        (* let (step_defs, step_body) = showLen step in *)
        let body = "<<" ^ baseToString b ^ "; " ^ String.concat ", " pos_bodies ^ ">>"
        in body
    | Struct (fields, _, _, _) ->
        let showField name e = 
          let field_body = showIExp e in
          name ^ ": " ^ field_body
        in
        let field_bodies = fold2list StrMap.fold showField fields in
        "<{" ^ String.concat "; " field_bodies ^ "}>"
    | Array (cells, len, _) -> 
        let showCell (i, e) = 
          let cell_body = showIExp e in
          string_of_int i ^ " ~> " ^ cell_body
        in
        begin
        match fold2list IntMap.fold (fun i e -> (i, e)) cells with
          | [0, e] -> showIExp e
          | cells -> 
            let cell_bodies = List.map showCell cells in
            "[|" ^ String.concat "; " cell_bodies ^ "|]"
             (* ^ "<" ^ E.dump len ^ ">" *)
        end
            
    | Var v -> v
      
    | Len e -> "len(" ^ showIExpBody e ^ ")"
  
    | BS (e, itype) -> sprintf "(%s)^%s" (showIExp e) (IntType.toString itype)
      
    | Val (e, t) -> sprintf "(%s)_%s" (showIExp e) (IntType.toString t)
  
    | Annotation (TypeHint t, e) -> showIExpBody e  ^ ":" ^ Type.toString t 
    (* | Annotation (Width w, e) -> sprintf "%s<%d>" (showIExpBody e) w *)  
    | Annotation (Name name, e) -> sprintf "%s (* named %s *)" (showIExpBody e) name
            
    | Unknown -> "?"
  
  and showLen : len -> string = function
    | Unknown -> "?"
    | Int (ival) -> Int64.to_string ival
    | e -> showIExp e
  
  and offsetToString : offset -> string = function (os, step) -> 
    let os_body = showOffsetVal os in
    let step_body = showIExp step in
    os_body ^ "(" ^ step_body ^ ")"
  
  and showOffsetVal : offsetVal -> string = function
    | Field s -> "field " ^ s
    | Attr s -> "attr " ^ s
    | Index i -> "index " ^ (string_of_int i)
    | Flat e -> showIExp e
  
  and showIExp : ?bracket: bool -> exp -> string = fun ?(bracket = false) e ->
    match e with
      | Var s -> s
      | e ->
            if bracket && (needsBracket e) then "(" ^ showIExpBody e ^ ")"
            else showIExpBody e
  
  let listToString es = "[" ^ String.concat "; " (List.map (showIExp ~bracket:false) es) ^ "]"
  let dumpList es = listToString es
    
  let toString e = showIExp ~bracket:false e  
  let dump e = toString e
  
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
    | Var _ | Int _ | String _ | Struct _ | Array _ | Ptr _ | Unknown -> []

  
  (**
      Not going into lengths for non-range expressions.
  *)
  let descend: (t -> t) -> t -> t = fun f e ->
    match e with
      | Var _ | String _ | Int _ | Unknown -> e
      | Ptr _ -> e
      | Len e -> Len (f e)
      | Val (e, itype) -> Val (f e, itype)
      | BS (e, itype) -> BS (f e, itype)
      | Sym (sym, es) -> Sym (sym, List.map f es) 
      | Range (e, pos, len) -> Range  (f e, f pos, f len)
      | Concat es -> Concat (List.map f es)
      | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map f fields, StrMap.map f attrs, f len, e_old)
      | Array (cells, len, step) -> Array (IntMap.map f cells, len, step)
      | Annotation(a, e) -> Annotation(a, f e)
  
  (*
  let rec replace e1 e2 = function
    | e when e = e1 -> e2
    | e -> descend (replace e1 e2) e
  *)
  
  let rec vars e = 
    match e with
      | Var v -> [v]
      | e -> concat_map vars (children e) |> nub

  let rec refcount v = function
    | Var v' when v = v' -> 1
    | e -> sum_with (refcount v) (children e)       


  (*************************************************)
  (** {1 Map} *)
  (*************************************************)

  module Key = struct
    type t = exp
    let compare = Pervasives.compare
    let toString = toString
  end

  module Base =
  struct
    type t = base
    let compare = Pervasives.compare
  end

  module BaseMap = Map.Make (Base)
  module Map = CustomMap(Key)
  module Set = Set.Make (Key)

  (*************************************************)
  (** {1 IDs} *)
  (*************************************************)

  let ids = ref Map.empty
  let lastId = ref 0

  let id e =
    match Map.maybe_find e !ids with
      | Some id -> id
      | None -> 
        let id = increment lastId in
        ids := Map.add e id !ids;
        id
  
  let serialize_state c =
    output_value c !ids;
    output_value c !lastId
    
  let deserialize_state c =
    ids := input_value c;
    lastId := input_value c 

  (*************************************************)
  (** {1 Well-formedness} *)
  (*************************************************)

  let typecheck t eTop =
    let module T = Type.T in
    let rec typecheck t e =
      debug "typechecking %s: %s" (toString e) (Type.toString t);
      match e, t with 
        | Len e, T.Int -> typecheck T.Bitstring e
        | Val (e, _), T.Int -> typecheck T.Bitstring e
        | BS (e, t), t' when Type.subtype (T.BsInt t) t' && IntType.isValid t -> 
          typecheck T.Int e
        | Sym (Opaque, [e]), t when Type.subtype t T.Bitstringbot ->
          typecheck t e
        | Sym (sym, es), t when Type.subtype (Sym.resultType sym) t -> 
          List.iter2 typecheck (Sym.argumentTypes sym) es
          (* Not too strict here, because some ranges are interpreted as bitstring integers. *) 
        | Range (e, pos, len), t when Type.subtype t T.Bitstring -> 
          typecheck T.Bitstring e;
          typecheck T.Int pos;
          typecheck T.Int len
        | Concat es, T.Bitstring -> 
          List.iter (typecheck T.Bitstring) es 
        | Struct (fields, attrs, len, e_old), T.Bitstring -> 
          StrMap.iter (fun _ e -> typecheck T.Bitstring e) fields;
          StrMap.iter (fun _ e -> typecheck T.Bitstring e) attrs 
        | Array (cells, len, step), T.Bitstring ->
          IntMap.iter (fun _ e -> typecheck T.Bitstring e) cells
        | Annotation(_, e), t  -> typecheck t e
        | Ptr _, t when Type.subtype T.Ptr t  -> ()
          (* This is very lax because we can't tell the width of the variable here,
             so we trust the type as long as it is a subtype of bitstring. *)
        | Var _, t when Type.subtype t T.Bitstring -> ()  
        | String _, T.Bitstring 
        | Int _, T.Int
        | Unknown, T.Bitstring -> ()
        | e, _ -> fail "typecheck: wrong type %s of expression %s in %s" (Type.toString t) (toString e) (toString eTop)
    in
    increase_debug_depth ();
    typecheck t eTop;
    decrease_debug_depth ()
    
  let rec typeOf = function
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
      
    | BS (_, itype) -> BsInt itype
      
    | Sym (Opaque, [e]) -> typeOf e 
      
    | Sym (sym, _) -> Sym.resultType sym

    | Annotation (_, e) -> typeOf e

  let itype_exn = function
    | Sym (sym, _) as e -> 
      begin match Sym.resultType sym with
        | BsInt itype -> itype
        | t -> fail "sym result type not BsInt: (%s : %s)" (toString e) (Type.toString t)
      end
    | String s -> (IntType.Unsigned, String.length s / 2)
    | BS (_, itype) (* | Val (_, itype) *) -> itype
    | e -> fail "expression itype undefined: %s" (toString e)

  (*************************************************)
  (** {1 Misc} *)
  (*************************************************)
  
  
  let concat : exp list -> exp = fun es -> Concat es
  
  let range : exp -> len -> len -> exp = fun e f l -> Range (e, f, l)
  
  let var v = Var v
  
  let int i = Int (Int64.of_int i)
      
  let intVal: exp -> int = function
    | Int i -> Int64.to_int i
    | e -> fail "not an int: %s" (toString e)
    
  let zero : exp = Int 0L
  let one  : exp = Int 1L
  let zeroByte signedness = BS (Int 0L, (signedness, 1))
  
  let sum = function
    | [] -> zero
    | [e] -> e
    | es -> Sym (PlusInt (List.length es), es)

  let prod = function
    | [] -> one
    | [e] -> e
    | es -> Sym (MultInt (List.length es), es)

  let conj es = Sym (And (List.length es), es)
  let disj es = Sym (Or  (List.length es), es)
                        
  let rec isConcrete : exp -> bool = function
    | Var _ -> false
    | e -> List.for_all isConcrete (children e)
  
  let isLength : exp -> bool = fun e ->
    match e with
    | Len _ -> true
    | _ -> false

  let isInteger : exp -> bool = function
    | Int _ -> true
    | _     -> false

  let isString : exp -> bool = function
    | String _ -> true
    | _     -> false
      

  let rec containsSym s = function
    | Sym (s', _) when s' = s -> true
    | e -> List.exists (containsSym s) (children e)
    

  let rec replace es es' e =
    match find_index ((=) e) es with
      | Some i -> List.nth es' i
      | None -> descend (replace es es') e
        
  let subst vs es e =
    replace (List.map (fun v -> Var v) vs) es e
    
  let substV vs vs' e = subst vs (List.map var vs') e
  
  let rec removeAnnotations = function
    | Annotation(_, e) -> removeAnnotations e
    | e -> descend removeAnnotations e

  (* TODO: Consider making this part of Solver.rewrite *)
  let rec truth = function
    | Sym (Op (LAnd, _), es) -> conj (List.map truth es)
    | Sym (Op (LOr, _), es) -> disj (List.map truth es)
    | Sym (Op (LNot, _), [e]) -> Sym (Not, [truth e])
      (* This is because we send defined(e) through branch as well.
         A proper solution would either use two different test 
         commands or apply truth explicityl to C if conditions. *)
    | e when typeOf e = Bool -> e
    | Sym (Op (op, (ts, t)), es) when Sym.Op.isBinaryComparison op ->
      Sym (Op (op, (ts, Bool)), es)
    | Sym (Cmp, [e1; e2]) -> Sym (Not, [Sym (BsEq, [e1; e2])])
    | Var v as e -> Sym (Truth, [e]) 
    | e -> fail "Exp.truth: unexpected: %s" (toString e) 
      
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
    | FPat (_, pats) -> List2.concat_map vars pats
    | VPat v -> [v]
    | Underscore -> []
                                                      
  let rec dump = function
    | VPat v -> v
    | FPat (f, ps) -> Sym.toString f ^ "(" ^ String.concat ", " (List.map dump ps) ^ ")"
    | Underscore -> "_"
end


module Stmt = struct

  open Exp.T
  open Pat.T

  module T = struct
    type stmt =
      | Let of pat * exp
        (** [Test e; P = if e then P else 0] *)
      | AuxTest of exp
      | Test of exp
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
  open T
  
  let toString t =
    match t with
      | In [v] -> 
        "in(c, " ^ v ^ ");";
      
      | In vs -> 
        "in(c, (" ^ String.concat ", " vs ^ "));";
  
      | New (v, t) -> 
        "new " ^ v ^ ": " ^ Type.toString t ^ ";"
  
      | Out [e] -> 
        "out(c, " ^ Exp.showIExp e ^ ");";
  
      | Out es -> 
        "out(c, (" ^ String.concat ", " (List.map Exp.showIExp es) ^ "));";
  
      | TestEq (e1, e2) ->
        "ifeq " ^ Exp.showIExp e1 ^ " = " ^ Exp.showIExp e2 ^ " then "
  
      | Test e ->
        "if " ^ Exp.showIExp e ^ " then "

      | AuxTest e ->
        "ifaux " ^ Exp.showIExp e ^ " then "
                                             
      | Assume e ->
        Printf.sprintf "assume %s in" (Exp.showIExp e)
                                                                       
      | Event (name, es) -> 
        "event " ^ name ^ "(" ^ String.concat ", " (List.map Exp.showIExp es) ^ ");"
      
      | Let (pat, e) ->
        "let " ^ Pat.dump pat ^ " = " ^ Exp.showIExp e ^ " in"
        
      | Yield -> "yield ."
        
      | Comment s -> sprintf "(* %s *)" s 
  
  
  let children: t -> exp list = function
    | Let (_, e) -> [e]
    | AuxTest e -> [e]
    | Test e -> [e]
    | TestEq (e1, e2) -> [e1; e2]
    | Assume e -> [e]
    | In vs -> []
    | Out es -> es
    | New (v, t) -> []
    | Event (ev, es) -> es
    | Yield -> []
    | Comment _ -> []
    
      
  let descend: (exp -> exp) -> t -> t = fun f -> function
    | Let (pat, e) -> Let(pat, f e) 
    | AuxTest e -> AuxTest (f e)
    | Test e -> Test (f e)      
    | TestEq (e1, e2) -> TestEq (f e1, f e2)
    | Assume e -> Assume (f e)
    | In vs -> In vs
    | Out es -> Out (List.map f es)
    | New (v, t) -> New (v, t)
    | Event (ev, es) -> Event (ev, List.map f es)
    | Yield -> Yield
    | Comment s -> Comment s
      
  let subst vs es t = descend (Exp.subst vs es) t
  
  let vars s = concat_map Exp.vars (children s)

  let removeAnnotations t = descend (Exp.removeAnnotations) t
end

open Pat.T
open Stmt.T

type iml = Stmt.t list

type t = iml

let map f p = List.map (Stmt.descend f) p
let iter f p = List.iter (fun s -> List.iter f (Stmt.children s)) p
  
let refcount v p = sum_with (fun s -> sum_with (Exp.refcount v) (Stmt.children s)) p
      
let vars p = concat_map Stmt.vars p

let rec freeVars = function
  | Let (VPat v, e) :: p ->
    remove v (Exp.vars e @ freeVars p)
  | New (v, t) :: p ->
    remove v (freeVars p)
  | In vs :: p ->
    diff (freeVars p) vs
  | s :: p ->
    Stmt.vars s @ freeVars p
  | [] -> [] 

let rec subst vs es = 

  let substUnderBinding p v =
    let vs, es = 
         List.combine vs es
      |> List.filter (fun (v', e) -> 
          if v' = v then false
          else if List.mem v (Exp.vars e) && refcount v' p > 0 then
            fail "subst: variable %s captures a variable in substitution %s ~> %s" v v' (Exp.toString e)
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
        s :: substUnderBinding p v
      | Let (pat, _) ->
        let vs' = Pat.vars pat in
        s :: List.fold_left substUnderBinding p vs'
      | In vs' ->
        s :: List.fold_left substUnderBinding p vs'
      | s -> s :: subst vs es p

let substV vs vs' e =  subst vs (List.map Exp.var vs') e

let toString p =
  String.concat "\n" (List.map Stmt.toString p) ^ "\n" 


(* 1180 lines *)

