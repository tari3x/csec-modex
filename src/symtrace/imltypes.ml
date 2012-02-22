
open Types
open Utils
open Exp
 
open List

(*
  Not using CV typet, because it contains options that we don't care about,
  and so is not equatable. 
*)
type imltype = 
  | MStringBot               (** All machine-representable strings and bottom. 
                                 Only used as result type, and therefore equivalent to bitstringbot. *)
  | MString of string        (** All machine-representable strings, with alias *)
  | Fixed of int * string    (** All strings of a given length, with name *)
  | Bounded of int * string  (** All strings up to a given length *)
  | Named of string          (** Some other type *)

let mstring = MString ""

type ftype = imltype list * imltype

(* types of functions based on function name *)
let funTypes: (string * ftype) list ref = ref []
(* types of read values based on expId *)
let readTypes: (int * imltype) list ref = ref []

let boolType = Named "bool"

(*************************************************)
(** {1 Strign Representations} *)
(*************************************************)

let parseType: string -> imltype = fun s -> 
  match Str.bounded_split (Str.regexp "_") s 3 with
    | ["bitstringbot"]     -> MStringBot
    | ["mstring"]          -> MString ""
    | ["mstring"; name]    -> MString name
    | ["fixed"; n]         -> Fixed (int_of_string n, "")
    | ["fixed"; n; name]   -> Fixed (int_of_string n, name)
    | ["bounded"; n]       -> Bounded (int_of_string n, "")
    | ["bounded"; n; name] -> Bounded (int_of_string n, name)
    | _                    -> Named s

let showType: imltype -> string = function
  | MStringBot        -> "bitstringbot"
  | MString ""        -> "mstring"
  | MString name      -> "mstring_" ^ name
  | Fixed (n, "")     -> "fixed_" ^ string_of_int n 
  | Fixed (n, name)   -> "fixed_" ^ string_of_int n ^ "_" ^ name
  | Bounded (n, "")   -> "bounded_" ^ string_of_int n 
  | Bounded (n, name) -> "bounded_" ^ string_of_int n ^ "_" ^ name
  | Named name        -> name

let lenToType : exp -> imltype = function
  | Int (i, _) -> Fixed (Int64.to_int i, "")
  | e -> fail ("lenToType: integer expected, got " ^ dump e)

let showFtype : string -> ftype -> string = fun name (ts, t) -> 
  name ^ "(" ^ String.concat ", " (List.map showType ts) ^ "): " ^ showType t
  
let printFtype : string * ftype -> unit = function (name, t) -> prerr_endline (showFtype name t)

let dumpTypes : unit -> unit = fun () ->
  prerr_endline "Types: ";
  iter printFtype !funTypes;
  prerr_endline ""

(*************************************************)
(** {1 Expression Types} *)
(*************************************************)

let getType : exp -> imltype = fun e -> 
  try match e with
  | Sym (("read", _), [], _, _) -> assoc (expId e) !readTypes 
  | Sym (("new", _), [], l, _) -> lenToType l
  | Sym (("newT", _), [String t], l, _) -> parseType t
  | Sym ((("var" | "const"), _), [String s], _, _) ->
    (* first try by name then by tag *) 
    begin try let (_, t) = assoc s !funTypes in t
    with Not_found -> 
      assoc (expId e) !readTypes (* this can fail for reads that are only used in lengths *) 
    end
  | Sym ((f, _), _, _, _) -> let (_, t) = assoc f !funTypes in t
  | e -> fail ("getType: unexpected expression: " ^ dump e)
  
  with Not_found -> mstring


(*************************************************)
(** {1 Casting Functions} *)
(*************************************************)


let casts: (imltype * imltype) list ref = ref []

let castFun: imltype -> imltype -> string = fun t t' -> "cast_" ^ showType t ^ "_" ^ showType t'

let mkCast: imltype -> imltype -> exp -> exp = fun t t' e ->
  (* debug ("mkCast: casting " ^ dump e ^ " to " ^ dumpType t); *)
  let cf = castFun t t' in
  if not (List.mem (t, t') !casts) then
    casts := (t, t') :: !casts;  
  Sym ((cf, Prefix), [e], Unknown, freshDet ())

(*
(**
  [mkInverse(mkCast t t' e)]
*)
let mkInverseCast: imltype -> imltype -> exp -> exp = fun t t' e ->
  (* debug ("mkCast: casting " ^ dump e ^ " to " ^ dumpType t); *)
  let cf = "inverse_cast_" ^ showType t ^ "_" ^ showType t' in
  if not (List.mem (t, t') !casts) then
    casts := (t, t') :: !casts;
  Sym ((cf, Prefix), [e], Unknown, freshDet ())
*)