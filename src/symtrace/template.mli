open Iml
open Iml.Sym
open Iml.Exp
open Transform

type t

val crypto  : t -> string list
val crypto2 : t -> string list
val query   : t -> string list
val envp    : t -> string list
val model   : t -> string list

val var_types : t -> Type_ctx.t
val fun_types : t -> Fun_type_ctx.t

val read_file: cv_lib_name:string -> name:string -> t

val is_defined : t -> (bitstring, _) Sym.t -> bool

val check_assertions : t -> bitstring Sym_defs.t -> unit
