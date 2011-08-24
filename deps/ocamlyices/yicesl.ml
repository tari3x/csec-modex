(* File generated from yicesl.idl *)

type context

external set_verbosity : int -> unit
	= "camlidl_yicesl_yicesl_set_verbosity"

external version : unit -> string
	= "camlidl_yicesl_yicesl_version"

external enable_type_checker : bool -> unit
	= "camlidl_yicesl_yicesl_enable_type_checker"

external enable_log_file : string -> unit
	= "camlidl_yicesl_yicesl_enable_log_file"

external mk_context : unit -> context
	= "camlidl_yicesl_yicesl_mk_context"

external del_context : context -> unit
	= "camlidl_yicesl_yicesl_del_context"

external read : context -> string -> unit
	= "camlidl_yicesl_yicesl_read"

external inconsistent : context -> bool
	= "camlidl_yicesl_yicesl_inconsistent"

external set_output_file : string -> unit
	= "camlidl_yicesl_yicesl_set_output_file"

