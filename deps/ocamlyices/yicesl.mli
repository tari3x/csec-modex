(* File generated from yicesl.idl *)
(**
  Light Yices binding for Ocaml

  See the official {{:http://yices.csl.sri.com/capil.shtml} C API Lite documentation}
  and the {{:http://yices.csl.sri.com/language.shtml} input language specification}.
*)

type context

(**
  Type represeting a context
*)
(**
  Set the verbosity level
*)
external set_verbosity : int -> unit
	= "camlidl_yicesl_yicesl_set_verbosity"

(**
  Return the yices version number
*)
external version : unit -> string
	= "camlidl_yicesl_yicesl_version"

(**
  Force Yices to type check expressions when they are asserted (default = false)
*)
external enable_type_checker : bool -> unit
	= "camlidl_yicesl_yicesl_enable_type_checker"

(**
  Enable a log file that will store the assertions, checks, decls, etc.
  If the log file is already open, then nothing happens.
*)
external enable_log_file : string -> unit
	= "camlidl_yicesl_yicesl_enable_log_file"

(**
  Create a logical context.
*)
external mk_context : unit -> context
	= "camlidl_yicesl_yicesl_mk_context"

(**
  Delete the given logical context.
*)
external del_context : context -> unit
	= "camlidl_yicesl_yicesl_del_context"

(**
  Process the given command in the given logical context. The command must
  use Yices input language.

  @raise Failure if the command failed. The message is provided by Yices 
  (C API Lite [yicesl_get_last_error_message]).
*)
external read : context -> string -> unit
	= "camlidl_yicesl_yicesl_read"

(** Return true if the given logical context is inconsistent. *)
external inconsistent : context -> bool
	= "camlidl_yicesl_yicesl_inconsistent"

(**
  Set the file that will store the output produced by yices
  (e.g., models). The default behavior is to send the output to standard output.
*)
external set_output_file : string -> unit
	= "camlidl_yicesl_yicesl_set_output_file"

