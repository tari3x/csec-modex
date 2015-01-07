(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Iml

val execute_file : in_channel -> iml

(*************************************************)
(** {1 Marshalling} *)
(*************************************************)

val raw_out: out_channel -> iml -> iml -> unit

val raw_in: in_channel -> iml * iml

(*************************************************)
(** {1 Misc} *)
(*************************************************)

(**
  Dump the names of C functions called during symex into "called.out".
*)
val dump_called_funs: unit -> unit

