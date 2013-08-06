(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Iml

val executeFile : in_channel -> iml

 
(*************************************************)
(** {1 Marshalling} *)
(*************************************************)

val rawOut: out_channel -> iml -> iml -> unit 

val rawIn: in_channel -> iml * iml 

(*************************************************)
(** {1 Misc} *)
(*************************************************)
      
(**
  Dump the names of C functions called during symex into "called.out".
*)
val dumpCalledFuns: unit -> unit 
 
