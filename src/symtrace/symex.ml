(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open List

open Common
open Transform_imltrace

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Exp.T
open Iml.Stmt.T

module E = struct
  include Iml.Exp
  include Iml.Exp.T
end
module S = Solver
module Stmt = struct
  include Iml.Stmt.T
  include Iml.Stmt
end
module Base_map = E.Base_map

module L = struct
  let get_len e = Simplify.simplify (E.Len e)
end

type mem = exp Base_map.t


type sym = string
type nargs = int

type cvm =
    (* loading *)
  | Load_int of intval
  | Load_str of string (** assumed to be in hex already *)
  | Load_char of char
  | Load_stack_ptr of string (** name of variable; step init to 0 (invalid value) *)
  | Load_heap_ptr of int (** stack: buffer length; step init to 0 *)
  | Load_buf (** stack: ptr, len *)
  | Load_mem (** stack: ptr; use ptr step as len. *)
  | Load_all (** stack: ptr; load the whole buffer *)
    (* Load_attr attr // stack: ptr; consumed *)
  | In  (** stack: len *)
  | New (**
            stack: constant int length N, type alias T. Creates value of type Fixed (N, T).
            Special case: N = -1. Creates value of type (Named T).
         *)
  | Env of string

    (* offsetts *)
  | Field_offset of string (** stack: ptr; step init to 0 *)
  | Ctx_offset of string (** pointer step set to 0,
                            a context pointer should never be used with Load_mem (implement a check in update) *)
  | Index_offset of Int_type.t (** stack: ptr, offset; step init to 0 *)

    (* operations *)
  | Apply of sym
  | Dup
  | Len
  | Truth
  | BS of Int_type.t
  | Val of Int_type.t
  | In_type of string

  | Apply_nondet (** For a symbol application on top of stack indicate that the application is not deterministic.
                    For a stack pointer assigns it a fresh id. *)

  (* | Concrete_result of intval *)
  | Append (** stack: first, second; second consumed *)
  | Event of sym * nargs
  | Branch of intval
  | Assume
  | Hint of string
  | Type_hint of string
  | Set_ptr_step (** The size of the underlying type,
                   stack: ptr, step; step consumed
                   Overwrites existing pointer step.
                   Is necessary as a separate thing because of casts and the trick with flat char arrays. *)
  | Done (** signals that we are done creating and customising a new value *)

    (* storing *)
  | Store_buf (** stack: exp, ptr; both consumed; use exp len *)
  | Store_mem (** stack: exp, ptr; both consumed; use pointer step *)
  | Store_all (** stack: exp, ptr; both consumed; replace whatever the pointer points to, don't look at exp len
                 Currently used in two cases:
                 - To replace contents of E.zero-terminated expressions
                 - To store cryptographic attributes *)
    (* Store_attr attr // stack: exp, ptr; both consumed *)
  | Clear (** No warnings *)
  | Copy_ctx (** stack: to, from; both consumed *)
  | Out

    (* misc *)
  | Call of string * nargs
  | Return
  | Comment


(*************************************************)
(** {1 State} *)
(*************************************************)

(** The symbolic memory *)
let mem : mem ref = ref Base_map.empty

(** Symbolic execution stack *)
let stack: exp Stack.t = Stack.create ()

(** IML generated so far *)
let iml: iml ref = ref []

(** All the functions called so far, for debug purposes only *)
let called_functions: string list ref = ref []

(** Current call stack, used for debug purposes only *)
let call_stack: string Stack.t = Stack.create ()

(** The ids for the calls on the call stack *)
let call_id : int ref = ref 0

(** The ids used for stack pointers. *)
let cur_ptr_id : int ref = ref 0

(** The number of instructions executed so far *)
let done_instr : int ref = ref 0

let last_comment = ref ""

let reset_state : unit -> unit = fun () ->
  (* don't reset the Exp state *)
  mem := Base_map.empty;
  Stack.clear stack;
  iml := [];
  Stack.clear call_stack;
  call_id := 0

let lens : exp Int_map.t ref = ref Int_map.empty

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let ptr_len = Sym (Ptr_len, [])

let make_assumptions : unit -> unit = fun () ->
  (* FIXME: remove this later when all symbolic sizes are being used properly *)
  S.add_fact (S.ge (E.int 8) ptr_len);
  S.add_fact (S.gt ptr_len E.zero)

let check_well_formed : exp -> unit = fun e ->

  let rec check_decreasing : pos -> unit = function
    | [_; (Attr _, _)] -> ()
    | (_, step1) :: ((_, step2) as os2) :: pos' ->
      if not (S.greater_equal_len step1 step2) then
        fail "check_well_formed: offset step sequence not monotonous: %s" (E.dump e);
      check_decreasing (os2 :: pos')

    | _ -> ()
  in

  (*
  (* check that all flat offsets have step 1 *)
  let rec check_flat_offset: offset -> unit = function
    | (Flat _, step) ->
      if not (S.equal_len step one) then
        fail ("check_well_formed: a flat offset with step greater 1: " ^ E.dump e)
   | _ -> ()
  in
  *)

  (*
  (*
    One thing that prevents this from being enforced is that a step of an attribute offset
    isn't known, so an attribute offset doesn't bubble up past the trailing flat or index offset.

    I think this can be fixed by updating bubble_up so that attributes always bubble up past
    flat offsets.
  *)
  let rec check_order : bool -> bool -> pos -> unit = fun seen_index prev_flat -> function
    | ((Field _ | Attr _), _) :: pos' ->
      if not seen_index then
        fail "check_pos: first field or attribute not preceded by index: %s" (E.dump e);
      if prev_flat then
        fail "check_pos: field or attribute preceded by flat: %s" (E.dump e);
      check_order seen_index false pos'

    | (Index _, _) :: pos' ->
      if prev_flat then
        fail "check_pos: index preceded by flat: %s" (E.dump e);
      check_order true false pos';

     | (Flat _, _) :: pos' -> check_order seen_index true pos';

     | [] -> ()
  in
  *)

  E.typecheck (E.type_of e) e;

  match e with
	  | Ptr (b, pos) ->
    	(* check_order false false pos; *)
	    check_decreasing pos;
      (* See notes about flat offset steps *)
      (* iter check_flat_offset pos *)
	  | e -> () (* L.get_len e <> Unknown *) (* see notes *)

(*
  FIXME: merge when merging with CIL.
*)
let is_interface_fun : string -> bool = fun s ->
  List.mem s
        ["event0"; "event1"; "event2"; "event3"; "event4"; "readenv"; "readenvE"; "readenvL";
         "make_str_sym"; "make_sym"; "mute"; "unmute"; "fail";
         (* Internal interface functions: *)
         "load_buf"; "load_all"; "load_ctx"; "load_int"; "load_str";
         "symL"; "symN"; "symNE"; "input"; "newTN"; "newTL"; "newL";
         "varsym"; "var"; "varWithBufInit"; "varL"; "output";
         "store_buf"; "store_all"; "store_ctx"; "event";
         "add_to_attr"; "set_attr_str"; "set_attr_buf"; "set_attr_int";
         "get_attr_int"; "copy_ctx"; "copy_attr_ex"; "copy_attr";
         "clear_attr"; "concrete_val"; "fresh_ptr"; "test_intype"; "assume_intype";
         "len"; "assume"; "assume_len"; "clear"; "duplicate"; "store_len"]



let interesting : exp -> bool = function
  | Ptr (Stack "SAX_meter.i:method[4777]", _) -> true
  (* | Ptr (Heap (17, _), _) -> true *)
  | _ -> false


(*************************************************)
(** {1 Fail} *)
(*************************************************)

let fail_mode = ref false

let fail_buf = ref ""

let output a =
  let output s =
    if !fail_mode then
      fail_buf := !fail_buf ^ ("\n  " ^ s)
    else
      if debug_enabled () then prerr_endline (decorate_debug s)
  in
  Printf.ksprintf output a


(** Non-destructive. *)
let dump_stack : unit -> unit = fun () -> Stack.iter (fun e -> output "# %s" (E.dump e)) stack

let dump_call_stack : unit -> unit = fun () -> Stack.iter (fun fname -> output "#  %s" fname) call_stack

let dump_memory: unit -> unit = fun () ->

    let dump_cell: base -> exp -> unit = fun b e ->
        output "%s => %s"(E.base_to_string b) (E.dump e)
    in

    Base_map.iter dump_cell !mem

let dump_called_funs: unit -> unit = fun () ->
  (* output called functions *)
  let f = open_out_bin "called.out" in
  List.iter (fun s -> output_string f (s ^ "\n")) !called_functions

let failfun () =
  fail_mode := true;
  output "Instructions Executed: %d" !done_instr;
  output "Last comment: %s" !last_comment;
  output ("Call stack:");
  dump_call_stack ();
  (* E.clip_enabled := false; *)
  output ("Execution stack:");
  dump_stack ();
  (*
  debug ("symbolic memory:");
  dump_memory ();
  debug ("generated iml:");
  iter prerr_endline (map E.dump (filter interesting_event !iml));
  *)
  (*
  (* FIXME: this should be done only once, given that we use catch now. *)
  dump_called_funs ();
  *)

  output "process = ";
  output "%s" (Iml.to_string (proc_and_filter !iml));
  fail_mode := false;
  let result = !fail_buf in
  fail_buf := "";
  result


let _ = fail_funs := !fail_funs @ [failfun]

(*************************************************)
(** {1 Symbolic Buffer Manipulation} *)
(*************************************************)

let flatten_array : exp Int_map.t -> exp = fun cells ->
  let rec check = fun len -> function
    | [] -> ()
    | [j, _] -> if j = len - 1 then () else fail "flatten: sparse arrays not supported yet"
    | _ :: xs -> check len xs
  in
  let clist = fold2list Int_map.fold (fun i e -> (i, e)) cells in
  check (length clist) clist;
  Simplify.simplify (Concat (List.map snd clist))

let flatten_index : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (Simplify.prod [step; (E.int i)]), step) :: pos
  | _ -> fail "flatten_index"

(**
    Flatten until the next field or attribute offset.
*)
let rec flatten_index_deep : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (Simplify.prod [step; (E.int i)]), step) :: flatten_index_deep pos
  | (Flat e, step) :: pos -> (Flat e, step) :: flatten_index_deep pos
  | pos -> pos


(**
    We assume that length is correct, in particular we don't check length when doing member extraction.

    If we need to apply a member offset to a concatenation, we try with the first element.

    None in length position means extract everything until the end of the storage unit.
    FIXME: this will be simplified.
*)
let rec extract : pos -> len option -> exp -> exp = fun pos l e ->
  debug "extract, e_host: %s" (E.dump e);
  debug "extract, pos: %s" (String.concat ", " (List.map E.offset_to_string pos));
  debug "extract, len: %s" (option_to_string E.dump l);
  begin match l with
    | None -> ()
    | Some l -> E.typecheck (Type.Int) l
  end;
  match (pos, l, e) with
    | ((Field s, _) :: os', _, Struct (fields, _, _, e_old)) ->
      begin
	      try let e' = Str_map.find s fields in extract os' l e'
	      with Not_found -> extract pos l e_old
      end

    | ((Attr s, _) :: os', _, Struct (_, attrs, _, _)) ->
      let e' = try Str_map.find s attrs
               with Not_found -> fail "extract: attribute not initialised: %s" s in
      extract os' l e'

    | ((Index i, step) :: pos', l, Array (cells, len, elt_size)) ->
      (* trying to catch a situation where pointer to the start of array is used to extract a big piece of array *)
      (* TODO: simplify the control here *)
      let inside_cell = match l with
        | Some l -> S.greater_equal_len_answer elt_size l = S.Yes
        | None -> false
      in
      if not inside_cell then
        extract pos l (flatten_array cells)
      else
      begin
	if S.equal_int step elt_size then
	  let e' = try Int_map.find i cells
	    with Not_found -> fail "extract: array index not initialised: %s" (string_of_int i) in
	  extract pos' l e'
	else if i = 0 && S.equal_int step len then
	  extract pos' l e
	else if S.greater_equal_len elt_size step then
	  let e' = try Int_map.find 0 cells
	    with Not_found -> fail "extract: cannot descend into first cell" in
	  extract pos l e'
	else
          extract pos l (flatten_array cells)
      end

    | ((Index i, step) :: pos', l, e) ->
      extract (flatten_index pos) l e

    | (pos, Some l, Array (cells, _, l')) ->
        if pos = [] && S.equal_int l l' then e else
        extract pos (Some l) (flatten_array cells)

    | (pos, None, Array (cells, _, l')) ->
        extract pos None (flatten_array cells)

    | ((Flat oe, _) :: os', l, e) ->
      let e' = Simplify.simplify (Range (e, oe, Simplify.minus (L.get_len e) oe)) in
      extract os' l e'

    | ([], None, e) -> e
    | ([], Some l, e) -> Simplify.simplify (Range (e, E.zero, l))

      (* FIXME *)
    | (os, l, Concat (e' :: es)) -> extract os l e'

    | ((Field s, _) :: os', Some l, e) ->
      (* We already pre-trim to length l, otherwise the length of the result is harder to compute. *)
      let e' = Simplify.simplify (Range (e, Sym (Sym.T.Field_offset, [String s]), l)) in
      extract os' (Some l) e'

    | _ -> fail "extract: cannot read through pointer"

let extract pos l e =
  push_debug "extract_pos";
  let result = extract pos l e in
  pop_debug "extract_pos";
  result

(** Creates structures and members along the way if they don't exist.

    [l_val] is the length of the part of [e_host] that needs to be replaced with [e_val].
    In case [l_val = None] the effect is to replace all data from [pos] until the end of
    the segment that [pos] points to.

    [step] gives the length for newly created structures and arrays.

    [e_host] is the rest of the current segment. This is important if [l_val = Infty].

    It is however not a requirement and sometimes the call can return expressions of other
    lengths.
*)
let rec update (pos : pos) (step : len) (l_val : len option) (e_host : exp) (e_val : exp) =
  debug "update, e_host: %s" (E.dump e_host);
  debug "update, e_val: %s"  (E.dump e_val);
  debug "update, pos: %s" (String.concat ", " (List.map E.offset_to_string pos));
  debug "update, step: %s" (E.dump step);
  debug "update, l_val: %s" (option_to_string E.dump l_val);
  E.typecheck Type.Int step;
  begin match l_val with
  | None -> ()
  | Some l -> E.typecheck Type.Int l
  end;
  match (pos, l_val, e_host) with
  | ((Index i, step') :: pos', None, Array (cells, len, elt_size)) ->
    update pos step None (flatten_array cells) e_val

  | ((Index i, step') :: pos', Some l_val, Array (cells, len, elt_size)) ->
    begin
      match S.greater_equal_len_answer elt_size l_val with
      | (S.No | S.Maybe) -> update pos step (Some l_val) (flatten_array cells) e_val
      | _ ->
	if S.equal_int step' elt_size then
	  let e_elem = try Int_map.find i cells
	    with Not_found -> Concat [] in
	  let e' = update pos' step' (Some l_val) e_elem e_val in
	  Array (Int_map.add i e' cells, len, elt_size)

	else if i = 0 && S.equal_int step' len then
	  update pos' step' (Some l_val) e_host e_val

	(* else if S.greater_equal_len elt_size step then
	   let e_elem = try Int_map.find 0 cells
	   with Not_found -> Concat [] in
	   let e' = update pos elt_size l_val e_elem e_val in
	   Array (Int_map.add 0 e' cells, len, elt_size) *)

        else update pos step (Some l_val) (flatten_array cells) e_val

    (* else fail "update: index step incompatible with array element size" *)
    end

  | ((Index i, step') :: pos', None, Concat []) ->
    update (flatten_index pos) step None e_host e_val

  | ((Index i, step') :: pos', Some l_val, Concat []) ->
    if S.greater_equal_len step' l_val then
      let e_new = Array (Int_map.empty, step, step') in
      update pos step (Some l_val) e_new e_val
    else
      update (flatten_index pos) step (Some l_val) e_host e_val

  (* TODO: give it one more chance in case Concat [Array _]? *)
  | ((Index i, step') :: pos', l_val, e_host) ->
    (* deep flattening here is slightly cosmetical - otherwise you get stuff like
       [payload_len|<{0 -> <{0 -> 7c}>}>] *)
    (* let e_new = update (flatten_index_deep pos') step' l_val (Concat []) e_val in
       update (flatten_index [Index i, step']) step (L.get_len e_new) e_host e_new *)
    update (flatten_index_deep pos) step l_val e_host e_val

  | ((Field s, step') :: pos', l_val, Struct (fields, attrs, len, e_old)) ->
    let e_field =
      try Str_map.find s fields
      with Not_found -> Concat []
    in
    let e' = update pos' step' l_val e_field e_val in
    Struct (Str_map.add s e' fields, attrs, len, e_old)

  | ((Attr s, step') :: pos', l_val, Struct (fields, attrs, len, e_old)) ->
    let e_attr = try Str_map.find s attrs
      with Not_found -> Concat [] in
    let e' = update pos' step' l_val e_attr e_val in
    Struct (fields, Str_map.add s e' attrs, len, e_old)

  (* FIXME: we might need to descend if position is E.zero *)
  | ((Flat oe, _) :: _, l_val, Array (cells, _, _)) ->
    update pos step l_val (flatten_array cells) e_val

  (* We follow the assumption that a flat offset has step 1.  If we want to create a
     structure below this offset, we better inherit the structure size (pointer step) from
     above.  *)
  | ((Flat oe, _) :: pos', l_val, e) ->
    (* FIXME: you might want to flatten_index_deep pos' in case oe > 0 *)
    let e1 = Simplify.simplify (Range (e, E.zero, oe)) in
    let e2 = Simplify.simplify (Range (e, oe, Simplify.minus (L.get_len e) oe)) in
    Simplify.simplify (Concat [e1; update pos' step l_val e2 e_val])

  | ([], None, e) -> e_val

  | ([], Some l_val, e) ->
    let e_len = Simplify.simplify (L.get_len e) in
    begin match S.greater_equal_len_answer e_len l_val with
    | S.Yes ->
      let e' = Simplify.simplify (Range (e, l_val, Simplify.minus e_len l_val)) in
      Simplify.simplify (Concat ([e_val; e']))
    (* here we essentially replace e by undef which is sound *)
    | S.No -> e_val
    | S.Maybe ->
      fail "update: cannot decide which is greater: %s or %s" (E.to_string e_len) (E.to_string l_val)
    end

  | (pos, l_val, Concat (e :: es)) when S.greater_equal_len (L.get_len e) step ->
    (* At this point [pos] starts with something that definitely goes into a deeper
       segment.  Thus it is safe to pass only the first element down - the right thing
       happens even if [l_val = Infty].  *)
    let e' = update pos step l_val e e_val in
    Simplify.simplify (Concat (e' :: es))

  | (((Field _ | Attr _), step') :: _, l_val, e) ->
    let e_old = Simplify.simplify (Range (e, E.zero, step)) in
    let e_new = Struct (Str_map.empty, Str_map.empty, step, e_old) in
    update pos step' l_val e_new e_val

(* Last resort: try to overwrite the value completely *)
(* | (((Field _, _) | (Attr _, _)) :: _, _) -> update pos step l_val (Concat []) e_val *)

(* | _ -> fail "update: cannot write through pointer" *)

let update pos step l_val e_host e_val =
  push_debug "update";
  let result = update pos step l_val e_host e_val in
  pop_debug "update";
  result


(*************************************************)
(** {1 Execution Functions} *)
(*************************************************)

(**
  Simplifications are done on a case-by-case basis. It is important not to do them too early, in order
  to let things like Hint and Set_len be applied to whatever they are meant for.
*)

let take_stack : unit -> exp = fun () ->
  try
    let e = (Stack.pop stack) in
    debug "taking %s" (E.dump e);
    e
  with
    | Stack.Empty -> fail "take_stack: not enough elements on stack"

let take_all_stack : unit -> exp list = fun () ->
  try
    let es = (pop_all stack) in
    List.iter (fun e -> debug "taking %s" (E.dump e)) es;
    es
  with
    | Stack.Empty -> fail "take_all_stack: not enough elements on stack"


let take_n_stack : int -> exp list = fun n ->
  try
    let es = (pop_n stack n) in
    List.iter (fun e -> debug "taking %s" (E.dump e)) es;
    es
  with
    | Stack.Empty -> fail "take_n_stack: not enough elements on stack"

let to_stack : exp -> unit = fun e ->
  let e' = e in
  debug "pushing %s" (E.dump e');
  Stack.push e' stack

let to_mem : base -> exp-> unit = fun b e ->
  check_well_formed e;
  debug "storing %s" (E.dump e);
  mem := Base_map.add b e !mem

let add_stmt s =
  iml := !iml @ [Stmt.Comment !last_comment; s]

(*
  None means take all that's in the buffer.
*)
let load : len option -> exp -> unit = fun l p ->
  if interesting p then mark_enabled := true;
  debug "load, p: %s" (E.dump p);
  match p with
    | Ptr (b, pos) ->
      let e = Base_map.find b !mem in
      (* extract already does the simplification *)
      let e'= extract pos l e in
      to_stack e';
      mark_enabled := false

    | _ -> fail "load: ptr expected"

let get_step : offset list -> exp = comp snd List.last

let load_p : bool -> unit = fun use_step ->
  try
    match take_stack () with
      | Ptr (b, pos) as p -> load (if use_step then Some (get_step pos) else None) p
      | _ -> fail "load_mem: ptr expected"
  with
    | Not_found   -> fail "load_mem: reading uninitialised memory"
    | Stack.Empty -> fail "load_mem: not enough elements on stack"

let store : cvm -> unit = fun flag ->
  let get_length e =
    let l = L.get_len e in
    if l = Unknown then fail "store: cannot determine expression length"
    else l
  in
  let p = take_stack () in
  let e = take_stack () in

  if interesting p then mark_enabled := true;

  debug "store, p: %s" (E.dump p);
  debug "store, e: %s" (E.dump e);
  match p with
    | Ptr (b, pos) ->
      let e_host = try Base_map.find b !mem with Not_found -> Concat [] in
      let l_val = match flag with
        | Store_buf -> Some (get_length e)
        | Store_mem -> Some (get_step pos)
        | Store_all -> None
        | _ -> fail "store: impossible"
      in
      let step = match b with
        | Heap (id, len) -> len
        | _ -> snd (List.hd pos)
      in
      (* update performs simplification already *)
      to_mem b (update pos step l_val e_host e);
      mark_enabled := false

    | _ -> fail "store: pointer expected"

let value ~expected_type e =
  match E.type_of e with
  | Type.Bs_int itype as t ->
    (* begin match expected_sign with *)
    if itype <> expected_type
    then fail "Expected type %s in expression %s, got %s"
      (Int_type.to_string expected_type) (E.to_string e) (Type.to_string t)
    else E.Val (e, itype) |> Simplify.simplify
  | _ ->
    E.Val (e, expected_type)

let rec execute = function

  | Load_buf ->
    begin try
      let l = take_stack () in
      let p = take_stack () in
      (* The expected type is the type of the argument of Load_buf in C. *)
      load (Some (value ~expected_type:Int_type.size_t l)) p
    with
      | Not_found   -> fail "load_buf: reading uninitialised memory"
      | Stack.Empty -> fail "load_buf: not enough elements on stack"
    end

  | Load_mem -> load_p true
  | Load_all -> load_p false

  | Load_int ival ->
    to_stack (Int ival)

  | Load_str s ->
    to_stack (String s)

  | Load_char c ->
    (* Character literals in C have type int *)
    to_stack (E.BS (Char c, Int_type.int))

  | Load_stack_ptr name ->
    to_stack (Ptr (Stack name, [Index 0, Unknown]))

  | Load_heap_ptr id ->
    let l = take_stack () in
    to_stack (Ptr (Heap (id, l), [Flat E.zero, Unknown]))

  | In ->
    let l = take_stack () in
    let vname = Var.fresh "" in
    let v = Var vname in
    (* The expected type is the type of the argument of In in C *)
    let fact = S.eq_int [E.Len v; value ~expected_type:Int_type.size_t l] in
    (* Inputs are defined in IML. *)
    S.add_fact (S.is_defined v);
    S.add_fact fact;
    iml := !iml @ [Stmt.In [vname]; Test fact];
    to_stack v

  | New ->
    let vname = Var.fresh "" in
    let v = Var vname in
    let l, t = match take_n_stack 2 with
      | [Int i; String s] when i = -1L -> Var (Var.fresh "unknown"), Named (s, None)
      | [Int i; String ""]             -> Int i, Fixed (Int64.to_int i)
      | [Int i; String s]              -> Int i, Named (s, Some (Fixed (Int64.to_int i)))
      | es ->
        fail "New: length followed by typename expected on stack, instead found %s"
          (E.dump_list es)
    in
    iml := !iml @ [Stmt.New (vname, t)];
    S.add_fact (S.is_defined v);
    S.add_fact (S.eq_int [E.len v; l]);
    to_stack v

  | Env v ->
    to_stack (Var v)

  | Field_offset s ->
    begin match take_stack () with
      | Ptr (b, pos) -> to_stack (Ptr (b, pos @ [(Field s, Unknown)]))
      | _ ->  fail "field_offset: pointer expected"
    end

  | Ctx_offset s ->
    begin match take_stack () with
        | Ptr (b, pos) -> to_stack (Ptr (b, pos @ [(Attr s, Unknown)]))
        | _ ->  fail "ctx_offset: pointer expected"
    end

  | Index_offset itype ->
    begin
      let e = take_stack () in
      (* FIXME: loss of precision because of Int64 conversion *)
      (* This seems to be what 6.5.6 of the standard implies. *)
      match take_stack (), S.eval (value ~expected_type:itype e) with
        | (Ptr (b, pos), Some i) -> to_stack (Ptr (b, pos @ [(Index i, Unknown)]))
        | (Ptr _, _)             -> fail "index_offset: only concrete indices supported for now"
        | _ ->  fail "index_offset: pointer expected"
     end

  (*
  | Apply_all s ->
    let args = take_all_stack () in
    to_stack (Sym (Sym.of_string s, args))
  *)

  | Apply s ->
    let sym = Sym.of_string s in
    let args = take_n_stack (Sym.arity sym) in
    let args =
      match sym with
      | Fun _ -> List.map args ~f:Simplify.full_simplify
      | _ -> args
    in
    let e' = Sym (sym, args) in
    to_stack e'

  | Truth ->
    let e = take_stack () in
    to_stack (E.truth e)

  | Dup ->
    let e = take_stack () in
    to_stack e; to_stack e

  | Len ->
    let e = take_stack() in
    to_stack (E.Len e)

  | BS itype ->
    let e = take_stack() in
    to_stack (E.BS (e, itype))

  | Val itype ->
    let e = take_stack () in
    to_stack (Simplify.simplify (E.Val (e, itype)))

  | In_type tname ->
    let t = Type.of_string tname in
    let e = take_stack() in
    to_stack (S.in_type e t)

  | Apply_nondet ->
    begin match take_stack () with
      | Sym (Fun (s, n), args) -> to_stack (Sym (Nondet_fun (s, Var.fresh_id "nondet", n), args))
      | Ptr (Stack name, pos)  -> to_stack (Ptr (Stack (name ^ "[" ^ (string_of_int (increment cur_ptr_id)) ^ "]"), pos))
      | e -> fail "Nondet: unexpected value on stack: %s" (E.to_string e)
    end

  | Append ->
    let args = take_n_stack 2 in
    to_stack (Simplify.simplify (Concat args))

  | Event (name, nargs) ->
    let args = take_n_stack nargs |> List.map ~f:Simplify.full_simplify in
    iml := !iml @ [Stmt.Event (name, args)] (* [Sym (("event", Prefix), [e], Unknown, Det)] *)

  | Out ->
    let e = take_stack () |> Simplify.full_simplify in
    iml := !iml @ [Stmt.Out [e]]

  | Branch bdir ->
    let e = take_stack () |> Simplify.full_simplify in
    debug "branch: %s" (E.dump e);
    if not (E.is_concrete e) then
    begin
      debug "branch is not concrete";
      let e = if bdir = 1L then e else S.not e in
      if not (S.is_true e) then
      begin
        debug "branch has non-constant condition, adding test statement";
        add_stmt (Test e);
        S.add_fact e
      end
    end

  | Assume ->
    let e = take_stack () in
    (* This is a bit stupid: we often cannot simplify an expression before assuming it,
       because parts of it may be undefined. *)
    S.add_fact e;
    let e = Simplify.full_simplify e in
    debug "assume: %s" (E.dump e);
    add_stmt (Stmt.Assume e)

  | Hint h ->
    let e = take_stack () |> Simplify.full_simplify  in
    let vname = Var.fresh h in
    let v = Var vname in
    S.add_fact (S.eq_bitstring [v; e]);
    iml := !iml @ [Let (Pat.T.VPat vname, Annotation(Name vname, e))];
    to_stack v;
    debug "attaching hint %s to %s" h (E.dump e)

  | Type_hint t ->
    let e = take_stack () in
    debug "attaching type hint %s to %s" t (E.dump e);
    to_stack (Annotation (E.Type_hint (Type.of_string t), e))

  | Set_ptr_step ->

    let flatten : offset -> offset_val = function
      | (Flat e,  step) -> Flat e
      | (Index i, step) -> Flat (Simplify.prod [step; (E.int i)])
        (* The logic here is that Field is already flat in the sense that the offset value is independet of step *)
      | (Field f, step) -> Field f
        (* fail "set_ptr_step: trying to flatten a field offset" *)
      | (Attr _, _) -> fail "set_ptr_step: trying to flatten an attribute"
    in

    let rec bubble_up : offset -> pos -> pos = fun (ov, l) -> function
      | (ov', l') :: pos' as pos ->
        if S.greater_equal_len l l' then

          if Simplify.is_zero_offset_val ov' then
            bubble_up (ov, l) pos'

          else if Simplify.is_zero_offset_val ov then
            if S.equal_int l l' then
              pos
            else
              bubble_up (flatten (ov', l'), l) pos'

          else
            if S.equal_int l l' && (Simplify.is_field_offset_val ov) && (Simplify.is_field_offset_val ov') then
              (ov, l) :: pos
            else fail "set_ptr_step: trying to merge two nonzero offsets"

          (*
          else if S.equal_len l l' then
            if is_zero_offset_val ov then
              pos
            else if is_field_offset_val ov then
              (ov, l) :: pos
            else
              fail "set_ptr_step: trying to delete a non-E.zero offset (1)"
          else
            fail "set_ptr_step: trying to delete a non-E.zero offset"
          *)

        else
          (ov, l) :: pos

      | [] -> [(ov, l)]
    in

    let set_step : len -> pos -> pos = fun l -> function
      | (ov, _) :: pos' -> bubble_up (ov, l) pos'
      | [] -> fail "set_ptr_step: empty offset list"
        (* This unfortunately does not work, because of pointer-to-pointer casts *)
        (* | _ ->  fail "set_ptr_step: step already present" *)
    in

    let l = take_stack () in
    (*
        Simplification needed because we want to remove casts from pointers.
    *)
    let e = match Simplify.simplify (take_stack ()) with
      | Ptr (b, pos) -> Ptr (b, rev (set_step l (rev pos)))
      | _ -> fail "set_ptr_step: pointer expected"
    in
    to_stack e

  | Done ->
    let e = take_stack () in
    (*
    let l = fresh_len e in
    S.add_fact (S.ge l E.zero);
    let e = L.set_len e l in
    *)
    let e = Simplify.full_simplify e in
    debug "Done, simplified: %s" (E.dump e);
    (* debug ("do_done, with new len: " ^ E.dump e); *)
    check_well_formed e;
    to_stack e;
    if E.is_length e then S.add_fact (S.ge e E.zero)

  | Store_buf -> store Store_buf
  | Store_mem -> store Store_mem
  | Store_all -> store Store_all

  | Clear ->
    ignore (take_stack ())

  | Copy_ctx ->
      execute Load_mem;
      let e_from = take_stack () in
      let p_to   = take_stack () in
      execute Load_mem;
      let e_to   = take_stack () in
      begin match (e_from, e_to) with
        | (Struct (_, attrs, _, _), Struct (fields, _, len, e_old)) ->
          (* FIXME: no need for simplification *)
          to_stack (Struct (fields, attrs, len, e_old));
          to_stack p_to;
          execute Store_mem;

        | _ -> fail "copy_ctx: two structure pointers expected"
      end

  | Call (fname, nargs) ->
    called_functions := !called_functions @ [fname];

    increase_indent ();

    Stack.push (Printf.sprintf "%s[%d, %s]" fname !call_id !last_comment) call_stack;
    call_id := !call_id + 1;
    debug "# Entering %s, new call stack:" fname;
    dump_call_stack ();
    debug ("# execution stack:");
    dump_stack ();
    if not (is_interface_fun fname) && Stack.length stack != nargs then
      warn "Wrong number of elements on stack when entering %s" fname

  | Return ->
    let fname = Stack.pop call_stack in
    debug "returning from %s" fname;
    decrease_indent ()

  | Comment -> ()


(*************************************************)
(** {1 Execution Loop} *)
(*************************************************)

let execute_file : in_channel -> iml = fun file ->

  let rec execute' = fun () ->
    let line = input_line file in
    let toks = words line in
    if length toks = 0 then fail "empty instruction: %s" line;
    let cmd =
      try match List.hd toks with
          | "//"             -> last_comment := line; warning_location := line; Comment
          | "LoadBuf"        -> Load_buf
          | "LoadMem"        -> Load_mem
          | "LoadAll"        -> Load_all
          | "LoadInt"        -> Load_int (Int64.of_string (nth toks 1))
            (* TODO: write full int types in crestify? *)
          | "BS_signed"      -> BS (Int_type.create `Signed (int_of_string (nth toks 1)))
          | "BS_unsigned"    -> BS (Int_type.create `Unsigned (int_of_string (nth toks 1)))
          | "Val_signed"     -> Val (Int_type.create `Signed (int_of_string (nth toks 1)))
          | "Val_unsigned"   -> Val (Int_type.create `Unsigned  (int_of_string (nth toks 1)))
          | "LoadStr"        -> Load_str (input_line file)
          | "LoadChar"       -> Load_char (nth toks 1).[0]
          | "LoadStackPtr"   -> Load_stack_ptr (nth toks 1) (* (int_of_string (nth toks 2)) *)
          | "LoadHeapPtr"    -> Load_heap_ptr (int_of_string (nth toks 1))
          | "In"             -> In
          | "New"            -> New
          | "Env"            -> Env (nth toks 1)
          | "FieldOffset"    -> Field_offset (nth toks 1)
          | "CtxOffset"      -> Ctx_offset (nth toks 1)
          | "IndexOffset"    -> Index_offset (Int_type.of_string (input_line file))
          (* | "Apply_all"       -> Apply_all (nth toks 1) *)
          | "Apply"          -> Apply (input_line file)
          | "Dup"            -> Dup
          | "Len"            -> Len
          | "Truth"          -> Truth
          | "InType"         -> In_type (nth toks 1)
          | "Nondet"         -> Apply_nondet
          (* | "Concrete_result" -> Concrete_result (Int64.of_string (nth toks 1)) *)
          | "Append"         -> Append
          | "Event"          -> Event (nth toks 1, int_of_string (nth toks 2))
          | "Branch"         -> Branch (Int64.of_string (nth toks 1))
          | "Assume"         -> Assume
          | "Hint"           -> Hint (nth toks 1)
          | "TypeHint"       -> Type_hint (nth toks 1)
          | "SetPtrStep"     -> Set_ptr_step
          | "Done"           -> Done
          | "StoreBuf"       -> Store_buf
          | "StoreMem"       -> Store_mem
          | "StoreAll"       -> Store_all
          | "Out"            -> Out
          | "Clear"          -> Clear
          | "CopyCtx"        -> Copy_ctx
          | "Call"           -> Call (nth toks 1, int_of_string (nth toks 2))
          | "Return"         -> Return
                                (* Using failwith as this will be caught outside and fail invoked then *)
          | _                -> failwith (Printf.sprintf "execute: unknown instruction: %s" line)
      with
        | _ -> fail "wrong number of arguments or unknown instruction: %s" line
    in
    begin match cmd with
      | Call _ | Return -> ()
      | Apply s -> debug "Apply %s" s
      | Load_str s -> debug "Load_str %s" s
      | _ -> debug "%s" line
    end;
    debug "stack depth = %s" (string_of_int (Stack.length stack));
    debug "instruction %d" !done_instr;
    execute cmd;
    (* if (line <> "Indent") && (line <> "Dedent") then *)
    done_instr := !done_instr + 1;
    execute' ()
  in

  make_assumptions ();
  try with_debug "execute" execute' () with End_of_file -> ();

  if Stack.length stack <> 1 then
    fail "Expecting a single element on stack (return of main)";

  (* return (); *)
  let iml = !iml in (* List.map deep_simplify  *)
  reset_state ();
  iml

(*************************************************)
(** {1 Marshalling} *)
(*************************************************)

let raw_out: out_channel -> iml -> iml -> unit = fun c client server ->
  output_value c client;
  output_value c server;
  E.serialize_state c;
  output_value c !cur_ptr_id

let raw_in: in_channel -> iml * iml = fun c ->
  let client = input_value c in
  let server = input_value c in
  E.deserialize_state c;
  cur_ptr_id := input_value c;
  Var.unfresh (vars client);
  Var.unfresh (vars server);
  (client, server)

(* 980 lines *)
