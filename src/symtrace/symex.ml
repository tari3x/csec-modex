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
module BaseMap = E.BaseMap

module L = struct
  let getLen e = E.Len e
end  

type mem = exp BaseMap.t 


type sym = string
type nargs = int

type cvm = 
    (* loading *)
  | LoadInt of intval
  | LoadStr of string (** assumed to be in hex already *)
  | LoadStackPtr of string (** name of variable; step init to 0 (invalid value) *)
  | LoadHeapPtr of int (** stack: buffer length; step init to 0 *)
  | LoadBuf (** stack: ptr, len *)
  | LoadMem (** stack: ptr; use ptr step as len. *)
  | LoadAll (** stack: ptr; load the whole buffer *)
    (* LoadAttr attr // stack: ptr; consumed *)
  | In  (** stack: len *)
  | New (** 
            stack: constant int length N, type alias T. Creates value of type Fixed (N, T).
            Special case: N = -1. Creates value of type (Named T).
         *)
  | Env of string
    
    (* offsetts *)
  | FieldOffset of string (** stack: ptr; step init to 0 *)
  | CtxOffset of string (** pointer step set to 0, 
                            a context pointer should never be used with LoadMem (implement a check in update) *)
  | IndexOffset (** stack: ptr, offset; step init to 0 *)
    
    (* operations *)
  | Apply of sym
  | Dup
  | Len
  | BS of IntType.t
  | Val of IntType.t
  | InType of string 
    
  | ApplyNondet (** For a symbol application on top of stack indicate that the application is not deterministic.
                    For a stack pointer assigns it a fresh id. *)

  (* | ConcreteResult of intval *)
  | Append (** stack: first, second; second consumed *)
  | Event of sym * nargs
  | Branch of intval
  | Assume
  | Hint of string 
  | TypeHint of string
  | SetPtrStep (** The size of the underlying type, 
                   stack: ptr, step; step consumed
                   Overwrites existing pointer step.
                   Is necessary as a separate thing because of casts and the trick with flat char arrays. *)
  | Done (** signals that we are done creating and customising a new value *)
    
    (* storing *)
  | StoreBuf (** stack: exp, ptr; both consumed; use exp len *)
  | StoreMem (** stack: exp, ptr; both consumed; use pointer step *)
  | StoreAll (** stack: exp, ptr; both consumed; replace whatever the pointer points to, don't look at exp len
                 Currently used in two cases:
                 - To replace contents of E.zero-terminated expressions
                 - To store cryptographic attributes *)
    (* StoreAttr attr // stack: exp, ptr; both consumed *)
  | Clear (** No warnings *)
  | CopyCtx (** stack: to, from; both consumed *)
  | Out
    
    (* misc *)
  | Call of string * nargs
  | Return
  | Comment


(*************************************************)
(** {1 State} *)
(*************************************************)

(** The symbolic memory *)
let mem : mem ref = ref BaseMap.empty

(** Symbolic execution stack *)
let stack: exp Stack.t = Stack.create () 

(** IML generated so far *)
let iml: iml ref = ref []

(** All the functions called so far, for debug purposes only *)
let calledFunctions: string list ref = ref []

(** Current call stack, used for debug purposes only *)
let callStack: string Stack.t = Stack.create ()

(** The ids for the calls on the call stack *)
let callId : int ref = ref 0

(** The ids used for stack pointers. *)
let curPtrId : int ref = ref 0

(** The number of instructions executed so far *)
let doneInstr : int ref = ref 0


let lastComment = ref ""

let resetState : unit -> unit = fun () ->
  (* don't reset the Exp state *)
  mem := BaseMap.empty;
  Stack.clear stack;
  iml := [];
  Stack.clear callStack;
  callId := 0

let lens : exp IntMap.t ref = ref IntMap.empty

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let ptrLen = Sym (PtrLen, [])

let makeAssumptions : unit -> unit = fun () ->
  (* FIXME: remove this later when all symbolic sizes are being used properly *)
  S.addFact (S.ge (E.int 8) ptrLen);
  S.addFact (S.gt ptrLen E.zero) 
  
let checkWellFormed : exp -> unit = fun e ->
  
  let rec checkDecreasing : pos -> unit = function
    | [_; (Attr _, _)] -> ()
    | (_, step1) :: ((_, step2) as os2) :: pos' ->
      if not (S.greaterEqualLen step1 step2) then
        fail "checkWellFormed: offset step sequence not monotonous: %s" (E.dump e);
      checkDecreasing (os2 :: pos')

    | _ -> ()
  in
    
  (* 
  (* check that all flat offsets have step 1 *)
  let rec checkFlatOffset: offset -> unit = function
    | (Flat _, step) -> 
      if not (S.equalLen step one) then
        fail ("checkWellFormed: a flat offset with step greater 1: " ^ E.dump e)
   | _ -> ()
  in
  *)
    
  (*
  (*
    One thing that prevents this from being enforced is that a step of an attribute offset
    isn't known, so an attribute offset doesn't bubble up past the trailing flat or index offset.
    
    I think this can be fixed by updating bubbleUp so that attributes always bubble up past
    flat offsets.
  *)   
  let rec checkOrder : bool -> bool -> pos -> unit = fun seenIndex prevFlat -> function
    | ((Field _ | Attr _), _) :: pos' -> 
      if not seenIndex then
        fail "checkPos: first field or attribute not preceded by index: %s" (E.dump e);
      if prevFlat then 
        fail "checkPos: field or attribute preceded by flat: %s" (E.dump e);
      checkOrder seenIndex false pos'

    | (Index _, _) :: pos' ->
      if prevFlat then
        fail "checkPos: index preceded by flat: %s" (E.dump e);
      checkOrder true false pos';
        
     | (Flat _, _) :: pos' -> checkOrder seenIndex true pos';

     | [] -> ()
  in               
  *)

  E.typecheck (E.typeOf e) e;
  
  match e with
	  | Ptr (b, pos) -> 
    	(* checkOrder false false pos; *) 
	    checkDecreasing pos;
      (* See notes about flat offset steps *)
      (* iter checkFlatOffset pos *)
	  | e -> () (* L.getLen e <> Unknown *) (* see notes *)

(*
  FIXME: merge when merging with CIL.
*)
let isInterfaceFun : string -> bool = fun s -> 
  List.mem s 
        ["event0"; "event1"; "event2"; "event3"; "event4"; "readenv"; "readenvE"; "readenvL";  
         "make_str_sym"; "make_sym"; "mute"; "unmute"; "fail";
         (* Internal interface functions: *)
         "load_buf"; "load_all"; "load_ctx"; "load_int"; "load_str"; 
         "symL"; "symN"; "symNE"; "input"; "newTN"; "newTL"; "newL";
         "varsym"; "var"; "varWithBUfInit"; "varL"; "output";  
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
      if debugEnabled () then prerr_endline (decorateDebug s)
  in
  Printf.ksprintf output a
    

(** Non-destructive. *)
let dumpStack : unit -> unit = fun () -> Stack.iter (fun e -> output "# %s" (E.dump e)) stack

let dumpCallStack : unit -> unit = fun () -> Stack.iter (fun fname -> output "#  %s" fname) callStack

let dumpMemory: unit -> unit = fun () ->
    
    let dumpCell: base -> exp -> unit = fun b e ->
        output "%s => %s"(E.baseToString b) (E.dump e)
    in
    
    BaseMap.iter dumpCell !mem  

let dumpCalledFuns: unit -> unit = fun () ->
  (* output called functions *)
  let f = open_out_bin "called.out" in
  List.iter (fun s -> output_string f (s ^ "\n")) !calledFunctions

let failfun () =
  fail_mode := true;
  output "Instructions Executed: %d" !doneInstr; 
  output "Last comment: %s" !lastComment;
  output ("Call stack:");
  dumpCallStack ();
  (* E.clipEnabled := false; *)
  output ("Execution stack:");
  dumpStack ();
  (*     
  debug ("symbolic memory:");
  dumpMemory ();
  debug ("generated iml:");  
  iter prerr_endline (map E.dump (filter interestingEvent !iml));
  *)
  (*
  (* FIXME: this should be done only once, given that we use catch now. *)
  dumpCalledFuns ();
  *)
  
  output "process = ";
  output "%s" (Iml.toString (procAndFilter !iml));
  fail_mode := false;
  let result = !fail_buf in
  fail_buf := "";
  result
  

let _ = failFuns := !failFuns @ [failfun]

(*************************************************)
(** {1 Symbolic Buffer Manipulation} *)
(*************************************************)

let flattenArray : exp IntMap.t -> exp = fun cells ->
  let rec check = fun len -> function
    | [] -> ()
    | [j, _] -> if j = len - 1 then () else fail "flatten: sparse arrays not supported yet"
    | _ :: xs -> check len xs
  in
  let clist = fold2list IntMap.fold (fun i e -> (i, e)) cells in
  check (length clist) clist;
  Simplify.simplify (Concat (List.map snd clist))

let flattenIndex : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (Simplify.prod [step; (E.int i)]), step) :: pos
  | _ -> fail "flattenIndex"

(**
    Flatten until the next field or attribute offset.
*)
let rec flattenIndexDeep : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (Simplify.prod [step; (E.int i)]), step) :: flattenIndexDeep pos
  | (Flat e, step) :: pos -> (Flat e, step) :: flattenIndexDeep pos
  | pos -> pos


(**
    We assume that length is correct, in particular we don't check length when doing member extraction.
    
    If we need to apply a member offset to a concatenation, we try with the first element.
    
    None in length position means extract everything until the end of the storage unit.
    FIXME: this will be simplified.
*)
let rec extract : pos -> len option -> exp -> exp = fun pos l e ->
  debug "extract, e_host: %s" (E.dump e);
  debug "extract, pos: %s" (String.concat ", " (List.map E.offsetToString pos));
  debug "extract, len: %s" (option_to_string E.dump l);
  begin match l with 
    | None -> ()
    | Some l -> E.typecheck (Type.Int) l
  end;
  match (pos, l, e) with
    | ((Field s, _) :: os', _, Struct (fields, _, _, e_old)) -> 
      begin
	      try let e' = StrMap.find s fields in extract os' l e'
	      with Not_found -> extract pos l e_old
      end
      
    | ((Attr s, _) :: os', _, Struct (_, attrs, _, _)) -> 
      let e' = try StrMap.find s attrs 
               with Not_found -> fail "extract: attribute not initialised: %s" s in
      extract os' l e'

    | ((Index i, step) :: pos', l, Array (cells, len, eltSize)) ->
      (* trying to catch a situation where pointer to the start of array is used to extract a big piece of array *)
      (* TODO: simplify the control here *)
      let inside_cell = match l with
        | Some l -> S.greaterEqualLenAnswer eltSize l = S.Yes
        | None -> false
      in
      if not inside_cell then 
        extract pos l (flattenArray cells)
      else
      begin 
		      if S.equalInt step eltSize then
		        let e' = try IntMap.find i cells
		                 with Not_found -> fail "extract: array index not initialised: %s" (string_of_int i) in
		        extract pos' l e'
		      else if i = 0 && S.equalInt step len then
		        extract pos' l e
		      else if S.greaterEqualLen eltSize step then
		        let e' = try IntMap.find 0 cells
		                 with Not_found -> fail "extract: cannot descend into first cell" in
		        extract pos l e'
		      else 
            extract pos l (flattenArray cells)
      end

    | ((Index i, step) :: pos', l, e) -> 
      extract (flattenIndex pos) l e

    | (pos, Some l, Array (cells, _, l')) ->
        if pos = [] && S.equalInt l l' then e else 
        extract pos (Some l) (flattenArray cells)

    | (pos, None, Array (cells, _, l')) ->
        extract pos None (flattenArray cells)

    | ((Flat oe, _) :: os', l, e) -> 
      let e' = Simplify.simplify (Range (e, oe, Simplify.minus (L.getLen e) oe)) in
      extract os' l e'

    | ([], None, e) -> e
    | ([], Some l, e) -> Simplify.simplify (Range (e, E.zero, l))

      (* FIXME *)
    | (os, l, Concat (e' :: es)) -> extract os l e'

    | ((Field s, _) :: os', Some l, e) -> 
      (* We already pre-trim to length l, otherwise the length of the result is harder to compute. *)
      let e' = Simplify.simplify (Range (e, Sym (Sym.T.FieldOffset, [String s]), l)) in
      extract os' (Some l) e'

    | _ -> fail "extract: cannot read through pointer"
      
let extract pos l e =
  increase_debug_depth ();
  let result = extract pos l e in
  decrease_debug_depth ();
  result

(**
    Creates structures and members along the way if they don't exist.

    [l_val] is the length of the part of [e_host] that needs to be replaced with [e_val].    
    In case [l_val = None] the effect is to replace all data from [pos] until the end of the
    segment that [pos] points to.
    
    [step] gives the length for newly created structures and arrays.
    
    [e_host] is the rest of the current segment. This is important if [l_val = Infty].
    
    It is however not a requirement and sometimes the call can return expressions of other lengths.
*)
let rec update : pos -> len -> len option -> exp -> exp -> exp = fun pos step l_val e_host e_val ->
  debug "update, e_host: %s" (E.dump e_host);
  debug "update, e_val: %s"  (E.dump e_val);
  debug "update, pos: %s" (String.concat ", " (List.map E.offsetToString pos));
  debug "update, step: %s" (E.dump step);
  debug "update, l_val: %s" (option_to_string E.dump l_val);
  begin match l_val with 
    | None -> ()
    | Some l -> E.typecheck (Type.Int) l
  end;
  match (pos, l_val, e_host) with
    | ((Index i, step') :: pos', None, Array (cells, len, eltSize)) ->
      update pos step None (flattenArray cells) e_val
  
    | ((Index i, step') :: pos', Some l_val, Array (cells, len, eltSize)) ->
      begin
      match S.greaterEqualLenAnswer eltSize l_val with
        | (S.No | S.Maybe) -> update pos step (Some l_val) (flattenArray cells) e_val
        | _ ->
		      if S.equalInt step' eltSize then
	          let e_elem = try IntMap.find i cells 
	                       with Not_found -> Concat [] in
	          let e' = update pos' step' (Some l_val) e_elem e_val in
	          Array (IntMap.add i e' cells, len, eltSize)
	          
		      else if i = 0 && S.equalInt step' len then
		        update pos' step' (Some l_val) e_host e_val
	          
		      (* else if S.greaterEqualLen eltSize step then
	          let e_elem = try IntMap.find 0 cells 
	                       with Not_found -> Concat [] in
	          let e' = update pos eltSize l_val e_elem e_val in
	          Array (IntMap.add 0 e' cells, len, eltSize) *)

          else update pos step (Some l_val) (flattenArray cells) e_val

		      (* else fail "update: index step incompatible with array element size" *)
      end

    | ((Index i, step') :: pos', None, Concat []) -> 
        update (flattenIndex pos) step None e_host e_val

    | ((Index i, step') :: pos', Some l_val, Concat []) -> 
      if S.greaterEqualLen step' l_val then
	      let e_new = Array (IntMap.empty, step, step') in
	      update pos step (Some l_val) e_new e_val
      else
        update (flattenIndex pos) step (Some l_val) e_host e_val

      (* TODO: give it one more chance in case Concat [Array _]? *)
    | ((Index i, step') :: pos', l_val, e_host) -> 
      (* deep flattening here is slightly cosmetical - otherwise you get stuff like [payload_len|<{0 -> <{0 -> 7c}>}>] *)
      (* let e_new = update (flattenIndexDeep pos') step' l_val (Concat []) e_val in
      update (flattenIndex [Index i, step']) step (L.getLen e_new) e_host e_new *)
      update (flattenIndexDeep pos) step l_val e_host e_val

    | ((Field s, step') :: pos', l_val, Struct (fields, attrs, len, e_old)) -> 
      let e_field = try StrMap.find s fields 
                    with Not_found -> Concat [] in
      let e' = update pos' step' l_val e_field e_val in
      Struct (StrMap.add s e' fields, attrs, len, e_old)

    | ((Attr s, step') :: pos', l_val, Struct (fields, attrs, len, e_old)) -> 
      let e_attr = try StrMap.find s attrs 
                   with Not_found -> Concat [] in
      let e' = update pos' step' l_val e_attr e_val in
      Struct (fields, StrMap.add s e' attrs, len, e_old)

      (* FIXME: we might need to descend if position is E.zero *)
    | ((Flat oe, _) :: _, l_val, Array (cells, _, _)) -> 
      update pos step l_val (flattenArray cells) e_val

      (* 
        We follow the assumption that a flat offset has step 1.
        If we want to create a structure below this offset, we better inherit the 
        structure size (pointer step) from above. 
      *)
    | ((Flat oe, _) :: pos', l_val, e) -> 
      (* FIXME: you might want to flattenIndexDeep pos' in case oe > 0 *)
      let e1 = Simplify.simplify (Range (e, E.zero, oe)) in
      let e2 = Simplify.simplify (Range (e, oe, Simplify.minus (L.getLen e) oe)) in
      Simplify.simplify (Concat [e1; update pos' step l_val e2 e_val])

    | ([], None, e) -> e_val 

    | ([], Some l_val, e) -> 
      begin match S.greaterEqualLenAnswer (L.getLen e) l_val with
        | S.Yes -> 
  	      let e' = Simplify.simplify (Range (e, l_val, Simplify.minus (L.getLen e) l_val)) in
  	      Simplify.simplify (Concat ([e_val; e']))
          (* here we essentially replace e by undef which is sound *)
        | S.No -> e_val
        | S.Maybe -> 
          fail "update: cannot decide which is greater: %s or %s" (E.toString (L.getLen e)) (E.toString l_val)
      end 

    | (pos, l_val, Concat (e :: es)) when S.greaterEqualLen (L.getLen e) step -> 
      (* 
        At this point [pos] starts with something that definitely goes into a deeper segment.
        Thus it is safe to pass only the first element down - the right thing happens even if
        [l_val = Infty].
       *)
      let e' = update pos step l_val e e_val in
      Simplify.simplify (Concat (e' :: es))
    
    | (((Field _ | Attr _), step') :: _, l_val, e) -> 
      let e_old = Simplify.simplify (Range (e, E.zero, step)) in
      let e_new = Struct (StrMap.empty, StrMap.empty, step, e_old) in
      update pos step' l_val e_new e_val
    
    (* Last resort: try to overwrite the value completely *)
    (* | (((Field _, _) | (Attr _, _)) :: _, _) -> update pos step l_val (Concat []) e_val *)

    (* | _ -> fail "update: cannot write through pointer" *)

let update pos step l_val e_host e_val =
  increase_debug_depth ();
  let result = update pos step l_val e_host e_val in
  decrease_debug_depth ();
  result


(*************************************************)
(** {1 Execution Functions} *)
(*************************************************)

(**
  Simplifications are done on a case-by-case basis. It is important not to do them too early, in order
  to let things like Hint and SetLen be applied to whatever they are meant for.
*)

let takeStack : unit -> exp = fun () ->
  try
    let e = (Stack.pop stack) in
    debug "taking %s" (E.dump e);
    e
  with 
    | Stack.Empty -> fail "takeStack: not enough elements on stack"

let takeAllStack : unit -> exp list = fun () ->
  try
    let es = (popAll stack) in
    List.iter (fun e -> debug "taking %s" (E.dump e)) es;
    es
  with 
    | Stack.Empty -> fail "takeAllStack: not enough elements on stack"
    

let takeNStack : int -> exp list = fun n ->
  try
    let es = (popN stack n) in
    List.iter (fun e -> debug "taking %s" (E.dump e)) es;
    es
  with 
    | Stack.Empty -> fail "takeNStack: not enough elements on stack"

let toStack : exp -> unit = fun e -> 
  let e' = e in
  debug "pushing %s" (E.dump e');
  Stack.push e' stack

let toMem : base -> exp-> unit = fun b e -> 
  if debugEnabled () then checkWellFormed e;
  debug "storing %s" (E.dump e);
  mem := BaseMap.add b e !mem

let addStmt s = 
  iml := !iml @ [Stmt.Comment !lastComment; s]

(*
  None means take all that's in the buffer.
*)
let load : len option -> exp -> unit = fun l p ->
  if interesting p then markEnabled := true;
  debug "load, p: %s" (E.dump p);
  match p with
    | Ptr (b, pos) ->
      let e = BaseMap.find b !mem in
      (* extract already does the simplification *)
      let e'= extract pos l e in
      toStack e';
      markEnabled := false
    
    | _ -> fail "load: ptr expected"

let getStep : offset list -> exp = comp snd last

let loadP : bool -> unit = fun useStep ->

  try
    match takeStack () with
      | Ptr (b, pos) as p -> load (if useStep then Some (getStep pos) else None) p
      | _ -> fail "loadMem: ptr expected"
  with
    | Not_found   -> fail "loadMem: reading uninitialised memory" 
    | Stack.Empty -> fail "loadMem: not enough elements on stack"

let store : cvm -> unit = fun flag ->
  let getLength e =
    let l = L.getLen e in
    if l = Unknown then fail "store: cannot determine expression length"
    else l 
  in
  let p = takeStack () in
  let e = takeStack () in

  if interesting p then markEnabled := true; 

  debug "store, p: %s" (E.dump p);
  debug "store, e: %s" (E.dump e);
  match p with 
    | Ptr (b, pos) ->
      let e_host = try BaseMap.find b !mem with Not_found -> Concat [] in
      let l_val = match flag with
        | StoreBuf -> Some (getLength e)
        | StoreMem -> Some (getStep pos)
        | StoreAll -> None
        | _ -> fail "store: impossible"
      in
      let step = match b with
        | Heap (id, len) -> len
        | _ -> snd (List.hd pos)
      in
      (* update performs simplification already *)
      toMem b ( (* silent *) (update pos step l_val e_host) e);
      markEnabled := false

    | _ -> fail "store: pointer expected"

let rec execute = function

  | LoadBuf ->
    begin try
      let l = takeStack () in
      let p = takeStack () in
      load (Some (E.Val (l, IntType.Unsigned))) p
    with
      | Not_found   -> fail "loadBuf: reading uninitialised memory"
      | Stack.Empty -> fail "loadBuf: not enough elements on stack"
    end

  | LoadMem -> loadP true
  | LoadAll -> loadP false

  | LoadInt ival ->
    toStack (Int ival)

  | LoadStr s ->
    toStack (String s)

  | LoadStackPtr name ->
    toStack (Ptr (Stack name, [Index 0, Unknown]))

  | LoadHeapPtr id ->
    let l = takeStack () in
    toStack (Ptr (Heap (id, l), [Flat E.zero, Unknown]))

  | In ->
    let l = takeStack () in
    let vname = Var.fresh "" in
    let v = Var vname in
    let fact = S.eqInt [E.Len v; E.Val (l, IntType.Unsigned)] in
    (* Inputs are defined in IML. *)
    S.addFact (S.isDefined v);
    S.addFact fact;
    iml := !iml @ [Stmt.In [vname]; GenTest fact];
    toStack v

  | New ->
    let vname = Var.fresh "" in
    let v = Var vname in
    let t = match takeNStack 2 with
      | [Int i; String s] when i = -1L -> Named (s, None)
      | [Int i; String ""]             -> Fixed (Int64.to_int i)
      | [Int i; String s]              -> Named (s, Some (Fixed (Int64.to_int i)))
      | es -> fail "New: length followed by typename expected on stack, instead found %s" (E.dumpList es)
    in
    iml := !iml @ [Stmt.New (vname, t)];
    toStack v
    
  | Env v ->
    toStack (Var v)

  | FieldOffset s ->
    begin match takeStack () with
      | Ptr (b, pos) -> toStack (Ptr (b, pos @ [(Field s, Unknown)]))
      | _ ->  fail "fieldOffset: pointer expected"
    end 

  | CtxOffset s ->
    begin match takeStack () with
        | Ptr (b, pos) -> toStack (Ptr (b, pos @ [(Attr s, Unknown)]))
        | _ ->  fail "ctxOffset: pointer expected"
    end 

  | IndexOffset ->
    begin 
      let e = takeStack () in
      (* FIXME: loss of precision because of Int64 conversion *)
      match takeStack (), Simplify.arithFold e with
        | (Ptr (b, pos), Int i)  -> toStack (Ptr (b, pos @ [(Index (Int64.to_int i), Unknown)]))
        | (Ptr _, _)             -> fail "indexOffset: only concrete indices supported for now"
        | _ ->  fail "indexOffset: pointer expected"
     end 

  (* 
  | ApplyAll s ->
    let args = takeAllStack () in
    toStack (Sym (Sym.ofString s, args))
  *)

  | Apply s ->
    let sym = Sym.ofString s in
    let args = takeNStack (Sym.arity sym) in 
    let e' = Sym (sym, args) in
    toStack e'

  | Dup ->
    let e = takeStack () in
    toStack e; toStack e

  | Len ->
    let e = takeStack() in
    toStack (E.Len e)
    
  | BS itype ->
    let e = takeStack() in
    toStack (E.BS (e, itype))

  | Val (s, _) ->
    let e = takeStack() in
    toStack (E.Val (e, s))
            
  | InType tname ->
    let t = Type.ofString tname in
    let e = takeStack() in
    toStack (S.inType e t)


  | ApplyNondet ->
    begin match takeStack () with
      | Sym (Fun (s, n), args) -> toStack (Sym (NondetFun (s, Var.freshId "nondet", n), args))
      | Ptr (Stack name, pos)  -> toStack (Ptr (Stack (name ^ "[" ^ (string_of_int (increment curPtrId)) ^ "]"), pos)) 
      | e -> fail "Nondet: unexpected value on stack: %s" (E.toString e) 
    end

  (* 
  | ConcreteResult ival ->
    begin match takeStack () with
          (* 
            Replace concrete expressions by their values.
            
            FIXME: should anything be concretised at all? Time to move away from it.
          *)
        | Sym (_, args) as e ->
          if E.isConcrete e 
          then toStack (Int ival) bla bla what about length here?
          else toStack e
  
        | e -> fail "concreteResult: Sym expected"
    end
  *)

  | Append ->
    let args = takeNStack 2 in
    toStack (Simplify.simplify (Concat args))

  | Event (name, nargs) ->
    let args = takeNStack nargs in
    iml := !iml @ [Stmt.Event (name, args)] (* [Sym (("event", Prefix), [e], Unknown, Det)] *)

  | Out ->
    let e = takeStack() in
    iml := !iml @ [Stmt.Out [e]]
    
  | Branch bdir ->
    let e = takeStack () in
    debug "branch: %s" (E.dump e);
    if not (E.isConcrete e) then
    begin
      debug "  branch is not concrete";
      let e = E.truth e in
      let e = if bdir = 1L then e else S.not e in
      if not (S.isTrue e) then
      begin
        debug "  branch is non-trivial, adding test statement"; 
        addStmt (GenTest e);
        S.addFact e
      end
    end

  | Assume ->
    let e = takeStack () in
    debug "assume: %s" (E.dump e);
    addStmt (Stmt.Assume e);
    S.addFact e

  | Hint h ->
    let e = takeStack () in
    let vname = Var.fresh h in
    let v = Var vname in
    S.addFact (S.eqBitstring [v; e]);
    iml := !iml @ [Let (Pat.T.VPat vname, Annotation(Name vname, e))];
    toStack v;
    debug "attaching hint %s to %s" h (E.dump e)
    
  | TypeHint t ->
    let e = takeStack () in
    debug "attaching type hint %s to %s" t (E.dump e);
    toStack (Annotation (E.TypeHint (Type.ofString t), e))
    
  | SetPtrStep ->
    
    let flatten : offset -> offsetVal = function
      | (Flat e,  step) -> Flat e
      | (Index i, step) -> Flat (Simplify.prod [step; (E.int i)])
        (* The logic here is that Field is already flat in the sense that the offset value is independet of step *)
      | (Field f, step) -> Field f 
        (* fail "setPtrStep: trying to flatten a field offset" *)
      | (Attr _, _) -> fail "setPtrStep: trying to flatten an attribute"
    in
    
    let rec bubbleUp : offset -> pos -> pos = fun (ov, l) -> function
      | (ov', l') :: pos' as pos -> 
        if S.greaterEqualLen l l' then
          
          if Simplify.isZeroOffsetVal ov' then 
            bubbleUp (ov, l) pos'
            
          else if Simplify.isZeroOffsetVal ov then
            if S.equalInt l l' then
              pos
            else
              bubbleUp (flatten (ov', l'), l) pos'
  
          else 
            if S.equalInt l l' && (Simplify.isFieldOffsetVal ov) && (Simplify.isFieldOffsetVal ov') then
              (ov, l) :: pos
            else fail "setPtrStep: trying to merge two nonzero offsets"
            
          (*
          else if S.equalLen l l' then
            if isZeroOffsetVal ov then
              pos
            else if isFieldOffsetVal ov then
              (ov, l) :: pos
            else
              fail "setPtrStep: trying to delete a non-E.zero offset (1)"
          else
            fail "setPtrStep: trying to delete a non-E.zero offset"
          *)
            
        else
          (ov, l) :: pos
  
      | [] -> [(ov, l)]
    in
    
    let setStep : len -> pos -> pos = fun l -> function 
      | (ov, _) :: pos' -> bubbleUp (ov, l) pos'
      | [] -> fail "setPtrStep: empty offset list" 
        (* This unfortunately does not work, because of pointer-to-pointer casts *)
        (* | _ ->  fail "setPtrStep: step already present" *)
    in
    
    let l = takeStack () in
    (* 
        Simplification needed because we want to remove casts from pointers.
    *)
    let e = match Simplify.simplify (takeStack ()) with
      | Ptr (b, pos) -> Ptr (b, rev (setStep l (rev pos)))
      | _ -> fail "setPtrStep: pointer expected"
    in
    toStack e 

  | Done ->
    let e = takeStack () in
    (*
    let l = freshLen e in
    S.addFact (S.ge l E.zero);
    let e = L.setLen e l in
    *)
    let e = Simplify.simplify e in
    debug "Done, simplified: %s" (E.dump e); 
    (* debug ("doDone, with new len: " ^ E.dump e); *)
    if debugEnabled () then checkWellFormed e;
    toStack e;
    if E.isLength e then S.addFact (S.ge e E.zero)

  | StoreBuf -> store StoreBuf
  | StoreMem -> store StoreMem
  | StoreAll -> store StoreAll

  | Clear ->
    ignore (takeStack ())

  | CopyCtx ->
      execute LoadMem;
      let eFrom = takeStack () in
      let pTo   = takeStack () in
      execute LoadMem;
      let eTo   = takeStack () in
      begin match (eFrom, eTo) with
        | (Struct (_, attrs, _, _), Struct (fields, _, len, e_old)) ->
          (* FIXME: no need for simplification *)
          toStack (Struct (fields, attrs, len, e_old));
          toStack pTo;
          execute StoreMem;
  
        | _ -> fail "copyCtx: two structure pointers expected"
      end
  
  | Call (fname, nargs) ->
    calledFunctions := !calledFunctions @ [fname];
  
    increase_indent ();
  
    Stack.push (Printf.sprintf "%s[%d, %s]" fname !callId !lastComment) callStack;
    callId := !callId + 1;
    debug "# Entering %s, new call stack:" fname;
    dumpCallStack ();
    debug ("# execution stack:");  
    dumpStack ();
    if not (isInterfaceFun fname) && Stack.length stack != nargs then
      warn "Wrong number of elements on stack when entering %s" fname
  
  | Return ->
    let fname = Stack.pop callStack in 
    debug "returning from %s" fname;
    decrease_indent ()
    
  | Comment -> ()
  

(*************************************************)
(** {1 Execution Loop} *)
(*************************************************)

let executeFile : in_channel -> iml = fun file ->

  let rec execute' = fun () ->
    let line = input_line file in
    let toks = words line in
    if length toks = 0 then fail "empty instruction: %s" line;
    let cmd = 
      try match List.hd toks with
          | "//"             -> lastComment := line; warning_location := line; Comment
          | "LoadBuf"        -> LoadBuf
          | "LoadMem"        -> LoadMem
          | "LoadAll"        -> LoadAll
          | "LoadInt"        -> LoadInt (Int64.of_string (nth toks 1))
          | "BS_signed"      -> BS (IntType.Signed, int_of_string (nth toks 1))
          | "BS_unsigned"    -> BS (IntType.Unsigned, int_of_string (nth toks 1))
          | "Val_signed"     -> Val (IntType.Signed, int_of_string (nth toks 1))
          | "Val_unsigned"   -> Val (IntType.Unsigned, int_of_string (nth toks 1))
          | "LoadStr"        -> LoadStr (input_line file)
          | "LoadStackPtr"   -> LoadStackPtr (nth toks 1) (* (int_of_string (nth toks 2)) *)
          | "LoadHeapPtr"    -> LoadHeapPtr (int_of_string (nth toks 1))
          | "In"             -> In
          | "New"            -> New
          | "Env"            -> Env (nth toks 1)
          | "FieldOffset"    -> FieldOffset (nth toks 1)
          | "CtxOffset"      -> CtxOffset (nth toks 1)
          | "IndexOffset"    -> IndexOffset 
          (* | "ApplyAll"       -> ApplyAll (nth toks 1) *)
          | "Apply"          -> Apply (input_line file)
          | "Dup"            -> Dup 
          | "Len"            -> Len
          | "InType"         -> InType (nth toks 1)
          | "Nondet"         -> ApplyNondet 
          (* | "ConcreteResult" -> ConcreteResult (Int64.of_string (nth toks 1)) *)
          | "Append"         -> Append 
          | "Event"          -> Event (nth toks 1, int_of_string (nth toks 2))
          | "Branch"         -> Branch (Int64.of_string (nth toks 1))
          | "Assume"         -> Assume
          | "Hint"           -> Hint (nth toks 1)
          | "TypeHint"       -> TypeHint (nth toks 1)
          | "SetPtrStep"     -> SetPtrStep
          | "Done"           -> Done
          | "StoreBuf"       -> StoreBuf
          | "StoreMem"       -> StoreMem
          | "StoreAll"       -> StoreAll
          | "Out"            -> Out
          | "Clear"          -> Clear
          | "CopyCtx"        -> CopyCtx
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
      | LoadStr s -> debug "LoadStr %s" s
      | _ -> debug "%s" line
    end;
    debug "stack depth = %s" (string_of_int (Stack.length stack));
    debug "instruction %d" !doneInstr;
    execute cmd;
    (* if (line <> "Indent") && (line <> "Dedent") then *)
    doneInstr := !doneInstr + 1;
    execute' ()
  in
  
  makeAssumptions ();
  try with_debug ~depth:0 execute' () with End_of_file -> ();
  
  if Stack.length stack <> 1 then
    fail "Expecting a single element on stack (return of main)";
    
  (* return (); *)
  let iml = !iml in (* List.map deepSimplify  *)
  resetState ();
  iml
  
(*************************************************)
(** {1 Marshalling} *)
(*************************************************)

let rawOut: out_channel -> iml -> iml -> unit = fun c client server ->
  output_value c client;
  output_value c server;
  E.serialize_state c;
  output_value c !curPtrId
  
let rawIn: in_channel -> iml * iml = fun c ->
  let client = input_value c in
  let server = input_value c in
  E.deserialize_state c;
  curPtrId := input_value c;
  Var.unfresh (vars client);
  Var.unfresh (vars server);
  (client, server)

(* 980 lines *)
