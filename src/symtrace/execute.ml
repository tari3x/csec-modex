(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

(*
  Instructions:
    loading: 
      LoadInt val
      LoadStr "\n" val // assumed to be in hex already
      LoadStackPtr name id // name and unique id of variable; step init to 0 (invalid value)
      LoadHeapPtr id   // stack: buffer length; step init to 0
      LoadBuf // stack: ptr, len
      LoadMem // stack: ptr; use ptr step as len.
      LoadAll // stack: ptr; load the whole buffer
      // LoadAttr attr // stack: ptr; consumed
    offsets:
      FieldOffset fieldname // stack: ptr; step init to 0
      CtxOffset string      // pointer step set to 0, a context pointer should never be used with LoadMem (implement a check in update)
      IndexOffset           // stack: ptr, offset; step init to 0
    operations:
      ApplyAll sym
      ApplyN sym num_params
      Dup
      Nondet // For a symbol application on top of stack indicate that the application is not deterministic.
             // For a stack pointer assigns it a fresh id.
      ConcreteResult val
      Append // stack: first, second; second consumed
      Event
      Branch val
      Hint hint // does nothing if hint already exists
      SetLen // stack: exp, len
             // Only meant as a modifier during creation of new values. Does nothing if length already present.
      SetPtrStep // the size of the underlying type, 
                 // stack: ptr, step; step consumed
                 // Overwrites existing pointer step.
                 // Is necessary as a separate thing because of casts and the trick with flat char arrays
      Done // signals that we are done creating and customising a new value
    storing:
      StoreBuf // stack: exp, ptr; both consumed; use exp len
      StoreMem // stack: exp, ptr; both consumed; use pointer step
      StoreAll // stack: exp, ptr; both consumed; replace whatever the pointer points to, don't look at exp len
               // Currently used in two cases:
               // - To replace contents of zero-terminated expressions
               // - To store cryptographic attributes
      // StoreAttr attr // stack: exp, ptr; both consumed
      Clear // no warnings
      CopyCtx // stack: to, from; both consumed

*)


open List

open Types
open Utils
open Solver
(* has to come after List - dirty shadowing *)
open Exp


(*************************************************)
(** {1 State} *)
(*************************************************)

(** The symbolic memory *)
let mem : mem ref = ref BaseMap.empty

(** Symbolic execution stack *)
let stack: exp Stack.t = Stack.create () 

(** Branch checks, outputs, accepts *)
let events: exp list ref = ref []

(** Current call stack, used for debug purposes only *)
let callStack: string Stack.t = Stack.create ()

(** The ids for the calls on the call stack *)
let callId : int ref = ref 0

(** The number of instructions executed so far *)
let doneInstr : int ref = ref 0

let resetState : unit -> unit = fun () ->
  (* don't reset the Exp state *)
  mem := BaseMap.empty;
  Stack.clear stack;
  events := [];
  Stack.clear callStack;
  callId := 0

let lens : exp IntMap.t ref = ref IntMap.empty

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let makeAssumptions : unit -> unit = fun () ->
  (* FIXME: remove this later when all symbolic sizes are being used properly *)
  addFact (grEq (mkInt 8) ptrLen);
  addFact (gr ptrLen zero) 
  
let checkWellFormed : exp -> unit = fun e ->
  
  let rec checkDecreasing : pos -> unit = function
    | [_; (Attr _, _)] -> ()
    | (_, step1) :: ((_, step2) as os2) :: pos' ->
      if not (greaterEqualLen step1 step2) then
        fail ("checkWellFormed: offset step sequence not monotonous: " ^ dump e);
      checkDecreasing (os2 :: pos')

    | _ -> ()
  in
     
  let rec checkOrder : bool -> bool -> pos -> unit = fun seenIndex prevFlat -> function
    | ((Field _ | Attr _), _) :: pos' -> 
      if not seenIndex then
        fail ("checkPos: first field or attribute not preceded by index: " ^ dump e);
      if prevFlat then 
        fail ("checkPos: field or attribute preceded by flat: " ^ dump e);
      checkOrder seenIndex false pos'

    | (Index _, _) :: pos' ->
      if prevFlat then
        fail ("checkPos: index preceded by flat: " ^ dump e);
      checkOrder true false pos';
        
     | (Flat _, _) :: pos' -> checkOrder seenIndex true pos';

     | [] -> ()
  in               

  let isNoLen : exp -> exp = function
    | Sym (("len", _), _, _, _) -> fail ("checkWellFormed: len expression inside length: " ^ dump e)
    | e -> e
  in
  
  let visitLen : exp -> exp = function 
    | Sym (_, _, l, _) as e -> ignore (visitExpPre isNoLen l); e
    | e -> e
  in
  
  ignore (visitExpPre visitLen e);
  match e with
	  | Ptr (b, pos) -> 
    	(* checkOrder false false pos; *) 
	    checkDecreasing pos
    | Sym ((_, Infix), _, _, Nondet _) -> fail ("checkWellFormed: nondeterministic infix operator: " ^ dump e);
	  | e -> () (* getLen e <> Unknown *) (* see notes *)

(*************************************************)
(** {1 Length Caching} *)
(*************************************************)

let lenId : int ref = ref 0

(** This is so that identical expressions get identical lengths.
    You could say instead that identical expressions should only be obtained by duplication and drop this.  *)
let freshLen : exp -> exp = fun e ->
  let id = expId e in
  try IntMap.find id !lens
  with Not_found -> 
    let i = !lenId + 1 in
    lenId := i;
    (* 
       Needs to be nondeterministic in order not to be concretised. 
    *)
    let l = Sym (("lenvar", Prefix), [mkInt i], Unknown, freshNondet ()) in
    lens := IntMap.add id l !lens;
    l

(*************************************************)
(** {1 Dump} *)
(*************************************************)

(** Non-destructive *)
let dumpStack : unit -> unit = fun () -> Stack.iter (fun e -> debug ("# " ^ dump e)) stack

let dumpCallStack : unit -> unit = fun () -> Stack.iter (fun fname -> debug ("#  " ^ fname)) callStack

let failFun () =
  prerr_endline ("Instructions Executed: " ^ string_of_int !doneInstr); 
  debug ("call stack:");
  dumpCallStack ();
  debug ("execution stack:");
  dumpStack ();  
  debug ("generated events:");
  clipEnabled := false;
  iter prerr_endline (map dump (filter interestingEvent !events))

let _ = failFuns := !failFuns @ [failFun]

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
  Concat (map snd clist, freshDet ())

let flattenIndex : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (op "*" step (mkInt i)), step) :: pos
  | _ -> fail "flattenIndex"

(**
    Flatten until the next field or attribute offset.
*)
let rec flattenIndexDeep : pos -> pos = function
  | (Index i, step) :: pos -> (Flat (op "*" step (mkInt i)), step) :: flattenIndexDeep pos
  | (Flat e, step) :: pos -> (Flat e, step) :: flattenIndexDeep pos
  | pos -> pos


(**
    We assume that length is correct, in particular we don't check length when doing member extraction.
    
    If we need to apply a member offset to a concatenation, we try with the first element.
*)
let rec extract : pos -> len -> exp -> exp = fun pos l e ->
  debug ("extract, e_host: " ^ dump e);
  debug ("extract, pos: "    ^ String.concat ", " (map dumpOffset pos));
  debug ("extract, len: "    ^ dumpLen l);
  match (pos, e) with
    | ((Field s, _) :: os', Struct (fields, _, _, e_old)) -> 
      begin
	      try let e' = StrMap.find s fields in extract os' l e'
	      with Not_found -> extract pos l e_old
      end
      
    | ((Attr s, _) :: os', Struct (_, attrs, _, _)) -> 
      let e' = try StrMap.find s attrs 
               with Not_found -> fail ("extract: attribute not initialised: " ^ s) in
      extract os' l e'

    | ((Index i, step) :: pos', Array (cells, len, eltSize)) ->
      (* trying to catch a situation where pointer to the start of array is used to extract a big piece of array *)
      begin
      (* TODO: simplify the control here *)
      match greaterEqualLenAnswer eltSize l with
        | (No | Maybe) -> extract pos l (flattenArray cells) 
        | _ ->
		      if equalLen step eltSize then
		        let e' = try IntMap.find i cells
		                 with Not_found -> fail ("extract: array index not initialised: " ^ (string_of_int i)) in
		        extract pos' l e'
		      else if i = 0 && equal step len then
		        extract pos' l e
		      else if greaterEqualLen eltSize step then
		        let e' = try IntMap.find 0 cells
		                 with Not_found -> fail ("extract: cannot descend into first cell") in
		        extract pos l e'
		      else 
            extract pos l (flattenArray cells)
      end

    | ((Index i, step) :: pos', e) -> 
      extract (flattenIndex pos) l e

      (* TODO: need a special case when e is an array - check things and try to extract a single cell, otherwise fail.
         In fact, flatten the array if it's one. *)
    | ((Flat oe, _) :: os', e) -> 
      let e' = simplify (Range (e, oe, All, freshDet ())) in
      extract os' l e'

    | ([], e) -> simplify (Range (e, zero, l, freshDet ()))

    | (os, Concat (e' :: es, _)) -> extract os l e'

    | ((Field s, _) :: os', e) -> 
      (* We already pre-trim to length l, otherwise the length of the result is harder to compute. *)
      let e' = simplify (Range (e, Sym (("field_offset", Prefix), [String s], Unknown, freshDet ()), l, freshDet ())) in
      extract os' l e'
                  
    | _ -> fail "extract: cannot read through pointer"

(**
    Creates structures and members along the way if they don't exist.

    [l_val] is the length of the part of [e_host] that needs to be replaced with [e_val].    
    In case [l_val = All] the effect is to replace all data from [pos] until the end of the
    segment that [pos] points to.
    
    [step] gives the length for newly created structures and arrays.
    
    [e_host] is the rest of the current segment. This is important if [l_val = Infty].
    
    It is however not a requirement and sometimes the call can return expressions of other lengths.
*)
let rec update : pos -> len -> len -> exp -> exp -> exp = fun pos step l_val e_host e_val ->
  debug ("update, e_host: " ^ dump e_host);
  debug ("update, e_val: "  ^ dump e_val);
  debug ("update, pos: "    ^ String.concat ", " (map dumpOffset pos));
  debug ("update, step: " ^ dumpLen step);
  debug ("update, l_val: "  ^ dumpLen l_val);
  match (pos, e_host) with
    | ((Index i, step') :: pos', Array (cells, len, eltSize)) ->
      begin
      match greaterEqualLenAnswer eltSize l_val with
        | (No | Maybe) -> update pos step l_val (flattenArray cells) e_val
        | _ ->
		      if equalLen step' eltSize then
	          let e_elem = try IntMap.find i cells 
	                       with Not_found -> Concat ([], freshDet ()) in
	          let e' = update pos' step' l_val e_elem e_val in
	          Array (IntMap.add i e' cells, len, eltSize)
	          
		      else if i = 0 && equal step' len then
		        update pos' step' l_val e_host e_val
	          
		      (* else if greaterEqualLen eltSize step then
	          let e_elem = try IntMap.find 0 cells 
	                       with Not_found -> Concat [] in
	          let e' = update pos eltSize l_val e_elem e_val in
	          Array (IntMap.add 0 e' cells, len, eltSize) *)

          else update pos step l_val (flattenArray cells) e_val

		      (* else fail "update: index step incompatible with array element size" *)
      end

    | ((Index i, step') :: pos', Concat ([], _)) -> 
      if greaterEqualLen step' l_val then
	      let e_new = Array (IntMap.empty, step, step') in
	      update pos step l_val e_new e_val
      else
        update (flattenIndex pos) step l_val e_host e_val

      (* TODO: give it one more chance in case Concat [Array _]? *)
    | ((Index i, step') :: pos', e_host) -> 
      (* deep flattening here is slightly cosmetical - otherwise you get stuff like [payload_len|<{0 -> <{0 -> 7c}>}>] *)
      (* let e_new = update (flattenIndexDeep pos') step' l_val (Concat []) e_val in
      update (flattenIndex [Index i, step']) step (getLen e_new) e_host e_new *)
      update (flattenIndexDeep pos) step l_val e_host e_val

    | ((Field s, step') :: pos', Struct (fields, attrs, len, e_old)) -> 
      let e_field = try StrMap.find s fields 
                    with Not_found -> Concat ([], freshDet ()) in
      let e' = update pos' step' l_val e_field e_val in
      Struct (StrMap.add s e' fields, attrs, len, e_old)

    | ((Attr s, step') :: pos', Struct (fields, attrs, len, e_old)) -> 
      let e_attr = try StrMap.find s attrs 
                   with Not_found -> Concat ([], freshDet ()) in
      let e' = update pos' step' l_val e_attr e_val in
      Struct (fields, StrMap.add s e' attrs, len, e_old)

      (* FIXME: we might need to descend if position is zero *)
    | ((Flat oe, _) :: _, Array (cells, _, _)) -> 
      update pos step l_val (flattenArray cells) e_val

    | ((Flat oe, step') :: pos', e) -> 
      (* FIXME: you might want to flattenIndexDeep pos' in case oe > 0 *)
      let e1 = simplify (Range (e, zero, oe, freshDet ())) in
      let e2 = simplify (Range (e, oe, All, freshDet ())) in
      simplify (Concat ([e1; update pos' step' l_val e2 e_val], freshDet ()))

    | ([], e) -> 
      if l_val = All then e_val else 
      if (greaterEqualLen (getLen e) l_val) then
	      let e' = simplify (Range (e, l_val, All, freshDet ())) in
	      simplify (Concat ([e_val; e'], freshDet ()))
      (* here we essentially replace e by undef which is sound *)
      else e_val

    | (pos, Concat (e :: es, _)) when greaterEqualLen (getLen e) step -> 
      (* 
        At this point [pos] starts with something that definitely goes into a deeper segment.
        Thus it is safe to pass only the first element down - the right thing happens even if
        [l_val = Infty].
       *)
      let e' = update pos step l_val e e_val in
      simplify (Concat (e' :: es, freshDet ()))
    
    | (((Field _ | Attr _), _) :: _, e) -> 
      let e_old = simplify (Range (e, zero, step, freshDet ())) in
      let e_new = Struct (StrMap.empty, StrMap.empty, step, e_old) in
      update pos step l_val e_new e_val
    
    (* Last resort: try to overwrite the value completely *)
    (* | (((Field _, _) | (Attr _, _)) :: _, _) -> update pos step l_val (Concat []) e_val *)

    (* | _ -> fail "update: cannot write through pointer" *)


(*************************************************)
(** {1 Execution Functions} *)
(*************************************************)

(**
  Simplifications are done on a case-by-case basis. It is important not to do them too early, in order
  to let things like Hint and SetLen be applied to whatever they are meant for.
*)

let takeStack : unit -> exp = fun () ->
  let e = (Stack.pop stack) in
  debug ("taking " ^ dump e);
  e

let takeAllStack : unit -> exp list = fun () ->
  let es = (popAll stack) in
  iter (fun e -> debug ("taking " ^ dump e)) es;
  es

let takeNStack : int -> exp list = fun n ->
  let es = (popN stack n) in
  iter (fun e -> debug ("taking " ^ dump e)) es;
  es

let toStack : exp -> unit = fun e -> 
  let e' = e in
  debug ("pushing " ^ dump e');
  Stack.push e' stack

let toMem : base -> exp-> unit = fun b e -> 
  if !debugEnabled then checkWellFormed e;
  debug ("storing " ^ dump e);
  mem := BaseMap.add b e !mem

(* TODO: make it like store, with a boolean switch *)
let load : len -> exp -> unit = fun l p ->
  if interesting p then markEnabled := true;
  debug ("load, p: " ^ dump p);
  match p with
    | Ptr (b, pos) ->
      let e = BaseMap.find b !mem in
      (* extract already does the simplification *)
      let e'= extract pos l e in
      toStack e';
      markEnabled := false
    
    | _ -> fail "load: ptr expected"
  
let loadBuf : unit -> unit = fun () ->  
  try
    let l = takeStack () in
    let p = takeStack () in
    load l p
  with
    | Not_found   -> fail "loadBuf: reading uninitialised memory"
    | Stack.Empty -> fail "loadBuf: not enough elements on stack"

let loadP : bool -> unit -> unit = fun useStep -> fun () ->
  try
    match takeStack () with
      | Ptr (b, pos) as p -> load (if useStep then getStep pos else All) p
      | _ -> fail "loadMem: ptr expected"
  with
    | Not_found   -> fail "loadMem: reading uninitialised memory" 
    | Stack.Empty -> fail "loadMem: not enough elements on stack"
  
let loadMem = loadP true
let loadAll = loadP false

let loadInt : intval -> unit = fun ival ->
  toStack (Int (ival, Unknown))

let loadStr : string -> unit = fun s ->
  toStack (String s)

let loadStackPtr : string -> unit = fun name ->
  toStack (Ptr (Stack name, [Index 0, Unknown]))

let loadHeapPtr : id -> unit = fun id ->
  try
    let l = takeStack () in
    toStack (Ptr (Heap (id, l), [Flat zero, Unknown]))
  with
    | Stack.Empty -> fail "loadHeapPtr: not enough elements on stack" 
                   
let fieldOffset : string -> unit = fun s ->
  try
    match takeStack () with
      | Ptr (b, pos) -> toStack (Ptr (b, pos @ [(Field s, Unknown)]))
      | _ ->  fail "fieldOffset: pointer expected"
  with
    | Stack.Empty -> fail "fieldOffset: not enough elements on stack" 

let ctxOffset : string -> unit = fun s ->
  try
    match takeStack () with
      | Ptr (b, pos) -> toStack (Ptr (b, pos @ [(Attr s, Unknown)]))
      | _ ->  fail "ctxOffset: pointer expected"
   with
    | Stack.Empty -> fail "ctxOffset: not enough elements on stack" 

let indexOffset : unit -> unit = fun () ->
  try
    let e = takeStack () in
    match (takeStack (), getIntVal e) with
      | (Ptr (b, pos), Some i) -> toStack (Ptr (b, pos @ [(Index i, Unknown)]))
      | (_, None)              -> fail "indexOffset: only concrete indices supported for now"
      | _ ->  fail "indexOffset: pointer expected"
   with
    | Stack.Empty -> fail "indexOffset: not enough elements on stack" 


let applyAll : string -> unit = fun s ->
  let args = takeAllStack () in
  toStack (Sym ((s, Prefix), args, Unknown, freshDet ()))

let applyN : string -> int -> unit = fun s numargs ->
  let args =
    try takeNStack numargs 
    with Stack.Empty -> fail "applyOp: not enough elements on stack"
  and sym  = if numargs = 2 then (s, Infix) else (s, Prefix) in (* && s <> "cast" *) (* I actually like infix casts *) 
  let e' = Sym (sym, args, Unknown, freshDet ()) in
  toStack e'

let dup : unit -> unit = fun () ->
  try
    let e = takeStack () in
    toStack e; toStack e
  with
    | Stack.Empty -> fail "dup: not enough elements on stack"

let nondet : unit -> unit = fun () ->
  match takeStack () with
    | Sym (sym, args, len, Det _) -> toStack (Sym (sym, args, len, freshNondet ()))
    | Ptr (Stack name, pos)       -> toStack (Ptr (Stack (name ^ "[" ^ (string_of_int (freshId ())) ^ "]"), pos)) 
    | _ -> fail "nondet: unexpected value on stack" 

let concreteResult : intval -> unit = fun ival ->
  try
    match takeStack () with
        (* only concretise deterministic symbol applications *)
      | Sym (sym, args, len, Det _) as e ->
        if for_all isConcrete args 
        then toStack (Int (ival, len))
        else toStack e

      | e -> fail "concreteResult: Sym expected"
  with
    Stack.Empty -> fail "concreteResult: not enough elements on stack"

let append : unit -> unit = fun () ->
  let args = 
    try takeNStack 2 
    with Stack.Empty -> fail "append: not enough elements on stack"
  in
  toStack (simplify (Concat (args, freshDet ())))

let event : unit -> unit = fun () ->
  let e = 
    try takeStack ()
    with Stack.Empty -> fail "event: stack empty"
  in
  events := !events @ [e] (* [Sym (("event", Prefix), [e], Unknown, Det)] *)

let branch : intval -> unit = fun bdir ->
  let e =
    try takeStack ()
    with Stack.Empty -> fail "branch: stack empty"
  in
  if not (isConcrete e) then
  begin
	  let branchS = if bdir = 0L then "branchF" else "branchT" in
    let branch = Sym ((branchS, Prefix), [e], Unknown, freshNondet ()) in
    debug ("branch: " ^ dump branch);
	  (* each branch gets a different id, as we don't want them to unify in the final output *)
	  events := !events @ [branch];
    match bdir with
      | 1L -> addFact e
      | _  -> addFact (Sym (("!", Prefix), [e], Unknown, freshDet ()))
  end

let hint : string -> unit = fun h ->
  try
    let e = Stack.top stack in
    addHint e h;
    debug ("attaching hint " ^ h ^ " " ^ " to " ^ dump e)
  with
    Stack.Empty -> fail "hint: stack empty"
  
  
let doSetLen : unit -> unit = fun () ->
  try 
    let l = takeStack () in
    let e = takeStack () in
    toStack (setLen e l)
  with
    Stack.Empty -> fail "setLen: not enough elements on stack"

let setPtrStep : unit -> unit = fun () ->
  
  let flatten : offset -> offsetVal = function
    | (Flat e,  step) -> Flat e
    | (Index i, step) -> Flat (op "*" step (mkInt i))
      (* The logic here is that Field is already flat in the sense that the offset value is independet of step *)
    | (Field f, step) -> Field f 
      (* fail "setPtrStep: trying to flatten a field offset" *)
    | (Attr _, _) -> fail "setPtrStep: trying to flatten an attribute"
  in
  
  let rec bubbleUp : offset -> pos -> pos = fun (ov, l) -> function
    | (ov', l') :: pos' as pos -> 
      if greaterEqualLen l l' then
        
        if isZeroOffsetVal ov' then 
          bubbleUp (ov, l) pos'
          
        else if isZeroOffsetVal ov then
          if equalLen l l' then
            pos
          else
            bubbleUp (flatten (ov', l'), l) pos'

        else 
          if equalLen l l' && (isFieldOffsetVal ov) && (isFieldOffsetVal ov') then
            (ov, l) :: pos
          else fail "setPtrStep: trying to merge two nonzero offsets"
          
        (*
        else if equalLen l l' then
          if isZeroOffsetVal ov then
            pos
          else if isFieldOffsetVal ov then
            (ov, l) :: pos
          else
            fail "setPtrStep: trying to delete a non-zero offset (1)"
        else
          fail "setPtrStep: trying to delete a non-zero offset"
        *)
          
      else
        (ov, l) :: pos

    | [] -> [(ov, l)]
  in
  
  let setStep : len -> pos -> pos = fun l -> function 
    | (ov, _) :: pos' -> bubbleUp (ov, l) pos'
    | [] -> fail "setPtrStep: empty offset list" 
  in
  
  try 
    let l = takeStack () in
    (* 
        Simplification needed because we want to remove casts from pointers.
    *)
    let e = match simplify (takeStack ()) with
      | Ptr (b, pos) -> Ptr (b, rev (setStep l (rev pos)))
      | _ -> fail "setPtrStep: pointer expected"
    in
    toStack e 
  with 
    Stack.Empty -> fail "setPtrStep: not enough elements on stack"

let doDone : unit -> unit = fun () ->
  try 
    let e = takeStack () in
    let l = freshLen e in
    addFact (grEq l zero);
    let e = setLen e l in
    let e = simplify e in
    (* debug ("doDone, simplified: " ^ dump e); *)
    (* debug ("doDone, with new len: " ^ dump e); *)
    if !debugEnabled then checkWellFormed e;
    toStack e;
    if isLength e then addFact (grEq e zero)
    (* This is now done by stripping casts in solver *)
    (* match e' with 
      | Sym (("castToInt", _), [e''; _], _, _) -> addFact (eq [e'; e''])
      | _ -> ()
    *)
  with 
    Stack.Empty -> fail "done: not enough elements on stack"

type storeFlag = StoreAll | StoreMem | StoreBuf

let store : storeFlag -> unit -> unit = fun flag () ->
  let getLength e =
    let l = getLen e in
    if l = Unknown then fail "store: cannot determine expression length"
    else l 
  in
  try
    let p = takeStack () in
    let e = takeStack () in

    if interesting p then markEnabled := true; 

    debug ("store, p: " ^ dump p);
    debug ("store, e: " ^ dump e);
    match p with 
      | Ptr (b, pos) ->
        let e_host = try BaseMap.find b !mem with Not_found -> Concat ([], freshDet ()) in
        let l_val = match flag with
          | StoreBuf -> getLength e
          | StoreMem -> getStep pos
          | StoreAll -> All
        in
        let step = match b with
          | Heap (id, len) -> len
          | _ -> snd (hd pos)
        in
        (* update performs simplification already *)
        toMem b (update pos step l_val e_host e);
        markEnabled := false

      | _ -> fail "store: pointer expected"
  with 
    | Stack.Empty -> fail "store: not enough elements on stack"

let storeBuf : unit -> unit = store StoreBuf
let storeMem : unit -> unit = store StoreMem
let storeAll : unit -> unit = store StoreAll

                                                                         
let clear : unit -> unit = fun () ->
  try ignore (takeStack ())
  with 
    | Stack.Empty -> fail "clear: stack already empty"

              
let copyCtx : unit -> unit = fun () ->
  try
    loadMem ();
    let eFrom = takeStack () in
    let pTo   = takeStack () in
    loadMem ();
    let eTo   = takeStack () in
    match (eFrom, eTo) with
      | (Struct (_, attrs, _, _), Struct (fields, _, len, e_old)) ->
        (* FIXME: no need for simplification *)
        toStack (Struct (fields, attrs, len, e_old));
        toStack pTo;
        storeMem ();

      | _ -> fail "copyCtx: two structure pointers expected"
  
  with Stack.Empty -> fail "copyCtx: not enough elements on stack"
  
let call : string -> unit = fun fname ->
  if (!indent = 20) then
  begin
    debug "INDENT -20";
    indent := 0;
  end
  else indent := !indent + 2;

  Stack.push (fname ^ "[" ^ (string_of_int !callId) ^ "]") callStack;
  callId := !callId + 1;
  debug ("# Entering " ^ fname ^ ", new call stack:");
  dumpCallStack ();
  debug ("# execution stack:");  
  dumpStack ()
  
let return : unit -> unit = fun () ->
  debug "returning";
  ignore (Stack.pop callStack);
  
  if (!indent = 0) then
  begin
    indent := 20;
    debug "INDENT +20";
  end
  else indent := !indent - 2
  

(*************************************************)
(** {1 Execution Loop} *)
(*************************************************)

let exitStat : unit -> unit = fun () ->
  Yices.dump_context Solver_yices.ctx;
  exit 0

let execute : in_channel -> exp list = fun file ->
  let rec execute' = fun () ->
    let line = input_line file in
    let toks = words line in
    if length toks = 0 then
      fail ("empty instruction: " ^ line);
    if ((hd toks) <> "Call") && ((hd toks) <> "Return") then
      debug line;
    debug ("stack depth = " ^ (string_of_int (Stack.length stack)));
    debug ("instruction " ^ string_of_int !doneInstr);
    (*  
    prerr_endline ("instruction " ^ string_of_int !doneInstr);
    prerr_endline line;
    *)  
    begin
    match hd toks with
        | "//" -> ()
        | "LoadBuf"        -> loadBuf ()
        | "LoadMem"        -> loadMem ()
        | "LoadAll"        -> loadAll ()
        | "LoadInt"        -> loadInt (Int64.of_string (nth toks 1))
        | "LoadStr"        -> loadStr (input_line file)
        | "LoadStackPtr"   -> loadStackPtr (nth toks 1) (* (int_of_string (nth toks 2)) *)
        | "LoadHeapPtr"    -> loadHeapPtr (int_of_string (nth toks 1))
        | "FieldOffset"    -> fieldOffset  (nth toks 1)
        | "CtxOffset"      -> ctxOffset  (nth toks 1)
        | "IndexOffset"    -> indexOffset ()
        | "ApplyAll"       -> applyAll (nth toks 1)
        | "ApplyN"         -> applyN (nth toks 1) (int_of_string (nth toks 2))
        | "Dup"            -> dup ()
        | "Nondet"         -> nondet ()
        | "ConcreteResult" -> concreteResult (Int64.of_string (nth toks 1))
        | "Append"         -> append ()
        | "Event"          -> event ()
        | "Branch"         -> branch (Int64.of_string (nth toks 1))
        | "Hint"           -> hint (nth toks 1)
        | "SetLen"         -> doSetLen ()
        | "SetPtrStep"     -> setPtrStep ()
        | "Done"           -> doDone ()
        | "StoreBuf"       -> storeBuf ()
        | "StoreMem"       -> storeMem ()
        | "StoreAll"       -> storeAll ()
        | "Clear"          -> clear ()
        | "CopyCtx"        -> copyCtx ()
        | "Call"           -> call (nth toks 1)
        | "Return"         -> return ()
        | _                -> fail ("execute: unknown instruction: " ^ line)
    end;
    (* if (line <> "Indent") && (line <> "Dedent") then *)
    doneInstr := !doneInstr + 1;
    execute' ();
  in
  makeAssumptions ();
  (* call "main"; *)
  try execute' () with End_of_file -> ();
  (* return (); *)
  let es = !events in (* map deepSimplify  *)
  resetState ();
  es
  
