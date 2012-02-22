(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open Str
open List

open Types

(*************************************************)
(** {1 State} *)
(*************************************************)

(*
  NB When adding any state, do not forget to serialize it in Execute.rawOut.
*)

(** Routines to be called on failure *)
let failFuns : (unit -> unit) list ref = ref []

(** The ids used for stack pointers. *)
let curPtrId : int ref = ref 0

(** Used for expression ids. *)
let curExpId = ref 0

(** Used for expression tags. *)
let curTagId = ref 0

let debugEnabled = ref false

(** 
    If this is on, the debug lines in the trace will have "(mark)" in front.
    This can be used to extract an interesting portion of the trace with grep.
 *)
let markEnabled = ref false

let hints: string IntMap.t ref = ref IntMap.empty

(*************************************************)
(** {1 General Purpose} *)
(*************************************************)

let words : string -> string list = Str.split (regexp "[ \t]+")

let trim : string -> string = function s -> 
  replace_first (regexp "^[ \t\n]+") "" (replace_first (regexp "[ \t\n]+$") "" s)

let comp f g x = f (g x)

(** The range function *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

let filter_out : ('a -> bool) -> 'a list -> 'a list = fun p -> filter (fun a -> not (p a))

let remove : 'a -> 'a list -> 'a list = fun a -> filter_out (fun b -> a = b)

let rec replicate: int -> 'a -> 'a list = fun i a -> 
  if i = 0 then []
  else a :: replicate (i - 1) a

let nub: 'a list -> 'a list = fun l -> 
  let rec nub' = fun ls ->
    function
      | (x::xs) when mem x ls -> nub' ls xs
      | (x::xs) -> x :: nub' (x::ls) xs
      | [] -> []
  in
  nub' [] l

let findIndex : ('a -> bool) -> 'a list -> int = fun p xs -> 
  let rec find i = function
    | [] -> raise Not_found
    | x :: xs -> if p x then i else find (i + 1) xs
  in
  find 0 xs

let rec inverse_mem_assoc: 'b -> ('a * 'b) list -> bool = fun b -> function
  | (_, b') :: _ when b = b' -> true
  | _ :: xs -> inverse_mem_assoc b xs
  | [] -> false

let rec inverse_assoc: 'b -> ('a * 'b) list -> 'a = fun b -> function
  | (a, b') :: _ when b = b' -> a
  | _ :: xs -> inverse_assoc b xs
  | [] -> raise Not_found

let assoc_keys: ('a * 'b) list -> 'a list = fun l -> let l1, l2 = split l in l1

(* The order is deepest first *)
let rec popAll : 'a Stack.t -> 'a list = fun stack ->
  try
    let t = Stack.pop stack in
    popAll stack @ [t]
  with 
    Stack.Empty -> []

(* The order is deepest first *)
let rec popN : 'a Stack.t -> int -> 'a list = fun stack i ->
  if i = 0 then [] else
  let t = Stack.pop stack in    
  popN stack (i - 1) @ [t]

let peek : 'a Stack.t -> 'a = fun s -> 
  let a = Stack.pop s in 
  Stack.push a s;
  a

(*
  TODO: Remove after switching to 3.12 - they have new Map functions there.
*)
let fold2list : (('k -> 'a -> 'b -> 'b) -> 'm -> 'b -> 'b) -> ('k -> 'a -> 'c) -> 'm -> 'c list = fun foldF f m ->
  rev (foldF (fun k a cs -> (f k a) :: cs) m [])

(** Remove the first occurence *)
let rec del : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list = fun eq y -> function
  | []                  -> []
  | x :: xs when eq x y -> xs
  | x :: xs             -> x :: del eq y xs

(** Multiset difference *)
let rec multidiff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list = fun eq xs -> function
  | []      -> xs
  | y :: ys -> multidiff eq (del eq y xs) ys

let rec last : 'a list -> 'a = function
  | [x]     -> x
  | x :: xs -> last xs
  | []      -> failwith "last: empty list"

let indent = ref 0

let decorateDebug s = (if !markEnabled then "(mark)" else "") ^ (String.make !indent ' ') ^ s

let debug_plain : string -> unit = fun s ->
  if !debugEnabled then begin prerr_string (decorateDebug s); flush stderr end

let debug : string -> unit = fun s ->
  if !debugEnabled then prerr_endline (decorateDebug s)

let warn : string -> unit = fun s -> 
  if !debugEnabled then print_endline (decorateDebug ("WARN: " ^ s)) 
                   else prerr_endline (decorateDebug ("WARN: " ^ s)) 

let debugBracketTree : string -> unit = fun s ->
  let depth = ref 0 in

  let print = fun c ->
    match c with
	    | '(' | '{' -> 
        begin
          prerr_string ("\n" ^ (String.make (2 * !depth) ' '));
          depth := !depth + 1;
          prerr_string (String.make 1 c)
        end
	    | ')' | '}' -> 
        begin
          prerr_string (String.make 1 c);
          depth := !depth - 1;
          prerr_string ("\n" ^ (String.make (2 * !depth) ' '))          
        end
	    | _ -> prerr_string (String.make 1 c)
  in
  
  String.iter print s

let fail : string -> 'a = fun s -> 
  (* debug s; *)
  (* dumpStack (); *)
  iter (fun f -> f ()) !failFuns;
  prerr_endline ("failure: " ^ s); (* looks like failwith truncates the string on some occasions *)
  exit 1

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let freshId : int ref -> int = fun id ->
  id := !id + 1;
  if !id = 0 then fail "freshId: overflow"; 
  !id
      
(*************************************************)
(** {1 Dump} *)
(*************************************************)

let clipEnabled = ref true

let dumpTag : tag -> string = function
  | Det i    -> "Det" ^ (string_of_int i)
  | Nondet i -> "Nondet" ^ (string_of_int i)
  | NoTag    -> "NoTag"

let dumpBase : base -> string = function
  | Stack name    -> "stack " ^ name (* ^ "[" ^ string_of_int id ^ "]" *)
  | Heap (id, _)  -> "heap " ^ string_of_int id

let rec dumpLen = fun e -> dumpFull e

and dumpOffsetVal : offsetVal -> string = function
  | Field s -> "field " ^ s
  | Attr  s -> "attr " ^ s
  | Index i -> "index " ^ (string_of_int i)
  | Flat e  -> dumpFull e

and dumpOffset : offset -> string = function (ot, l) ->
  (dumpOffsetVal ot) ^ "(" ^ dumpLen l ^ ")"

and dumpFull : exp -> string = function
  | Int (ival, len) -> "i" ^ Int64.to_string ival ^ "<" ^ dumpLen len ^ ">"
  | String s -> s
  | Sym ((s, Prefix), es, len, id) -> 
      let idPart = match id with 
        | Det i    -> "[d" ^ string_of_int i ^ "]"
        | Nondet i -> "[" ^ string_of_int i ^ "]"
        | NoTag    -> "[-]"
      in
      s ^ idPart ^ "(" ^ String.concat ", " (map dumpFull es) ^ ")" ^ "<" ^ dumpLen len ^ ">"
        (* ^ "[" ^ string_of_int len ^ "," ^ string_of_int id ^ "]" *)
  | Sym ((s, Infix), es, len, tag) ->
      let len_dump = if s = "castToInt" then "<" ^ dumpLen len ^ ">" else "" in
      "(" ^ String.concat (" " ^ s ^ " ") (map dumpFull es) ^ ")" ^ len_dump
      (* ^ "[" ^ string_of_int len ^ "," ^ string_of_int id ^ "]" *)
  | Range (e, f, l, tag) -> "(" ^ dumpFull e ^ ")" ^ "{" ^ dumpLen f ^ "," ^ dumpLen l ^ ",tag = " ^ dumpTag tag ^ "}"
  | Concat (es, _) -> "(" ^ String.concat "|" (map dumpFull es) ^ ")"
  | Ptr (b, pos) -> "<<" ^ dumpBase b ^ "; " ^ String.concat ", " (map dumpOffset pos) ^ ">>"
  | Struct (fields, _, len, _) ->
      let showField name e = name ^ " ~> " ^ dumpFull e in
      "<{" ^ String.concat "; " (fold2list StrMap.fold showField fields) ^ "}>"
      ^ "<" ^ dumpLen len ^ ">"

  | Array (cells, len, step) -> 
      let showCell i e = string_of_int i ^ " ~> " ^ dumpFull e in
      "<{" ^ String.concat "; " (fold2list IntMap.fold showCell cells) ^ "}>"
      ^ "<" ^ dumpLen len ^ ">" ^ "(" ^ dumpLen step ^ ")"
      
  | Unknown -> "?"
  | All     -> "+"

let dump : exp -> string = fun e ->
  let s = dumpFull e in
  (*
  if String.length s > 100000 then 
  begin
    debugBracketTree s;
    fail "HUGE expression"
  end;
  *)  
  if not !markEnabled && !clipEnabled && String.length s > 1000 then 
    (String.sub s 0 1000) ^ " ... (clipped at 1000 symbols, full len: " ^ string_of_int (String.length s) ^ ")" 
  else s

let dumpList : exp list -> string = fun es -> "[" ^ String.concat ", " (map dump es) ^ "]"

let dumpProcess : exp list -> string = fun es -> String.concat "\n" (map dump es) ^ "\n"


(*************************************************)
(** {1 Traversal and Structure Manipulation} *)
(*************************************************)

let replaceArgs: exp list -> exp -> exp = fun es -> function
  | Sym ((f, fixity), _, len, tag) -> Sym ((f, fixity), es, len, tag)
  | e -> e 

(* TODO: rewrite the traversal functions in terms of this function *)
let mapChildren: (exp -> exp) -> exp -> exp = fun f e ->
  match e with
    (* | Sym ((("var" | "const" | "new" | "newT"), _), _, _, _) as e -> e *)
    | Sym (sym, es, len, tag) -> Sym (sym, map f es, f len, tag) 
    | Range (e, pos, len, tag) -> Range (f e, f pos, f len, tag)
    | Concat (es, tag) -> Concat (map f es, tag)
    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map f fields, StrMap.map f attrs, f len, e_old)
    | e -> e
  


(**
  Applies a function to all nodes in an expression, in preorder:
  [visitExpPre f e = map (visitExpPre f) (children (f e))]
  
  Does not go into lengths.
  
  Be careful: [f] should not be a function that strips layers off the expression. 
  This would result in skipping a layer. Use [visitExpPost] in that case.
  
  This function is useful for doing expanding substitutions.
*)
let rec visitExpBodyPre : (exp -> exp) -> exp -> exp = fun f e ->
  
  let visit = visitExpBodyPre f in

  match f e with
    | Sym ((("var" | "const" | "new" | "newT"), _), _, _, _) as e -> e
    | Sym (sym, es, len, tag) -> Sym (sym, map visit es, len, tag) 
    | Range (e, pos, len, tag) -> Range (visit e, pos, len, tag)
    | Concat (es, tag) -> Concat (map visit es, tag)
    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map visit fields, StrMap.map visit attrs, len, e_old)
    | e -> e


(**
  Applies a function to all nodes in an expression, in preorder:
  [visitExpPre f e = map (visitExpPre f) (children (f e))]
  
  Be careful: [f] should not be a function that strips layers off the expression. 
  This would result in skipping a layer. Use [visitExpPost] in that case.
  
  This function is useful for doing expanding substitutions.
*)
let rec visitExpPre : (exp -> exp) -> exp -> exp = fun f e ->
  
  let visit = visitExpPre f in

  match f e with
    | Sym (("final", _), [e], _, _) -> e
      (* Not visiting lengths: we want to operate on IML expressions *)
    | Sym (sym, es, len, tag) -> Sym (sym, map visit es, len, tag)       (* FIXME: not visiting length *)
    | Range (e, pos, len, tag) -> Range (visit e, visit pos, visit len, tag)
    | Concat (es, tag) -> Concat (map visit es, tag)
    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map visit fields, StrMap.map visit attrs, visit len, e_old)
    | e -> e

(**
    Same as [visitExpPre], but only applies to lengths.
*)
let rec visitExpLenPre : (len -> len) -> exp -> exp = fun f e -> 
  
  let rec visitLen : len -> len = fun l -> visitExpLenPre f (f l) in
  
  (* debug ("visitExpLenPre: e = " ^ dump e); *)
  
  match e with
    | Sym (sym, es, len, tag) -> Sym (sym, map (visitExpLenPre f) es, visitLen len, tag)
    | Range (e, pos, len, tag) -> Range (visitExpLenPre f e, visitLen pos, visitLen len, tag)
    | Concat (es, tag) -> Concat (map (visitExpLenPre f) es, tag)
    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map (visitExpLenPre f) fields, 
                                                    StrMap.map (visitExpLenPre f) attrs, visitLen len, e_old)
    | e -> e
  
(**
    Same as [visitExpPre], but only applies in arithmetic context.
    Top context is not arithmetic.
*)
let visitArithPre : (exp -> exp) -> exp -> exp = fun f e -> 

  let rec visit: bool -> exp -> exp = fun isArithChild e ->
      
	  (* debug ("visitArithPre: e = " ^ dump e); *)

    let isArithOp = match e with
        (* FIXME: including IfEq here is quite questionable *)
	    | Sym ((s, _), _, _, _) 
	      when List.mem s ["!"; "&&"; "LOR"; "=="; "!="; ">"; "<"; "<="; ">="; "-"; "+"; "*"; "If"; "IfEq"; "castToInt"] -> true
      | _ -> false 
    in

    let e = if isArithChild || isArithOp then f e else e in
	  match e with
	    | Sym (sym, es, len, tag) -> Sym (sym, map (visit isArithOp) es, (visit true) len, tag)
	    | Range (e, pos, len, tag) -> Range ((visit false) e, (visit true) pos, (visit true) len, tag)
	    | Concat (es, tag) -> Concat (map (visit false) es, tag)
	    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map (visit false) fields, 
	                                                    StrMap.map (visit false) attrs, (visit true) len, e_old)
	    | e -> e

  in visit false e
      
(**
  Applies a function to all nodes in an expression, in postorder:
  [visitExpPost f e = f (map (visitExpPost f) (children e))]
  
  Does not apply to lengths
  
  This function is useful for doing simplifying substitutions.
*)
let rec visitExpBodyPost : (exp -> exp) -> exp -> exp = fun f e ->

  (* debug ("visitExpBodyPost, e: " ^ dump e); *)

  let visit = visitExpBodyPost f in
  
  f
  (match e with
    | Sym ((("var" | "const" | "new" | "newT"), _), _, _, _) as e -> e
    | Sym (sym, es, len, tag) -> Sym (sym, map visit es, len, tag)
    | Range (e, pos, len, tag) -> Range (visit e, pos, len, tag)
    | Concat (es, tag) -> Concat (map visit es, tag)
    | e -> e)
  
  
(**
  Applies a function to all nodes in an expression, in postorder:
  [visitExpPost f e = f (map (visitExpPost f) (children e))]
  
  This function is useful for doing simplifying substitutions.
*)
let rec visitExpPost : (exp -> exp) -> exp -> exp = fun f e ->

  (* debug ("visitExpPost, e: " ^ dump e); *)

  let visit = visitExpPost f in
  
  f
  (match e with
      (* NB: not visiting lengths, see visitExpPre *)
    | Sym (sym, es, len, tag) -> Sym (sym, map visit es, len, tag)
    | Range (e, pos, len, tag) -> Range (visit e, visit pos, visit len, tag)
    | Concat (es, tag) -> Concat (map visit es, tag)
    | e -> e)

(**
  Applies a function to all nodes in an expression, in preorder:
  [visitAllSubexp f e = f e; (map (visitAllSubexp f) (children e))]
  
  This function is useful for doing checks on expressions.
*)
let rec visitAllSubexp : (exp -> unit) -> exp -> unit = fun f e ->

  let visit = visitAllSubexp f in

  f e;
  match e with
    | Sym (sym, es, len, tag) -> iter visit es; visit len;
    | Range (e, pos, len, tag) -> visit e; visit pos; visit len;
    | Concat (es, tag) -> iter visit es
    | e -> ()

let rec visitAllBodySubexp : (exp -> unit) -> exp -> unit = fun f e ->

  let visit = visitAllBodySubexp f in

  f e;
  match e with
    | Sym (sym, es, len, tag) -> iter visit es; 
    | Range (e, pos, len, tag) -> visit e; 
    | Concat (es, tag) -> iter visit es
    | e -> ()


(*************************************************)
(** {1 Tags and Identities} *)
(*************************************************)

let tag2id : id IntMap.t ref = ref IntMap.empty
let exp2id : id ExpMap.t ref = ref ExpMap.empty

let tagRequests = ref 0
let tagMisses = ref 0
let noTags = ref 0
let noTagIds = ref 0
let tagIdFound = ref 0
let assignedIds = ref 0
let assignedTags = ref 0
let expIdCalls = ref 0

let getTag : exp -> tag = fun e -> 
  tagRequests := !tagRequests + 1;
  match e with
    | Sym (sym, es, len, tag) -> tag
    | Range (e, offset, len, tag) -> tag
    | Concat (es, tag) -> tag
    | _ ->
      tagMisses := !tagMisses + 1;
      NoTag

let setTag : tag -> exp -> exp = fun tag -> function
    | Sym (sym, es, len, _) -> Sym (sym, es, len, tag)
    | Range (e, offset, len, _) -> Range (e, offset, len, tag)
    | Concat (es, _) -> Concat (es, tag)
    | e -> e

let tagNum : tag -> int = function
  | Det i    -> i
  | Nondet i -> i
  | NoTag    -> failwith "tagNum called with NoTag"

let removeDet: exp -> exp = function
	| Sym (sym, es, len, Det _) -> Sym (sym, es, len, NoTag)
	| Range (e, offset, len, Det _) -> Range (e, offset, len, NoTag)
	| Concat (es, Det _) -> Concat (es, NoTag)
	| e -> e

let rec simplifyStructure: exp -> exp = fun e ->
  let subst e =
    match getTag e with
      | NoTag -> e
      | tag -> 
        (* An option would be to only substitute if the id already exists, thus forbiding
           recursive idByStructure calls *)
        (* This optimisation gives 20% performance improvement *)
        (* This does affect naming *)
        Sym (("id", Prefix), [Int (Int64.of_int (expId e), Unknown)], Unknown, NoTag) 
  in
  
  removeDet (mapChildren (visitExpPost subst) e)
  (* removeDet e *)

and idByStructure: id option -> exp -> id = fun default e ->
  let e = simplifyStructure e in
  (* debug ("simplified expression for id: " ^ dump e); *)
  try ExpMap.find e !exp2id
	with Not_found -> 
	  let id = match default with 
	  | Some id -> id
	  | None -> assignedIds := !assignedIds + 1; freshId curExpId in
	  exp2id := ExpMap.add e id !exp2id;
	  id
  
and expId : exp -> id = fun e ->
  let id = match getTag e with
    | NoTag -> noTags := !noTags + 1; idByStructure None e
    | tag ->
      try 
        let id = IntMap.find (tagNum tag) !tag2id in
        tagIdFound := !tagIdFound + 1;

        (* 
          We update the structural mapping, so that both maps are always defined for 
          each expression. This doesn't guarantee consistency between tag- and structure-based
          ids. Right now we don't fail on an incosistency.

          Right now turned off, but this call is made in Solver_yices.
        *)
        
        (* if id <> idByStructure (Some id) e then (); *)
                (* fail ("getTag: id collision for e = " ^ dump e 
                ^ "\nUse registerTag() any time you transfer a tag to a new expression") *)
                
        (* debug ("the tag number " ^ string_of_int (tagNum tag) ^ " maps to id " ^  string_of_int id); *)
        id
      with Not_found ->
      begin
        noTagIds := !noTagIds + 1;
        let id = idByStructure None e in
        tag2id := IntMap.add (tagNum tag) id !tag2id;
        id
      end
  in
  expIdCalls := !expIdCalls + 1;
  (* debug ("calculating id for e = " ^ dump e);
  debug ("id = " ^ string_of_int id); *)
  id

  
(* let registerTag: exp -> exp = fun e -> ignore (expId e); e *)

let freshDet : unit -> tag = fun () -> assignedTags := !assignedTags + 1; Det (freshId curTagId)

let freshNondet : unit -> tag = fun () -> assignedTags := !assignedTags + 1; Nondet (freshId curTagId)

(* 
let printTagStats () =
  debug ("expId calls: " ^ string_of_int !expIdCalls);
  debug ("tag requests: " ^ string_of_int !tagRequests);
  debug ("tag misses: " ^ string_of_int !tagMisses);
  debug ("absent tags: " ^ string_of_int !noTags);
  debug ("present ids for tags: " ^ string_of_int !tagIdFound);  
  debug ("absent ids for tags: " ^ string_of_int !noTagIds);
  debug ("assigned ids: " ^ string_of_int !assignedIds);
  debug ("assigned tags: " ^ string_of_int !assignedTags)

  let _ = failFuns := !failFuns @ [printTagStats]
*)


(*************************************************)
(** {1 Hints} *)
(*************************************************)

let getHint : exp -> string = fun e ->
  let id = expId e in
  try IntMap.find id !hints
  with Not_found -> ""

let addHint : exp -> string -> unit = fun e hint ->
  let id = expId e in
  let old_hint = getHint e in
  if old_hint = "" then
    hints := IntMap.add id hint !hints

(*************************************************)
(** {1 Misc} *)
(*************************************************)

(**
   Structural equality up to deterministic tags.
*)
let structEq : exp -> exp -> bool = fun e1 e2 -> simplifyStructure e1 = simplifyStructure e2


let concat : exp list -> exp = fun es -> Concat (es, freshDet ())

let range : exp -> len -> len -> exp = fun e f l -> Range (e, f, l, freshDet ())

let mkInt : int -> exp = fun i -> Int (Int64.of_int i, Unknown)
let intVal: exp -> int = function
  | Int (i, _) -> Int64.to_int i
  | e -> failwith ("not an int: " ^ dump e)

let undef : len -> exp = fun l -> Sym (("undef", Prefix), [], l, freshNondet ())

(* 
  These are mostly used in the solver, so tags are not necessary.
  minexplib is 10% faster when not using tags here.
*)
let eq: exp list -> exp = fun es -> Sym (("==", Infix), es, Unknown, NoTag)
let neg : exp -> exp = fun e -> Sym (("!", Prefix), [e], Unknown, NoTag)
let gr : exp -> exp -> exp = fun a b -> Sym ((">", Infix), [a; b], Unknown, NoTag)
let grEq : exp -> exp -> exp = fun a b -> Sym ((">=", Infix), [a; b], Unknown, NoTag)


(* FIXME: move mkVar here, by giving an interface to exp *)

let zero : exp = Int (0L, Unknown)
let one  : exp = Int (1L, Unknown)
let tt   : exp = eq [zero; zero]

let unknown () = undef Unknown

let rec isConcrete : exp -> bool = function
  | Int _ -> true
  | String _ -> true
  | Sym (("var", _), _, _, _) -> false
  | Sym (_, es, _, Det _) -> for_all isConcrete es
  | Sym _ -> false
  | Range (e, _, _, _) -> isConcrete e
  | Concat (es, _) -> for_all isConcrete es 
  | _ -> false (* as first approximation *)

let isLength : exp -> bool = function
  | Sym ((sym, _), _, _, _) when List.mem sym ["user_len"; "net_len"; "lenvar"; "len"] -> true
  | Sym (("bn_len", _), _, _, _) -> fail "isLength: bn_len is deprecated"
  | _ -> false

let isArithmetic : exp -> bool = function
  | Int _ -> true
  | Sym ((sym, _), _, _, _) when List.mem sym ["+"; "-"] -> true
  | Sym (("castToInt", _), _, _, _) -> true
  | _ -> false

let isComparison: exp -> bool = function
  | Sym ((sym, _), _, _, _) when List.mem sym [">"; "<"; ">="; "<="; "!="] -> true
  | _ -> false

let isLogical: exp -> bool = function
  | Sym ((sym, _), _, _, _) when List.mem sym ["!"; "&&"; "||"] -> true
  | _ -> false

let isInteger : exp -> bool = function
  | Int _ -> true
  | _     -> false

let isSpecialLen : exp -> exp -> bool = fun a b ->
  a = Unknown || b = Unknown || a = All || b = All

let isAuxiliaryIf : exp -> bool = function
  | Sym ((("IfEq"), _), [e1; e2], _, _) 
    when isConcrete e1 || isConcrete e2 || isLength e1 || isLength e2 || isArithmetic e1 || isArithmetic e2 -> true
  | Sym ((("If"), _), [e], _, _) -> isComparison e || isLogical e
  | _ -> false

let isNondet : exp -> bool = function
  | Sym (_, es, _, Nondet _) -> true
  | _ -> false 

let containsSym : string -> exp -> bool = fun s e ->
  
  let contains : exp -> exp = function
    | Sym ((s', _), _, _, _) when s' = s -> raise Exit
    | e -> e
  in
  
  try ignore (visitExpPost contains e); false with Exit -> true

let getSize: exp -> int = fun e ->
  let size = ref 0 in
  let count e = size := !size + 1 in
  visitAllBodySubexp count e;
  !size

let interesting : exp -> bool = function
  | Ptr (Stack "SAX_meter.i:method[4777]", _) -> true 
  (* | Ptr (Heap (17, _), _) -> true *)
  | _ -> false


