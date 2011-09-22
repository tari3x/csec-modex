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

(** Routines to be called on failure *)
let failFuns : (unit -> unit) list ref = ref []

(** The ids used for tags, expression ids and stack pointers. *)
let curId : int ref = ref 0

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

let comp f g x = f (g x)

(** The range function *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

let filter_out : ('a -> bool) -> 'a list -> 'a list = fun p -> filter (fun a -> not (p a))

let remove : 'a -> 'a list -> 'a list = fun a -> filter_out (fun b -> a = b)


let findIndex : ('a -> bool) -> 'a list -> int = fun p xs -> 
  let rec find i = function
    | [] -> raise Not_found
    | x :: xs -> if p x then i else find (i + 1) xs
  in
  find 0 xs

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
  failwith s

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let freshId : unit -> int = fun () ->
  curId := !curId + 1;
  if !curId = 0 then fail "freshId: overflow"; 
  !curId

(*************************************************)
(** {1 Dump} *)
(*************************************************)

let clipEnabled = ref true

let rec dumpLen = fun e -> dumpFull e

and dumpOffsetVal : offsetVal -> string = function
  | Field s -> "field " ^ s
  | Attr  s -> "attr " ^ s
  | Index i -> "index " ^ (string_of_int i)
  | Flat e  -> dumpFull e

and dumpOffset : offset -> string = function (ot, l) ->
  (dumpOffsetVal ot) ^ "(" ^ dumpLen l ^ ")"

and dumpBase : base -> string = function
  | Stack name    -> "stack " ^ name (* ^ "[" ^ string_of_int id ^ "]" *)
  | Heap (id, _)  -> "heap " ^ string_of_int id

and dumpFull : exp -> string = function
  | Int (ival, len) -> "i" ^ Int64.to_string ival ^ "<" ^ dumpLen len ^ ">"
  | String s -> s
  | Sym ((s, Prefix), es, len, id) -> 
      let idPart = match id with 
        | (Det _ | NoTag) -> "" 
        | Nondet i        -> "[" ^ string_of_int i ^ "]" 
      in
      s ^ idPart ^ "(" ^ String.concat ", " (map dumpFull es) ^ ")" ^ "<" ^ dumpLen len ^ ">"
        (* ^ "[" ^ string_of_int len ^ "," ^ string_of_int id ^ "]" *)
  | Sym ((s, Infix), es, len, tag) ->
      let len_dump = if s = "castToInt" then "<" ^ dumpLen len ^ ">" else "" in
      "(" ^ String.concat (" " ^ s ^ " ") (map dumpFull es) ^ ")" ^ len_dump
      (* ^ "[" ^ string_of_int len ^ "," ^ string_of_int id ^ "]" *)
  | Range (e, f, l, _) -> "(" ^ dumpFull e ^ ")" ^ "{" ^ dumpLen f ^ "," ^ dumpLen l ^ "}"
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
(** {1 Traversal} *)
(*************************************************)

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
  
  let e' = match e with
    | Sym (sym, es, len, tag) -> Sym (sym, map (visitExpLenPre f) es, visitLen len, tag)
    | Range (e, pos, len, tag) -> Range (visitExpLenPre f e, visitLen pos, visitLen len, tag)
    | Concat (es, tag) -> Concat (map (visitExpLenPre f) es, tag)
    | Struct (fields, attrs, len, e_old) -> Struct (StrMap.map (visitExpLenPre f) fields, 
                                                    StrMap.map (visitExpLenPre f) attrs, visitLen len, e_old)
    | e -> e
  in
  (* I think this is the responsibility of the caller: *)
    (*let m = getMeta e in
    let m' = getMeta e' in
    m'.hint <- m.hint;*)
    e'
  
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
    | Sym (sym, es, len, tag) -> Sym (sym, map visit es, visit len, tag)
    | Range (e, pos, len, tag) -> Range (visit e, visit pos, visit len, tag)
    | Concat (es, tag) -> Concat (map visit es, tag)
    | e -> e)


(*************************************************)
(** {1 Tags and Identities} *)
(*************************************************)

let tag2id : id IntMap.t ref = ref IntMap.empty
let exp2id : id ExpMap.t ref = ref ExpMap.empty

let getTag : exp -> tag = function
    | Sym (sym, es, len, tag) -> tag
    | Range (e, offset, len, tag) -> tag
    | Concat (es, tag) -> tag
    | _ -> NoTag

let tagNum : tag -> int = function
  | Det i    -> i
  | Nondet i -> i
  | NoTag    -> failwith "tagNum called with NoTag"

let removeDet : exp -> exp = 
  
  let remove : exp -> exp = function
    | Sym (sym, es, len, Det _) -> Sym (sym, es, len, Det 0)
    | Range (e, offset, len, Det _) -> Range (e, offset, len, Det 0)
    | Concat (es, Det _) -> Concat (es, Det 0)
    | e -> e
  in
  
  visitExpPost remove

(**
   Structural equality up to deterministic tags.
*)
let structEq : exp -> exp -> bool = fun e1 e2 -> removeDet e1 = removeDet e2

let expId : exp -> id = fun e ->
  
  let idByStructure : exp -> id = fun e ->
    let e' = removeDet e in
	  try ExpMap.find e' !exp2id
	  with Not_found -> 
	    let id = freshId () in
	    exp2id := ExpMap.add e' id !exp2id;
	    id
  in
  
  match getTag e with
    | NoTag -> idByStructure e
    | tag ->
      try IntMap.find (tagNum tag) !tag2id
      with Not_found ->
        let id = idByStructure e in
        tag2id := IntMap.add (tagNum tag) id !tag2id;
        id
  
let freshDet : unit -> tag = fun () -> Det (freshId ())

let freshNondet : unit -> tag = fun () -> Nondet (freshId ())

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

let concat : exp list -> exp = fun es -> Concat (es, freshDet ())

let range : exp -> len -> len -> exp = fun e f l -> Range (e, f, l, freshDet ())

let mkInt : int -> exp = fun i -> Int (Int64.of_int i, Unknown)

let mkVar : string -> exp -> exp = fun s e ->
  match getTag e with
    | NoTag -> Sym (("var", Prefix), [String s], Unknown, freshDet ())
    | tag   -> Sym (("var", Prefix), [String s], Unknown, tag)

let mkLet : exp -> exp = fun e -> Sym (("let", Prefix), [e], Unknown, freshDet ())

let undef : len -> exp = fun l -> Sym (("undef", Prefix), [], l, freshNondet ())

let zero : exp = Int (0L, Unknown)
let one  : exp = Int (1L, Unknown)

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

let isInteger : exp -> bool = function
  | Int _ -> true
  | _     -> false

let isSpecialLen : exp -> exp -> bool = fun a b ->
  a = Unknown || b = Unknown || a = All || b = All

let isAuxiliaryIf : exp -> bool = function
  | Sym ((("IfEq"), _), [e1; e2], _, _) when isConcrete e1 || isConcrete e2 || isLength e1 || isLength e2 -> true
  | _ -> false


let eq: exp list -> exp = fun es -> Sym (("==", Infix), es, Unknown, freshDet ())

let neg : exp -> exp = fun e -> Sym (("!", Prefix), [e], Unknown, freshDet ())

let gr : exp -> exp -> exp = fun a b -> Sym ((">", Infix), [a; b], Unknown, freshDet ())

let grEq : exp -> exp -> exp = fun a b -> Sym ((">=", Infix), [a; b], Unknown, freshDet ())

let interesting : exp -> bool = function
  | Ptr (Stack "SAX_meter.i:r_size[4705]", _) -> true 
  (* | Ptr (Heap (17, _), _) -> true *)
  | _ -> false


