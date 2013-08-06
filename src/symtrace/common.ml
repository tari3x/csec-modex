(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(*************************************************)
(** {1 Lists} *)
(*************************************************)

module List2 = struct

  let concat_map f xs = List.concat (List.map f xs)
  
  let rec sum = function
    | x :: xs -> x + sum xs
    | [] -> 0
  
  let sum_with f xs = sum (List.map f xs) 
  
  let rec any = function
    | true :: _ -> true
    | false :: xs -> any xs
    | [] -> false 
  
  let filter_out : ('a -> bool) -> 'a list -> 'a list = fun p -> List.filter (fun a -> not (p a))
  
  let rec filter_map: ('a -> 'b option) -> 'a list -> 'b list = fun f -> function
    | [] -> []
    | x :: xs -> 
      match f x with
        | Some y -> y :: filter_map f xs
        | None -> filter_map f xs  
  
  let rec first_some: ('a -> 'b option) -> 'a list -> 'b option = fun f -> function
    | [] -> None
    | x :: xs -> 
      match f x with
        | Some y -> Some y
        | None -> first_some f xs
  
  let rec find_first f = function
    | x :: xs when f x -> Some x
    | x :: xs -> find_first f xs
    | [] -> None
  
  let remove : 'a -> 'a list -> 'a list = fun a -> filter_out (fun b -> a = b)
  
  let rec remove_first f = function
    | x :: xs when f x -> xs
    | x :: xs -> x :: remove_first f xs
    | [] -> []
  
  let find_and_remove f xs = 
    match find_first f xs with
      | Some x -> Some (x, remove_first f xs)
      | None -> None
  
  let rec replicate: int -> 'a -> 'a list = fun i a -> 
    if i = 0 then []
    else a :: replicate (i - 1) a
  
  let nub: 'a list -> 'a list = fun l -> 
    let rec nub' = fun ls ->
      function
        | (x::xs) when List.mem x ls -> nub' ls xs
        | (x::xs) -> x :: nub' (x::ls) xs
        | [] -> []
    in
    nub' [] l
  
  let rec set_element: int -> 'a -> 'a list -> 'a list = fun i x' -> function
    | x :: xs -> if i > 0 then x :: set_element (i - 1) x' xs else x' :: xs
    | [] -> failwith "replace: index out of bounds"
  
  let find_index : ('a -> bool) -> 'a list -> int option = fun p xs -> 
    let rec find i = function
      | [] -> None
      | x :: xs -> if p x then Some i else find (i + 1) xs
    in
    find 0 xs
  
  let find_index_exn : ('a -> bool) -> 'a list -> int = fun p xs -> 
    match find_index p xs with
      | Some i -> i
      | None -> failwith "find_index: not found"
  
  (** Remove the first occurence *)
  let rec del : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list = fun eq y -> function
    | []                  -> []
    | x :: xs when eq x y -> xs
    | x :: xs             -> x :: del eq y xs
  
  (** Set difference *)
  let rec diff : 'a list -> 'a list -> 'a list = fun xs -> function
    | []      -> xs
    | y :: ys -> diff (remove y xs) ys
  
  
  (** Multiset difference *)
  let rec multidiff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list = fun eq xs -> function
    | []      -> xs
    | y :: ys -> multidiff eq (del eq y xs) ys
  
  let rec last : 'a list -> 'a = function
    | [x]     -> x
    | x :: xs -> last xs
    | []      -> failwith "last: empty list"
  
  let rec distinct = function
    | x :: xs when List.mem x xs -> false
    | x :: xs -> distinct xs
    | [] -> true 
  
  (**
    The function gt specifies a directed graph on the elements:
    gt x x' if there is an edge x -> x'.
    
    Let x > x' be the partial ordering "x' is a descendant of x" (the transitive closure of the graph relation).
    In the following "greater" and "smaller" refer to >. 
  
    A list (x :: xs) is topologically sorted (in ascending order) if 
    - x is not greater than any of the xs
    - xs is topologically sorted.
  
    Will hang if there is a cycle.
  *)
  let rec topsort gt = function
    | [] -> []
      (*
        Let rank(x, xs) be the number of elements in xs that are smaller than x (the number of descendants of x in xs). 
        We shall prove that if the graph does not contain loops (no x is a descendant of itself) then
        topsort(x :: xs) is topologically sorted. The proof is by double induction on length(x :: xs) and rank(x, xs). 
        The induction also ensures termination.
      *)  
    | x :: xs ->
      (* Find all immediate children of x *)
      match List.partition (gt x) xs with
        (*
          If there are no children then x is not greater than any of the xs. 
          By induction (x :: sort xs) is topologically sorted. 
        *)
       | [], xs  -> x :: topsort gt xs
        (*
          The rank of any element x' of xs is strictly smaller than the rank of x, because
          all descendants of x' are also descendants of x, but x' is not a descendant of itself. 
          By induction sort(xs @ [x] @ xs') is topologically sorted.
        *)
       | xs, xs' -> topsort gt (xs @ [x] @ xs')
      
      
  let rec cross_product f xs ys = 
    match xs with
      | x :: xs -> List.map (f x) ys @ cross_product f xs ys
      | [] -> []
        
end

(* FIXME: remove *)
include List2

(*************************************************)
(** {1 Assoc} *)
(*************************************************)

let maybe_assoc: 'a -> ('a * 'b) list -> 'b option = fun x xs ->
  if List.mem_assoc x xs then Some (List.assoc x xs) else None

let rec inverse_mem_assoc: 'b -> ('a * 'b) list -> bool = fun b -> function
  | (_, b') :: _ when b = b' -> true
  | _ :: xs -> inverse_mem_assoc b xs
  | [] -> false

let rec inverse_assoc: 'b -> ('a * 'b) list -> 'a = fun b -> function
  | (a, b') :: _ when b = b' -> a
  | _ :: xs -> inverse_assoc b xs
  | [] -> raise Not_found

let assoc_keys: ('a * 'b) list -> 'a list = fun l -> let l1, l2 = List.split l in l1

(*************************************************)
(** {1 Strings} *)
(*************************************************)

let words : string -> string list = Str.split (Str.regexp "[ \t]+")

let trim : string -> string = function s -> 
  Str.replace_first (Str.regexp "^[ \t\n]+") "" (Str.replace_first (Str.regexp "[ \t\n]+$") "" s)

(*************************************************)
(** {1 Stacks} *)
(*************************************************)

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


(*************************************************)
(** {1 IO} *)
(*************************************************)

(*
  Because pp_expr in Yices uses stdout, we redirect all our standard output to a copy of stdout,
  and redirect stdout to stderr. 
*)
let out_channel = Unix.out_channel_of_descr (Unix.dup Unix.stdout)
;;
Unix.dup2 Unix.stderr Unix.stdout
;;
let print_string s = output_string out_channel s
let print_endline s = output_string out_channel (s ^ "\n")

(* FIXME: try ... with in recursive function bad, will exceed stack for very long files *)
let rec readFile : in_channel -> string list = fun file ->
  try
    let line = input_line file in
    line :: readFile file
  with End_of_file -> []

let prerr_title s =
  prerr_endline ("\n" ^ s);
  prerr_endline (String.make (String.length s) '=');
  prerr_endline ""
  
(*************************************************)
(** {1 Debug} *)
(*************************************************)

(** Routines to be called on failure *)
let failFuns : (unit -> string) list ref = ref []

(**
  Debug is enabled when debug_view >= debug_depth.
*)
let debug_depth = ref 1
let debug_view = ref 0
let indent = ref 0

let increase_indent ?(by = 1) () = 
  indent := !indent + by * 2
  (* 
  if (!indent = 20) then
  begin
    debug "INDENT -20";
    indent := 0;
  end
  *)

let decrease_indent ?(by = 1) () = 
  indent := !indent - by * 2
  (*
    if (!indent = 0) then
    begin
      indent := 20;
      debug "INDENT +20";
    end
    else indent := !indent - 2
  *)  


(** 
    If this is on, the debug lines in the trace will have "(mark)" in front.
    This can be used to extract an interesting portion of the trace with grep.
 *)
let markEnabled = ref false

let warning_location = ref ""

let debugEnabled () = !debug_view >= !debug_depth

let increase_debug_view ?(by = 1) () = 
  debug_view := !debug_view + by

let decrease_debug_view ?(by = 1) () = 
  debug_view := !debug_view - by

let increase_debug_depth ?(by = 1) () = 
  debug_depth := !debug_depth + by;
  increase_indent ~by ()

let decrease_debug_depth ?(by = 1) () = 
  debug_depth := !debug_depth - by;
  decrease_indent ~by ()
  
  
(**
  Locally increase debug view.
*)
let with_debug ?(depth = 1) f x = 
  increase_debug_view ~by:depth ();
  let result = f x in
  decrease_debug_view ~by:depth ();
  result  

(**
  Locally decrease debug level.
*)
let silent ?(depth = 1) f x = with_debug ~depth:(- depth) f x

let decorateDebug s = (if !markEnabled then "(mark)" else "") ^ (String.make (max 0 !indent) ' ') ^ s

(**
  Allows to locally increase debug depth.
*)
let debug ?(raise_by = 0) a = 

  let debug s = 
    debug_depth := !debug_depth - raise_by;
    if debugEnabled () then prerr_endline (decorateDebug s);
    debug_depth := !debug_depth - raise_by
  in

  Printf.ksprintf debug a

let warn a =
  let warn s =
    if !warning_location <> "" then 
      prerr_endline (decorateDebug ("WARNING: " ^ s ^ " (" ^ !warning_location ^ ")"))
    else
      prerr_endline (decorateDebug ("WARNING: " ^ s))
  in 
  Printf.ksprintf warn a
  
;;
Printexc.record_backtrace true;
;;

let fail a = 
  let fail s = 
    let s_extra = List.map (fun f -> f ()) !failFuns in
    let s_extra = String.concat "\n" s_extra in
    failwith ("failure: " ^ s ^ "\n" ^ s_extra)
  in
  Printf.ksprintf fail a
  

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

(*************************************************)
(** {1 Maps} *)
(*************************************************)

module type CustomKey = sig
  include Map.OrderedType
  
  val toString: t -> string
end

module type CustomMap = sig
  include Map.S
  
  val ofList: (key * 'a) list -> 'a t 
      
  val find: key -> 'a t -> 'a
  
  val maybe_find: key -> 'a t -> 'a option
  
  val disjointUnion: 'a t list -> 'a t
  
  val keys: 'a t -> key list
  val values: 'a t -> 'a list
end

module CustomMap (M: CustomKey): (CustomMap with type key = M.t) = struct
  include Map.Make(M)
  
  let ofList (bindings: (key * 'a) list): 'a t = 
    List.fold_left (fun m (k, a) -> add k a m) empty bindings 
    
  let find k m = 
    try find k m 
    with Not_found ->
      (* This isn't always an error, so using debug which can be silenced. *) 
      debug "key not found: %s" (M.toString k);
      raise Not_found
  
  let maybe_find k m = 
    if mem k m then Some (find k m) else None
              
  let disjointUnion ms =
    let f k a b =
      match a, b with
        | Some a, None -> Some a
        | None, Some b -> Some b
        | _ -> fail "Map.disjointUnion: maps are not disjoint, both contain %s" (M.toString k)
    in
    List.fold_left (merge f) empty ms
            
  let keys m = 
    let (keys, _) = List.split (bindings m) in
    keys
    
  let values m = 
    let (_, values) = List.split (bindings m) in
    values    
end


(*************************************************)
(** {1 Misc} *)
(*************************************************)

let non f x = not (f x)

let comp f g x = f (g x)

let (|>) x f = f x

let const x y = x

(** The range function *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

let never_returns a = ()

let fold2list : (('k -> 'a -> 'b -> 'b) -> 'm -> 'b -> 'b) -> ('k -> 'a -> 'c) -> 'm -> 'c list = fun foldF f m ->
  List.rev (foldF (fun k a cs -> (f k a) :: cs) m [])

let increment : int ref -> int = fun id ->
  id := !id + 1;
  if !id = 0 then fail "freshId: overflow"; 
  !id

let option_to_string to_string = function
  | Some a -> "Some " ^ to_string a
  | None -> "None"
    
