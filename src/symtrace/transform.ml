 
open List

open Types
open Utils
open Exp
open Imltypes
open Solver

(*************************************************)
(** {1 Types} *)
(*************************************************)

(** Pi function name *)
type piFun = string

(** Pi function definition, either expressed directly (as IML) or in terms of other functions *) 
type piFunDef = Basic of exp | Rewrite of exp

(**
  Pi functions with their definitions.
*)
type piFunInfo = piFun * piFunDef

(**
  [(parser, concat, result)]
*)
type parsingRule = (piFun * piFun) * exp


(*************************************************)
(** {1 State} *)
(*************************************************)

(*
  Right now these are global, but eventually you might want to make them
  per process pair.
*)
let concats: piFunInfo list ref = ref []
let parsers: piFunInfo list ref = ref []

(**
  Function pairs with disjoint value ranges.
*)
let disjointPairs: (piFun * piFun) list ref = ref []

let parsingRules : parsingRule list ref = ref []

let arities : (piFun * int) list ref = ref []

(**
  Safe parsers check that the argument comes from the range of the concat.
  
  The list contains the parsers together with their matched concats and the argument number.
*)
let safeParsers : (piFun * (piFun * int)) list ref = ref []

let concatId : int ref = ref 0
let parserId : int ref = ref 0

let verbose : bool ref = ref false

(*************************************************)
(** {1 Debug Output} *)
(*************************************************)

let showFun : piFunInfo -> string = function 
  | (name, Basic def) -> name ^ "/" ^ string_of_int (assoc name !arities) ^ " := " ^ (showIExp def)
  | (name, Rewrite e) -> name ^ "/" ^ string_of_int (assoc name !arities) ^ " ~> " ^ (showIExp e)

let showFuns : piFunInfo list -> unit = fun cs ->
  prerr_endline "";
  iter (fun c -> prerr_endline (showFun c)) cs;
  prerr_endline ""

(*************************************************)
(** {1 Formal Arguments} *)
(*************************************************)

(**
  Argument must start from 0, because we use it for addressing the actuals array.
  
  Must be deterministic because same arguments should match. Also we use structural identity
*)
(* TODO: remove len parameter *)
let mkArg: len -> int -> exp = fun len id ->
  Sym (("arg", Prefix), [mkInt id], len, NoTag)
  
let isArg : exp -> bool = function
  | Sym (("arg", _), _, _, _) -> true
  | _ -> false

let argId: exp -> int = function
  | Sym (("arg", _), i :: _, _, _) -> intVal i
  | e -> fail ("argId: not an arg: " ^ dump e) 

(** 
  [len(id) = len(arg(id))]
*)
let mkLen len id = 
  let l = Sym (("lenarg", Prefix), [mkInt id], len, NoTag) in
  addFact (grEq l zero);
  l

let isArgLen : exp -> bool = function
  | Sym (("lenarg", _), _, _, _) -> true
  | _ -> false

let lenArgId: len -> int = function
  | Sym (("lenarg", _), i :: _, _, _) -> intVal i
  | e -> fail ("lenArgId: not a lenarg: " ^ dump e) 

let mkFormalArgs: int -> exp list = fun n ->
  map (fun i -> mkArg (mkLen Unknown i) i) (0 -- (n - 1))

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let newConcatName : unit -> string = fun () ->
  concatId := !concatId + 1;
  "conc" ^ string_of_int !concatId  

let newParserName : unit -> string = fun () ->
  parserId := !parserId + 1;
  "parse" ^ string_of_int !parserId  

let isParser : string -> bool = fun s -> mem_assoc s !parsers 
  (* List.exists (function ((s', _), _) when s = s' -> true | _ -> false) !parsingRules *) 
   
let isConcat: string -> bool = fun s -> mem_assoc s !concats

let isFormatFun: string -> bool = fun s -> isParser s || isConcat s

let parserName : parsingRule -> string = function ((name, _), _) -> name


(**
  [substMany [a1, ..., an] [b1, ..., bn] e = e[b1/a1, ..., bn/an]]. 

  Applies the substitutions in pararallel.
*)
let substMany: exp list -> exp list -> exp -> exp = 
  
  let mkFinal e = Sym (("final", Prefix), [e], Unknown, NoTag) in
  
  let rec substOne = fun es1 es2 e -> match (es1, es2) with
      (* Using equalLen because this is used to substitute both lengths and normal subexpressions *)
    | e1 :: es1', e2 :: es2' -> substOne es1' es2' (if equalLen e1 e then mkFinal e2 else e)
    | [], [] -> e
    | _ -> fail "substMany: bad argument"
  in
  
  fun es1 es2 -> visitExpPre (substOne es1 es2)


let subst : exp -> exp -> exp -> exp = fun a b e -> substMany [a] [b] e


(* Replace application of format functions by their definitions *)
let expandFormatFuns: exp -> exp = 

  let lookupDef: piFun -> exp = fun name ->
	  let def = 
      try if isParser name then assoc name !parsers else assoc name !concats
      with Not_found -> fail "expandFormatFuns: impossible happened" 
    in
	  match def with
	    | Basic e    -> e 
	    | Rewrite _ -> fail "lookup def: not a basic definition" 
	  in
      
  let expand: exp -> exp = function 
    | Sym ((f, _), es, _, tag) when isFormatFun f ->
      let e_def = lookupDef f in
      let args = mkFormalArgs (length es) in
      setTag tag (substMany args es e_def)
    | e -> e

  in visitExpPre expand

(*************************************************)
(** {1 Constant extraction} *)
(*************************************************)

let constants: string list ref = ref []
let constDefs: (string * exp) list ref = ref []
  
let mkConst: string -> exp -> exp = fun c e ->
  if not (List.mem c !constants) then
  begin 
    constants := !constants @ [c];
    constDefs := (c, e) :: !constDefs;
  end;
  Sym (("const", Prefix), [String c], Unknown, NoTag)

let extractConstConcats : exp list -> exp list = 
  
  let mkConst : exp -> exp = function
    | Sym ((c, _), [], _, _) when isConcat c ->
      begin match assoc c !concats with
        | Basic e -> mkConst ("const_" ^ c) e  
        | Rewrite e -> fail "extractConstConcats: impossible happened"
      end
    | e -> e
  in
  
  List.map (visitExpBodyPre mkConst)
  
let extractConstants : exp list -> exp list = 
  
	let mkConst : exp -> exp = fun e -> match e with
    | Int (ival, len) -> mkConst ("integer_" ^ Int64.to_string ival) e
    | String s -> mkConst ("string_" ^ s) e
    | e -> e
  in
  
  List.map (visitExpBodyPre mkConst)


(*************************************************)
(** {1 Concatenation Tags} *)
(*************************************************)

let mkTag : exp -> exp = fun e ->
  Sym (("tag", Prefix), [e], getRealLen e, NoTag)

let replaceTags : exp -> exp = fun e -> match e with
    | (Int _ | String _) -> mkTag e
    | e -> e

let replaceTagsInConcats : unit -> unit = fun () ->

  let replace = function
    | (name, Basic (Concat (es, tag))) -> (name, Basic (Concat (map replaceTags es, tag))) 
    | x -> x 
  in
  
  concats := List.map replace !concats


(*************************************************)
(** {1 Concatenations} *)
(*************************************************)

(**
  All args are identified in their expression order. All lenargs have the same id as the corresponding arg. 
*)

let extractConcats : exp list -> exp list * piFunInfo list = fun events ->
  
  let concats : piFunInfo list ref = ref [] in
  
  let nextArgId = ref 0 in 
  let takenLens: int list ref = ref [] in
  
  let argLens : len list ref = ref [] in
  
  (* 
    A length field is equal to the length of a field which is neither a tag nor a length field
  *)
  let isConcreteArgLen : exp -> bool = fun e -> 
    List.exists (fun l -> equalLen e l) !argLens && not (List.exists (fun l -> equalLen e (getLen l)) !argLens) 
  in 
  
  let isNotTag: exp -> bool = fun e -> not (isConcrete e || isArithmetic e) in
  
  let isConcreteArg: exp -> bool = fun e -> isNotTag e && not (isConcreteArgLen e) in

  let wrapArg: exp -> exp = fun e ->
    Sym (("arg", Prefix), [mkInt (freshId nextArgId - 1); e], getRealLen e, NoTag)
  in

  let rec collectArgs: exp list -> exp list = function
    | e :: es when isConcreteArg e -> 
      let e' = wrapArg e in 
      e' :: collectArgs es
    | e :: es -> e :: collectArgs es
    | [] -> []
  in

  let rec collectArgLens: exp list -> exp list = function
    | e :: es when isConcreteArgLen e -> 
      let eArg = find (fun e' -> equalLen e (getLen e') && not (mem (argId e') !takenLens)) es in
      let id = argId eArg in
      takenLens := id :: !takenLens;
      mkLen (getRealLen e) id :: collectArgLens es
    | Sym (("arg", Prefix), [i; e], l, NoTag) :: es ->
      Sym (("arg", Prefix), [i; e], mkLen Unknown (intVal i), NoTag) :: collectArgLens es
    | e :: es -> e :: collectArgLens es
    | [] -> []
  in

  let rec extractConcreteArgs: exp list -> exp list = function
    | Sym (("arg", _), [_; e], _, _) :: es -> e :: extractConcreteArgs es
    | e :: es -> extractConcreteArgs es
    | [] -> []
  in
  
  let rec removeConcreteArgs: exp list -> exp list = function
    | Sym (("arg", Prefix), [id; e], l, tag) :: es -> Sym (("arg", Prefix), [id], l, tag) :: removeConcreteArgs es
    | e :: es -> e :: removeConcreteArgs es
    | [] -> []
  in
  
  let extract : exp -> exp = function
    | Concat (es, tag) ->
      debug ("extract, e = " ^ dump (Concat (es, tag)));
      nextArgId := 0;
      takenLens := [];
      argLens := map getRealLen (filter isNotTag es);
      let es' = collectArgLens (collectArgs es) in
      let args = extractConcreteArgs es' in
      let def = removeConcreteArgs es' in
      let name = newConcatName () in
      concats := !concats @ [(name, Basic (concat def))];
      arities := !arities @ [(name, List.length args)];
      debug ("extract, e_new = " ^ dump (concat def));
      Sym ((name, Prefix), args, Unknown, tag)
    | e -> e
  in
  
  let events' = map (visitExpPre extract) events in
  (events', !concats)


let isInjectiveConcat: bool -> piFunInfo -> bool = fun useTypeInfo c ->
  
  let argsWithoutLen = ref 0 in
  let increment () = argsWithoutLen := !argsWithoutLen + 1; !argsWithoutLen in
  
  let isFixed: imltype -> bool = function
	  | Fixed _ -> true
	  | _ -> false
  in

	let rec check: imltype list -> exp list -> exp list -> bool = fun ts lens -> function
	  | e :: es when isArgLen e -> check ts (e :: lens) es
	  | e :: es when isArg e ->
      let typeFact = if useTypeInfo then not (isFixed (nth ts (argId e))) else true in
      if typeFact && not (List.exists (fun l -> equalLen l (getRealLen e)) lens) then
      begin
        (* debug ("no length found for " ^ dump e);
        debug ("lens: " ^ dumpList lens); *)
        if increment () > 1 then false
        else check ts lens es
      end
	    else check ts lens es
    | e :: es -> check ts lens es
	  | [] -> true
   
	in match c with 
  | (name, Basic (Concat (es, _))) ->
    if useTypeInfo then
	    let (ts, _) = 
	      try assoc name !funTypes
	      with Not_found -> fail ("isInjectiveConcat: concat " ^ name ^ " has no type") in
	    check ts [] es
    else check [] [] es
  | _ -> true


(** Thrown by [unify] *)
exception Disjoint
exception NoUnify of string

(**
  [needDisjoint] - should the concats be split into simpler concats when possible to achieve disjointness?  
  If [needDisjoint] is true, all the resulting concats are disjoint.
  If [needDisjoint] is false, some of the concats may not be disjoint, refer to {! Transform.disjointPairs}.
*)
let rec insertConcats : ?needDisjoint: bool -> piFunInfo list -> unit = fun ?(needDisjoint = true) cs ->

  let newConcats : piFunInfo list ref = ref [] in 
  
  let nextArgId = ref 0 in
  let newArg : unit -> exp = fun () ->
    let id = freshId nextArgId - 1 in
    mkArg (mkLen Unknown id) id 
  in
  let resetArg () = nextArgId := 0 in
  
  (* substitutions unifying the first and the second expression *)
  let args1: exp list ref = ref [] in
  let args2: exp list ref = ref [] in
  
  (*
    Sets args1 and args2.
    Returns a list where all arguments are unified and the rest of the fields are taken from the first concat.
  *)
  let rec unifyArgs: exp list * exp list -> exp list = function
    | ([arg1], es2) when isArg arg1 ->
      (* FIXME: what if es2 is empty? *)
      let arg = newArg () in
      args1 := !args1 @ [arg1];
      args2 := !args2 @ (match es2 with [e] -> [e] | es2 -> [concat es2]);
      [arg] 

    | (es1, [arg2]) when isArg arg2 ->
      let arg = newArg () in
      args1 := !args1 @ (match es1 with [e] -> [e] | es1 -> [concat es1]);
      args2 := !args2 @ [arg2];
      [arg]

    | (arg1 :: es1, arg2 :: es2) when isArg arg1 || isArg arg2 ->
      let arg = newArg () in
      args1 := !args1 @ [arg1]; args2 := !args2 @ [arg2];
      arg :: unifyArgs (es1, es2)
      
    | e1 :: es1, e2 :: es2 -> e1 :: unifyArgs (es1, es2)
      
    | [], [] -> []
     
    | _ -> raise (NoUnify "unifyArgs: cannot unify")
  in

  (* The first list is assumed to contain new arguments *)
  let rec unifyRest: exp list * exp list -> exp list = function
    | [arg1], es2 when isArg arg1 -> [arg1]
    
    | (arg1 :: es1, arg2 :: es2) when isArg arg1 -> arg1 :: unifyRest (es1, es2)
    
    | (len1 :: es1, len2 :: es2) when isArgLen len1 || isArgLen len2 ->
      
      (*
      debug ("unifying lengths " ^ dump len1 ^ " and " ^ dump len2);
      debug ("args1 = " ^ dumpList !args1);
      debug ("args2 = " ^ dumpList !args2);
      *)
      
      if not (equalLen (getLen len1) (getLen len2)) then
        raise (NoUnify "length fields not aligned");

      (* can try proving disjointness now *)
      let es = unifyRest (es1, es2) in 

	    let argNum =
        try
	        if isArgLen len1 then findIndex (fun e -> equalLen len1 (getLen e)) !args1 
	        else findIndex (fun e -> equalLen len2 (getLen e)) !args2
        with Not_found ->
          raise (NoUnify "orphan length field");
      in
      
      let arg1 = nth !args1 argNum in
      let arg2 = nth !args2 argNum in
      if not (equalLen len1 (getLen arg1)) || not (equalLen len2 (getLen arg2)) then
         raise (NoUnify "length fields correspond to different arguments");
      let len = mkLen (getRealLen len1) argNum in
      len :: es

    | (Int (i1, len1) :: es1, Int (i2, len2) :: es2) ->
      if not (equalLen len1 len2) then
        raise (NoUnify "integer fields of different lengths");
      if i1 <> i2 then
        raise Disjoint
      else 
        Int (i1, len1) :: unifyRest (es1, es2)
        
    | (String s1 :: es1, String s2 :: es2) ->
      let len1 = String.length s1 in
      let len2 = String.length s2 in
      let minLen = min len1 len2 in
      let s1' = String.sub s1 0 minLen in
      let s2' = String.sub s2 0 minLen in
      if s1' <> s2' then
        raise Disjoint
      else if len1 <> len2 then
        raise (NoUnify "strings have different length but are the same over common prefix")
      else
        String s1 :: unifyRest (es1, es2)

    | [], [] -> []

    | _ -> raise (NoUnify "unifyRest: cannot unify")
  in

  (*
    Result: (unified expression, substitutions unifying the first expression, substitutions unifying the second expression)
  *)
  let unify: exp list * exp list -> exp list * exp list * exp list = fun (es1, es2) ->
    (* debug ("unifying " ^ dumpList es1 ^ " and " ^ dumpList es2); *)
    args1 := []; args2 := []; resetArg ();
    let es1 = unifyArgs (es1, es2) in
    let es1 = unifyRest (es1, es2) in
    es1, !args1, !args2
  in

  let compactArg : exp -> exp = fun e ->
    match extractConcats [e] with
      | ([e'], cs) -> newConcats := !newConcats @ cs; e'
      | _ -> failwith "compactArg: impossible happened"
  in
  
  let rec insert : piFunInfo -> piFunInfo list -> piFunInfo list = fun cNew concats ->
    match (cNew, concats) with
    | ((nameNew, Basic (Concat (defNew, _))), ((nameOld, Basic (Concat (defOld, _))) as cOld) :: cs) -> 
      begin
      try
        let (def, argsOldPre, argsNewPre) = unify (defOld, defNew) in
        let argsOld = map compactArg argsOldPre in
        let argsNew = map compactArg argsNewPre in
        if for_all2 equal argsOld argsNew then
          (* cOld and cNew are the same *)
          cOld :: (nameNew, Rewrite (Sym ((nameOld, Prefix), argsNew, Unknown, freshDet ()))) :: cs
        else if not needDisjoint then
          (* just compare cNew to the rest *)
          cOld :: insert cNew cs
        else if defOld = def then
          (* unifying with cOld *)
          cOld :: (nameNew, Rewrite (Sym ((nameOld, Prefix), argsNew, Unknown, freshDet ()))) :: cs
        else if defNew = def then
          (* unifying with cNew *)
          (nameOld, Rewrite (Sym ((nameNew, Prefix), argsOld, Unknown, freshDet ()))) :: insert cNew cs
        else
          (* unifying with a fresh constructor *)
          let nameFresh = newConcatName () in
          let cFresh = (nameFresh, Basic (concat def)) in
          arities := (nameFresh, length argsOld) :: !arities;
          newConcats := cFresh :: !newConcats; 
          (nameOld, Rewrite (Sym ((nameFresh, Prefix), argsOld, Unknown, freshDet ()))) ::
          (nameNew, Rewrite (Sym ((nameFresh, Prefix), argsNew, Unknown, freshDet ()))) :: cs
          
      with 
      | Disjoint ->
        (* debug ("disjoint: " ^ nameNew ^ " and " ^ nameOld); *)
        disjointPairs := (nameOld, nameNew) :: !disjointPairs; 
        cOld :: insert cNew cs
      | NoUnify s ->
        (* debug ("cannot unify " ^ nameNew ^ " with " ^ nameOld ^ ": " ^ s); *)
        if needDisjoint then
          failwith ("cannot unify: " ^ s)
        else
          cOld :: insert cNew cs 
          
      end

    | (_, cOld :: cs) -> cOld :: insert cNew cs (* cOld already rewritten, skip *) 
    | (_, []) -> [cNew]

  in
  let insertConcat : piFunInfo -> unit = fun c ->
    
    (* debug ("inserting: " ^ showFun c); *)
    
    concats := insert c !concats;
    insertConcats !newConcats;
    
  in iter insertConcat cs
  
(* TODO: this can be rewritten using expandFormatFuns *)
let rewriteConcats : exp list -> exp list = 
  
  let replaceArgs : exp list -> exp -> exp = fun args -> function
    | Sym (("arg", _), [Int (i, _)], _, _) -> nth args (Int64.to_int i)
    | e -> e
  in
  
  let rec rewrite : exp -> exp = function
    | Sym ((sym, _), args, _, tag) as e ->
      begin try
      match assoc sym !concats with
        | Basic _    -> e
        | Rewrite e' -> visitExpPost rewrite (visitExpPost (replaceArgs args) (setTag tag e'))
      with
        Not_found -> e
      end
      
    | e -> e
    
  in
  map (visitExpPost rewrite)

(**
  Leave only basic concats. Also remove unused concats (those turned into constants).
*)
let cleanupConcats : exp list -> unit = fun es ->
  concats := filter (function (c, Basic _) when exists (containsSym c) es -> true | _ -> false) !concats 
  (* concats := filter (function (_, Basic _) -> true | _ -> false) !concats *) 
      
(*************************************************)
(** {1 Extracting Parsers} *)
(*************************************************)

let extractParsers : exp list -> exp list = fun events ->
    
  let matchParser : exp -> piFunInfo -> bool = fun e -> function
    | (name, Basic e') -> equal e e'
    | _ -> false 
  in

  let insertParser : exp -> string = fun e ->
	  try let (name, _) = List.find (matchParser e) !parsers in name 
	  with Not_found -> 
    begin
      let name = newParserName () in
      
      debug ("adding parser, " ^ name ^"(x) = " ^ dump e);
      
      parsers := !parsers @ [(name, Basic e)];
      arities := (name, 1) :: !arities;
      name
    end
  in

  let check : exp -> exp = function 
    | String _ -> fail "extractParsers: string in a parsing expression"
    | e when isArithmetic e -> e
    | Sym ((s, _), _, _, _) as e -> 
      if not (List.mem s ["arg"; "lenarg"]) then
      begin
        debug ("check, unmatched symbol:" ^ dump e);
        fail "extractParsers: unmatched symbol "
      end
      else e
    | Concat _ -> fail "extractParsers: concat in a parsing expression"
    | e -> e
  in

  let extract : exp -> exp = function
    | Range (x, pos, len, tag) as e ->
      
      debug ("\n===============================\nextracting parser, e = " ^ dump e);
      debug ("extracting parser, x = " ^ dump x);
      
      let argLen = mkLen Unknown 0 in
      let arg = mkArg Unknown 0 in
      let xLen = match getLen x with
        | Unknown -> failwith "extractParsers: range base without length"
        | l -> l
      in
      (* 
        We strip deterministic tags because otherwise the following might happen:
        x{i, j} gets id1
        x'{i, j} gets id2 and id2 <> id1
        both expressions yield arg0{i, j}, but because the tags point to different ids,
        they will not be considered equal.
        
        It's important to replace xLen first, because it might contain x.
      *)
      let e' = visitExpPre removeDet (substMany [xLen; x] [argLen; arg] e) in
      
      debug ("extracting parser, e' = " ^ dump e');
      
      ignore (visitExpPost check e');  
      let name = insertParser e' in
      Sym ((name, Prefix), [x], Unknown, tag)
      
    | e -> e
  in
  
  map (visitExpPre extract) events   

let cleanupParsers : exp list -> unit = fun es ->

  parsingRules := filter (fun p -> exists (containsSym (parserName p)) es) !parsingRules;
  parsers := filter (fun (p, _) -> exists (containsSym p) es) !parsers

(*************************************************)
(** {1 Parsing Rules} *)
(*************************************************)

let computeParsingRules : piFunInfo list -> unit = fun ps ->
  
  let applyParser : piFunInfo -> piFunInfo -> unit = fun parser concat ->

    debug ("applyParser, parser: " ^ showFun parser);
    debug ("applyParser, concat: " ^ showFun concat);
    
    match (parser, concat) with
      | ((parserFun, Basic parserDef), (concatFun, Basic concatDef)) ->
        let argLen = mkLen Unknown 0 in
        let arg = mkArg Unknown 0 in
        let concatLen = match getLen concatDef with
          | Unknown -> failwith "applyParser: cannot compute concat def length"
          | l -> l
        in

        (* debug ("applyParser: replacing " ^ dump argLen ^ " by " ^ dump concatLen);

        let e = subst argLen concatLen parserDef in
        
        debug ("applyParser: replacing " ^ dump arg ^ " by " ^ dump concatDef);
        
        let e = subst arg concatDef e in
        *)
                          
        let e = substMany [argLen; arg] [concatLen; concatDef] parserDef in 
        
        (* debug ("applyParser: e after subst arg = " ^ dump e); *)
        
        let e' = visitExpPost simplify e in
        
        if !verbose then prerr_endline ("applyParser " ^ parserFun ^ " to " ^ concatFun ^ ": \n  " 
                                                       ^ dump e ^ "\n  ~> " ^ dump e' ^ "\n");
        parsingRules := !parsingRules @ [((parserFun, concatFun), e')]
        
      | _ -> () (* not a basic concat, skip it *)
          
  in 
  
  replaceTagsInConcats ();
  iter (fun parser -> iter (applyParser parser) !concats) ps

(*************************************************)
(** {1 Traversal with Context} *)
(*************************************************)

type pCtx = exp list

let mkFact : exp -> exp = function
  | Sym ((("IfEq"), _), args, _, _) -> eq args
  | Sym ((("If"), _), [e], _, _) -> e
  | _ -> failwith "mkFact: unexpected exression"


let iterWithCtx: (pCtx -> exp -> unit) -> exp list -> unit = fun f -> 
  
  let rec doIter: pCtx -> exp list -> unit = fun ctx -> function
    (* a somewhat arbitrary choice not do descend into an auxiliary if itself, let's see *)
  | e :: es when isAuxiliaryIf e -> doIter (mkFact e :: ctx) es
  | e :: es -> f ctx e; doIter ctx es
  | [] -> ()
  
  in doIter []


let mapWithCtx: (pCtx -> exp -> exp) -> exp list -> exp list = fun f -> 

  let rec doMap: pCtx -> exp list -> exp list = fun ctx -> function
    (* a somewhat arbitrary choice not do descend into an auxiliary if itself, let's see *)
  | e :: es when isAuxiliaryIf e -> e :: doMap (mkFact e :: ctx) es
  | e :: es -> f ctx e :: doMap ctx es
  | [] -> []
  
  in doMap []


(*************************************************)
(** {1 Parsing Safety} *)
(*************************************************)

(*
  FIXME: used by the output functions, but remove later 
*)
let isValidParse : exp -> bool = function
  | Sym (("arg", _), _, _, _) -> true
  | Concat _                  -> false
	| e when isConcrete e       -> true
	| _                         -> false

let checkParsers : pCtx -> exp -> unit = fun ctx -> 

  let mkConcatExpr : piFun -> exp = fun cname ->
    Sym ((cname, Prefix), [], Unknown, NoTag)
  in
  
  (* Could possibly just give rewrite rules to SMT, but don't want to mess with foralls yet *)
  let rewriteParsers : piFun -> exp -> exp = fun cname e -> 
    let c = mkConcatExpr cname in
    match e with
    | Sym ((p, _), [c'], _, _) when c = c' -> 
      begin
          try List.assoc (p, cname) !parsingRules
          with Not_found -> e
      end
    | e -> e
  in

  let rec checkTags : exp list -> bool = function
    | [] -> true
    | e :: es ->
      match e with 
        | Sym (("tag", _), [t], _, _) -> 
          if not (equal e t) then
          begin
            debug ("checkParsingSafety: tag " ^ dump e ^ " not checked");
            false
          end
          else checkTags es
        | _ -> checkTags es
  in

  let rec getMinLen : exp list -> exp = function
    | (Sym (("lenarg", _), _, l, _)) as e :: es -> addLen l (addLen e (getMinLen es))
    | Sym (("tag", _), _, l, _) :: es -> addLen l (getMinLen es)
    | e :: es -> getMinLen es
    | [] -> zero
  in
  
  (* check an application of a parser to specific concat *)
  let checkConcat : piFun -> exp -> piFunInfo -> bool = fun p e -> function
    | (cname, Basic (Concat (es_c, _))) ->
      
      debug ("\ncheckParsingSafety: trying concat " ^ cname);
      solver_debug := false;
      
      resetFacts ();
      let c = mkConcatExpr cname in
      let ctx = List.map (subst e c) ctx in
      let ctx = List.map (visitExpPre (rewriteParsers cname)) ctx in
      (* debug ("checkParsingSafety: ctx = " ^ dumpList ctx); *)
      let minLen = getMinLen es_c in
      
      solver_debug := true;
      addFact (eq [getLen c; getRealLen e]);
      List.iter addFact ctx;
      if not (checkTags es_c) then false
      else if not (greaterEqual (getLen c) minLen) then
      begin
        debug ("checkParsingSafety: lengths in " ^ dump c ^ " not checked");
        false
      end
      else true
      
    | _ -> true
  in
      
  (* check an application of a parser to all possible concats *)
  let checkParse : exp -> unit = fun a -> match a with
    | Sym ((p, _), [e], _, _) when isParser p -> 
      debug ("\n==============================\ncheckParsingSafety: checking the application " ^ dump a);
      begin try 
        let (c, _) = List.find (checkConcat p e) !concats in
        solver_debug := false;
        (* cannot fail *)
        match List.assoc (p, c) !parsingRules with
          | Sym (("arg", _), [Int (i64, _)], _, _) ->
            begin 
            let i = Int64.to_int i64 in
            try 
              let p' = inverse_assoc (c, i) !safeParsers in
              if p <> p' then fail ("two different forms of the same safe parser encountered: c = " ^ c ^ ", i = " ^ string_of_int i)
            with
              Not_found -> safeParsers := (p, (c, i)) :: !safeParsers
            end
          | _ -> debug ("checkParsingSafety: the parser is not an inverse in " ^ dump a);
      with 
        Not_found -> 
          solver_debug := false;
          debug ("checkParsingSafety: no concat satisfies the application " ^ dump a);
      end
        
    | _ -> ()

  in visitAllSubexp checkParse


let computeSafeParsers : exp list -> unit = iterWithCtx checkParsers


let isSafeParser : piFun -> bool = fun p -> isParser p && List.mem_assoc p !safeParsers

(*************************************************)
(** {1 Filtering} *)
(*************************************************)


let rec containsPtr : exp -> bool = function
  | Int _ -> false
  | String _ -> false
  | Range (e, _, _, _) -> containsPtr e
  | Sym (_, es, _, _) -> exists containsPtr es
  | Ptr _ -> true
  | _ -> false

(*
let isComparison : exp -> bool = function
  | Sym ((("branchT" | "branchF"), _), [Sym (((">" | "<" | "<=" | ">=" | "=="), _), _, _, _)], _, _) -> true
  | _ -> false
*)

let isArithmeticWrite : exp -> bool = function
  | Sym (("write", _), [e], _, _) -> isArithmetic e
  | _ -> false

let isArithmeticEq : exp -> bool = function
  | Sym ((("IfEq"), _), [e1; e2], _, _) when isArithmetic e1 || isArithmetic e2 -> true
  | _ -> false

let isLenWrite : exp -> bool = function
  | Sym (("write", _), [e], _, _) when isLength e -> true
  | _ -> false

(*
  FIXME: need to carefully justify why we can remove arithmetic writes.
*)
let boringEvent : exp -> bool = fun e ->
  (containsPtr e) || (isCastEq e) || (isBoringComparison e) || (isLenWrite e)
 
let interestingEvent e = not (boringEvent e)

let cryptographicEvent e = not ((isAuxiliaryIf e) || (isArithmeticWrite e) || (isArithmeticEq e))

let preprocess e = 
  
  let rec stripCast : exp -> exp = function
      (* FIXME: need to preserve identity? *)
    | (Sym (("castToInt", _), [a; _], _, _)) as e ->
      (* debug ("stripping cast from e = " ^ dump e); *)
      addFact (eq [e; a]);
      stripCast a
    | e -> (* debug ("not stripping cast from e = " ^ dump e); *) e
  in
  
  let rewriteCrypto : exp -> exp = function
    | Sym (("HMAC", fixity), [String hash; msg; key], l, tag) -> Sym (("HMAC_" ^ hash, fixity), [msg; key], l, tag)
    | Sym (("SHA256", fixity), [e], l, tag) ->
      (* we cannot use a CV rewrite rule cause the key needs to be freshly generated *)
      let sha256key = Sym (("var", Prefix), [String "SHA256_key"], Unknown, NoTag) in 
      Sym (("SHA_hash", fixity), [sha256key; e], l, tag) 
    | Sym (("IfEq", _), [Sym (("DSA_verify", _), es, l, tag); eOne], l', tag') when equalLen eOne one -> 
      Sym (("If", Prefix), [Sym (("DSA_check", Prefix), es, l, tag)], l', tag')
    | e -> e
  in

  let e = visitExpPost Exp.preprocess e in
  let e = visitArithPre stripCast e in
  let e = visitExpPre rewriteCrypto e in (*if cryptographicEvent e then visitExpPre rewriteCrypto e else e in *) 
  e

let procAndFilter es = filter interestingEvent (map preprocess es)

let postprocess = filter cryptographicEvent

    
(*************************************************)
(** {1 User Input} *)
(*************************************************)

let crypto : string list ref = ref []

(** Printed after the automatically generated facts *)
let crypto2 : string list ref = ref []

let query : string list ref = ref []

let envp : string list ref = ref []

(**
  These are used for typechecking, but are not repeated in the actual model output.
*)
let typehints: string list ref = ref []

(**
  This part is dropped.
*)
let model: string list ref = ref []

(* let keys : string list ref = ref [] *)

(* FIXME: try in recursive function bad, will exceed stack for very long files *)
let rec readFile : in_channel -> string list = fun file ->
  try
    let line = input_line file in
    line :: readFile file
  with End_of_file -> []

let rec splitTemplate: string list ref -> string list -> unit = fun dest -> function
  | l1 :: l2 :: ls' when trim l2 = "<Environment>" -> splitTemplate envp (((l1 ^ "\n" ^ l2) :: ls'))
  | l1 :: l2 :: ls' when trim l2 = "<Query>" -> splitTemplate query (((l1 ^ "\n" ^ l2) :: ls'))
  | l1 :: l2 :: ls' when trim l2 = "<Model>" -> splitTemplate model (((l1 ^ "\n" ^ l2) :: ls'))
  | l1 :: l2 :: ls' when trim l2 = "<Type hints>" -> splitTemplate typehints (((l1 ^ "\n" ^ l2) :: ls'))
  | l1 :: l2 :: ls' when trim l2 = "<Crypto2>" -> splitTemplate crypto2 (((l1 ^ "\n" ^ l2) :: ls'))
  | l :: ls'  -> dest := !dest @ [l]; splitTemplate dest ls'   
  | [] -> ()

let readTemplate: in_channel -> unit = fun file -> splitTemplate crypto (readFile file)

