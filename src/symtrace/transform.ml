 
open List

open Types
open Utils
open Exp
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

let argId : int ref = ref 0
let lenId : int ref = ref 0

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

let mkArg: len -> int -> exp = fun len id ->
  Sym (("arg", Prefix), [mkInt id], len, NoTag)

(* 
  Argument must start from 0, because we use it for addressing the actuals array.
  
  Must be deterministic because same arguments should match. Also we use structural identity
  
  FIXME: Shouldn't argument numbering be dealt with locally?
*)
let newArg : len -> exp = fun len ->
  let id = !argId in
  argId := !argId + 1;
  mkArg len id

let mkLen len id = 
  let l = Sym (("lenarg", Prefix), [mkInt id], len, NoTag) in
  addFact (grEq l zero);
  l

let newLen : len -> exp = fun len ->
  let id = !lenId in
  lenId := !lenId + 1;
  mkLen len id

(* FIXME: do something more elegant *)
let resetArgAndLen () = argId := 0; lenId := 0

let mkFormalArgs: piFun -> exp list = fun f ->
  map (fun i -> mkArg (mkLen Unknown i) i) (0 -- (assoc f !arities - 1))


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
      let args = mkFormalArgs f in
      setTag tag (substMany args es e_def)
    | e -> e

  in visitExpPre expand

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

let extractConcats : exp list -> exp list * piFunInfo list = fun events ->
  
  let concats : piFunInfo list ref = ref [] in
  let argLens : len list ref = ref [] in

  let isArgLen : exp -> bool = fun e -> List.exists (fun l -> equalLen e l) !argLens in

  let isArg : exp -> bool = fun e ->
    (* 
    debug ("isArg: e = " ^ dump e);
    debug ("isArg, concrete = " ^ string_of_bool (isConcrete e)); 
    debug ("isArg, arithmetic = " ^ string_of_bool (isArithmetic e));
    debug ("isArg, length = " ^ string_of_bool (isLength e));
    *)
    not (isConcrete e || isArithmetic e || isLength e) in

  let collectArgLens : exp list -> unit = fun es ->
    let f = function
        (* 
          This is a bit convoluted, but hopefully sensible:
          something is a concrete argument, if it looks like an argument and is not equal
          to some other argument's length.
          
          Whatever magic we do here, all mistakes will be caught during checking later, 
          so soundness is not compromised.
        *) 
        | e when isArg e && not (List.exists (fun e' -> equalLen e (getRealLen e')) es) ->
          argLens := !argLens @ [getRealLen e];
        | e -> (* debug ("collectArgLens: skipping e = " ^ dump e) *) ()
    in List.iter f es
  in 

  (*
    Go through a concat body and replace the actual arguments with formal arguments.
    Param 1: the list of pairs (actual length, formal length) that are still available for taking.
    Param 2: the concat body.
    Return : (the new concat body with formal arguments, the list of actual arguments that were replaced) 
  *)
  let rec collectArgs : (len * len) list -> exp list -> exp list * exp list = fun lens -> function
    | e :: es when isArgLen e ->
      let len = newLen (getRealLen e) in
      let (def, args) = collectArgs (lens @ [e, len]) es in
      (len :: def, args)

    | e :: es when isArg e -> 
      let (len, lens') = 
        try 
            let l_pair = (List.find (fun (l, _) -> equalLen l (getRealLen e)) lens) in
            (snd l_pair, remove l_pair lens) 
        with Not_found -> (newLen (getRealLenLen e), lens) in (* OLD? check injectivity separately *)
      let arg = newArg len in
      let (def, args) = collectArgs lens' es in
      (arg :: def, e :: args)
      
    | e :: es ->
      let (def, args) = collectArgs lens es in
      (e :: def, args)

    | [] -> resetArgAndLen (); ([], [])
  in

  let extract : exp -> exp = function
    | Concat (es, tag) ->
      collectArgLens es;
      let name = newConcatName () in
      let (def, args) = collectArgs [] es in
      concats := !concats @ [(name, Basic (concat def))];
      arities := !arities @ [(name, List.length args)];
      debug ("extract, argLens = " ^ dumpList !argLens);
      debug ("extract, e = " ^ dump (Concat (es, tag)));
      debug ("extract, e_new = " ^ dump (concat def));
      Sym ((name, Prefix), args, Unknown, tag)
    | e -> e
  in
  
  let events' = map (visitExpPre extract) events in
  (events', !concats)


(** Thrown by [unify] *)
exception Disjoint

(**
  [allowSplit] - should the concats be split into simpler concats when possible?  
  If [allowSplit] is true, all the resulting concats are disjoint.
  If [allowSplit] is false, some of the concats may not be disjoint, refer to {! Transform.disjointPairs}.
*)
let rec insertConcats : ?allowSplit: bool -> piFunInfo list -> unit = fun ?(allowSplit = true) cs ->

  let newConcats : piFunInfo list ref = ref [] in 
  
  let isArgLen : exp -> bool = function
    | Sym (("lenarg", _), _, _, _) -> true
    | _ -> false
  in
  
  let isArg : exp -> bool = function
    | Sym (("arg", _), _, _, _) -> true
    | _ -> false
  in

  (*
    Param1: list of lengths collected in first expression
    Param2: list of lengths collected in second expression
    Param3: (first expression, second expression)
    Result: (unified expression, substitutions unifying the first expression, substitutions unifying the second expression)
  *)
  let rec unify : len list -> len list -> exp list * exp list -> exp list * exp list * exp list = 
    fun lens1 lens2 -> function (es1, es2) ->
    (*
      debug ("unify, es1: " ^ dumpList es1);
      debug ("unify, es2: " ^ dumpList es2);
    *)
    match (es1, es2) with
    | ([(Sym (("arg", _), _, _, _)) as arg1], es2) ->
      let arg = newArg (mkLen (getRealLenLen arg1) (length lens1)) in
      resetArgAndLen();
      ([arg], [arg1], match es2 with [e] -> [e] | es2 -> [concat es2])

    | (es1, [(Sym (("arg", _), _, _, _)) as arg2]) ->
      let arg = newArg (mkLen (getRealLenLen arg2) (length lens1)) in
      resetArgAndLen();
      ([arg], (match es1 with [e] -> [e] | es1 -> [concat es1]), [arg2])

    | (arg1 :: es1, arg2 :: es2) when isArg arg1 || isArg arg2 ->
      (*
      debug ("arg1: " ^ dump arg1);
      debug ("arg2: " ^ dump arg2);

      debug ("lens1: " ^ dumpList lens1);
      debug ("lens2: " ^ dumpList lens2);
      *)
      let lenId = try (findIndex (equalLen (getRealLen arg1)) lens1)
                  with Not_found -> failwith "unify: length field not found for potential argument" in 
      if not (equalLen (getRealLen arg2) (nth lens2 lenId)) then
        failwith "unify: arguments aligned, but length fields not";
      let len = mkLen (getRealLenLen arg1) lenId in
      let arg = newArg len in
      let (def, args1, args2) = unify lens1 lens2 (es1, es2) in
      (arg :: def, arg1 :: args1, arg2 :: args2)

    | (len1 :: es1, len2 :: es2) when isArgLen len1 || isArgLen len2 ->
      if not (equalLen (getRealLen len1) (getRealLen len2)) then
        failwith "unify: length fields not aligned";
      let len = mkLen (getRealLen len1) (length lens1) in
      let (def, args1, args2) = unify (lens1 @ [len1]) (lens2 @ [len2]) (es1, es2) in
      (len :: def, args1, args2)

    | (Int (i1, len1) :: es1, Int (i2, len2) :: es2) ->
      if not (equalLen len1 len2) then
        failwith "unify: integer fields of different lengths";
      if i1 <> i2 then
        raise Disjoint
      else 
        let (def, args1, args2) = unify lens1 lens2 (es1, es2) in
        (Int (i1, len1) :: def, args1, args2)
        
    | (String s1 :: es1, String s2 :: es2) ->
      let len1 = String.length s1 in
      let len2 = String.length s2 in
      let minLen = min len1 len2 in
      let s1' = String.sub s1 0 minLen in
      let s2' = String.sub s2 0 minLen in
      if s1' <> s2' then
        raise Disjoint
      else if len1 <> len2 then
        failwith "unify: strings have different length but are the same over common prefix"
      else
        let (def, args1, args2) = unify lens1 lens2 (es1, es2) in
        (String s1 :: def, args1, args2)

    | ([], []) -> resetArgAndLen(); ([], [], [])

    | _ -> failwith "unify: cannot unify"

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
        let (def, argsOldPre, argsNewPre) = unify [] [] (defOld, defNew) in
        resetArgAndLen ();
        let argsOld = map compactArg argsOldPre in
        let argsNew = map compactArg argsNewPre in
        if for_all2 equal argsOld argsNew then
          (* cOld and cNew are the same *)
          cOld :: (nameNew, Rewrite (Sym ((nameOld, Prefix), argsNew, Unknown, freshDet ()))) :: cs
        else if not allowSplit then
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
          
      with Disjoint ->
        disjointPairs := (nameOld, nameNew) :: !disjointPairs; 
        cOld :: insert cNew cs
      end

    | (_, cOld :: cs) -> cOld :: insert cNew cs (* cOld already rewritten, skip *) 
    | (_, []) -> [cNew]

  in
  let insertConcat : piFunInfo -> unit = fun c ->
    (*
    debug ("inserting: " ^ showFun c);
    *)
    concats := insert c !concats;
    insertConcats !newConcats;
    
  in iter insertConcat cs
  
(**
  Leave only basic concats.
*)
let cleanupConcats : unit -> unit = fun () ->
  concats := filter (function (_, Basic _) -> true | _ -> false) !concats

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
      let arg = resetArgAndLen (); newArg Unknown in
      let xLen = match getLen x with
        | Unknown -> failwith "extractParsers: range base without length"
        | l -> l
      in
      (* 
        We strip deterministic tags because the concatenation expressions don't represent any particular
        value, but instead a function, and so deterministic applications should be considered the same.
        
        It's important to replace xLen first, because it might contain x.
      *)
      let e' = removeDet (substMany [xLen; x] [argLen; arg] e) in
      
      debug ("extracting parser, e' = " ^ dump e');
      
      ignore (visitExpPost check e');  
      let name = insertParser e' in
      Sym ((name, Prefix), [x], Unknown, tag)
      
    | e -> e
  in
  
  map (visitExpPre extract) events   

let cleanupParsers : exp list -> unit = fun es ->

	let containsSym : string -> exp -> bool = fun s e ->
	  
	  let contains : exp -> exp = function
	    | Sym ((s', _), _, _, _) when s' = s -> raise Exit
	    | e -> e
	  in
	  
	  try ignore (visitExpPost contains e); false with Exit -> true
  in    
  
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
        let arg = resetArgAndLen (); newArg Unknown in
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
          fail (* debug *) ("checkParsingSafety: no concat satisfies the application " ^ dump a);
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
    | e -> e
  in
  
  let e' = visitExpPost Exp.preprocess e in
  let e' = visitArithPre stripCast e' in
  let e' = visitExpPre rewriteCrypto e' in
  e'

let procAndFilter es = filter interestingEvent (map preprocess es)

let postprocess = filter cryptographicEvent

    
(*************************************************)
(** {1 User Input} *)
(*************************************************)

let crypto : string list ref = ref []

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
  | l :: ls'  -> dest := !dest @ [l];  splitTemplate dest ls'   
  | [] -> ()  

let readTemplate: in_channel -> unit = fun file -> splitTemplate crypto (readFile file)

