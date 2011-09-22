(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

 
open List

open Types
open Utils
open Solver
open Exp
open Execute

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

(** Thrown by [unify] *)
exception Disjoint


(*************************************************)
(** {1 State} *)
(*************************************************)

let concats : piFunInfo list ref = ref []

let parsingRules : parsingRule list ref = ref []

let arities : (piFun * int) list ref = ref []

let concatId : int ref = ref 0
let parserId : int ref = ref 0

let argId : int ref = ref 0
let lenId : int ref = ref 0

let verbose : bool ref = ref false

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

let newConcatName : unit -> string = fun () ->
  concatId := !concatId + 1;
  "conc" ^ string_of_int !concatId  

let newParserName : unit -> string = fun () ->
  parserId := !parserId + 1;
  "parse" ^ string_of_int !parserId  

let isParseFun : string -> bool = fun s ->
  exists (function ((s', _), _) when s = s' -> true | _ -> false) !parsingRules

let parserName : parsingRule -> string = function ((name, _), _) -> name

(* 
  Argument must start from 0, because we use it for addressing the actuals array.
  
  Must be deterministic because same arguments should match. Also we use structural identity
  
*)
let newArg : len -> exp = fun len ->
  let id = !argId in
  argId := !argId + 1;
  Sym (("arg", Prefix), [mkInt id], len, NoTag)

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

(* Used to give lengths to formal arguments, there we need to strip it all *)
let getRealLen = function
  | Sym(_, _, l, _) -> l
  | e -> getLen e

let getRealLenLen e = match getRealLen e with
  | Unknown -> fail "getRealLenLen: unknown length"
  | l -> getRealLen l

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
(** {1 Transformations} *)
(*************************************************)

let extractConcats : exp list -> exp list * piFunInfo list = fun events ->
  
  let concats : piFunInfo list ref = ref [] in
  let argLens : len list ref = ref [] in

  let isArgLen : exp -> bool = fun e -> exists (fun l -> equalLen e l) !argLens in

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
	    | e when isArg e && not (exists (fun e' -> equalLen e (getRealLen e')) es) ->
	      argLens := !argLens @ [getRealLen e];
	    | e -> debug ("collectArgLens: skipping e = " ^ dump e)
    in iter f es
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
                    let l_pair = (find (fun (l, _) -> equalLen l (getRealLen e)) lens) in
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
      arities := !arities @ [(name, length args)];
      debug ("extract, argLens = " ^ dumpList !argLens);
      debug ("extract, e = " ^ dump (Concat (es, tag)));
      debug ("extract, e_new = " ^ dump (concat def));
      Sym ((name, Prefix), args, Unknown, tag)
    | e -> e
  in
  
  let events' = map (visitExpPre extract) events in
  (events', !concats)


let rec insertConcats : piFunInfo list -> unit = fun cs ->

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
    
	  debug ("unify, es1: " ^ dumpList es1);
	  debug ("unify, es2: " ^ dumpList es2);
    
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
        if defOld = def then
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
          
      with Disjoint -> cOld :: insert cNew cs
      end

    | (_, cOld :: cs) -> cOld :: insert cNew cs (* cOld already rewritten, skip *) 
    | (_, []) -> [cNew]

  in
  let insertConcat : piFunInfo -> unit = fun c ->
    debug ("inserting: " ^ showFun c);
    concats := insert c !concats;
    insertConcats !newConcats;
    
  in iter insertConcat cs
  

let rewriteConcats : exp list -> exp list = 
  
  let replaceArgs : exp list -> exp -> exp = fun args -> function
    | Sym (("arg", _), [Int (i, _)], _, _) -> nth args (Int64.to_int i)
    | e -> e
  in
  
  let rec rewrite : exp -> exp = function
    | Sym ((sym, _), args, _, id) as e ->
      begin try
      match assoc sym !concats with
        | Basic _    -> e
        | Rewrite e' -> visitExpPost rewrite (visitExpPost (replaceArgs args) e')
      with
        Not_found -> e
      end
      
    | e -> e
    
  in
  map (visitExpPost rewrite)
  
(**
  Leave only basic concats.
*)
let cleanupConcats : unit -> unit = fun () ->
  concats := filter (function (_, Basic _) -> true | _ -> false) !concats


(* FIXME: move into a single parser analysis function *)
let subst : exp -> exp -> exp -> exp = fun a b c ->
  (* Using equalLen because this is used to substitute both lengths and normal subexpressions *)
  (* let d = arithSimplify (op "-" [ *)
  if equalLen a c then b else c

let extractParsers : exp list -> exp list * piFunInfo list = fun events ->
  
  let parsers : piFunInfo list ref = ref [] in

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
      
      debug ("extracting parser: " ^ dump e);
      
      let argLen = mkLen Unknown 0 in
      let arg = resetArgAndLen (); newArg Unknown in
      let xLen = match getLen x with
        | Unknown -> failwith "extractParsers: range base without length"
        | l -> l
      in
      let e' = visitExpPre (comp (subst xLen argLen) (subst x arg)) e in
      ignore (visitExpPost check e');  
      let name = newParserName () in
      parsers := !parsers @ [(name, Basic e')];
      arities := (name, 1) :: !arities;
      Sym ((name, Prefix), [x], Unknown, tag)
      
    | e -> e
  in
  
  let events' = map (visitExpPre extract) events in
  (events', !parsers)
  

let computeParsingRules : piFunInfo list -> unit = 
  
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
        let e = visitExpPost (comp (subst arg concatDef) (subst argLen concatLen)) parserDef in
        let e' = visitExpPost simplify e in
        if !verbose then prerr_endline ("applyParser " ^ parserFun ^ " to " ^ concatFun ^ ": \n  " 
                                                       ^ dump e ^ "\n  ~> " ^ dump e' ^ "\n");
        parsingRules := !parsingRules @ [((parserFun, concatFun), e')]
        
      | _ -> () (* not a basic concat, skip it *)
          
  in 
  iter (fun parser -> iter (applyParser parser) !concats)


let isValidParse : exp -> bool = function
  | Sym (("arg", _), _, _, _) -> true
  | Concat _                  -> false
	| e when isConcrete e       -> true
	| _                         -> false


(**
  Assumes that [cleanupConcats] has been called.
*)
let checkParsingSafety : exp list -> unit = 

  (*
    For variables in the process contains the list of concatenations that these variables can contain.
    If no entry then all concatenations are possible. This is used to account for tag checking.
  *)
  let possibleValues : (exp * piFun list) list ref = ref [] in

  let findParseResult : piFun -> piFun -> exp = fun f g ->
    try assoc (f, g) !parsingRules
    with Not_found -> failwith ("checkParse: cannot find parse result for " ^ f ^ ", " ^ g)
  in

  
  let checkParse : exp -> exp = function
    | Sym ((f, _), [e], _, _) when isParseFun f ->
      let values = try assoc e !possibleValues with Not_found -> map fst !concats in
      let parseResults = map (findParseResult f) values in
      if not (for_all isValidParse parseResults) then
      begin
        debug ("checkParse: invalid parse while checking f(e) = " ^ f ^ "(" ^ dump e ^ ")");
        debug ("checkParse: possible values for e: " ^ String.concat ", " values);
        debug ("checkParse: possible values of f(e): " ^ String.concat "\n " (map dump parseResults));
        failwith ("checkParse: invalid parse");
      end;
      e
    | e -> e
  in
  
  let areDifferentTags : exp -> exp -> bool = fun t1 t2 -> match t1, t2 with
    | String s1, String s2 -> s1 <> s2 (* FIXME: should only compare the overlapping region? No, I guess this is fine. *)
    | _ -> false
  in

  let check : exp -> unit = function
    | Sym (("IfEq", _), [Sym ((f, _), [e], _, _); c], _, _) when isParseFun f && isConcrete c ->
      if for_all (function ((f', _), c') -> f' <> f || isConcrete c') !parsingRules then
      begin
        let values = List.concat (map (function ((f', g), c') -> if f <> f' || areDifferentTags c c' then [] else [g]) !parsingRules) in
        possibleValues := (e, values) :: !possibleValues;
        debug ("checkParsingSafety: adding e = " ^ dump e ^ ", values = " ^ String.concat ", " values);
      end
      
    | e -> ignore (visitExpPre checkParse e)
  
  in iter check


(*************************************************)
(** {1 Soundness Proof} *)
(*************************************************)

let prove : unit -> unit = function _ -> failwith "prove: undefined"


(*************************************************)
(** {1 Pi Output} *)
(*************************************************)

(* let keys : string list ref = ref [] *)

let constants : string list ref = ref []

let crypto : string list ref = ref []

let query : string list ref = ref []

let env : string list ref = ref []

let rec readFile : in_channel -> string list = fun file ->
  try
    let line = input_line file in
    line :: readFile file
  with End_of_file -> []
  

let showPiExp : exp -> string = fun e ->

  let rec showExpBody : exp -> string = function 
	  | Int (ival, len) -> 
      let result = "integer_" ^ Int64.to_string ival in
      if not (List.mem result !constants) then constants := !constants @ [result];
      result
	  | String s -> 
      let result = "string_" ^ s in
      if not (List.mem result !constants) then constants := !constants @ [result];
      result ^ "()"
    | Sym (("var", _), [String s], _, _) -> s      
	  | Sym ((s, Prefix), es, len, id) ->
	    s ^ "(" ^ String.concat ", " (map showExp es) ^ ")"
    | e -> "unexpected(" ^ dump e ^ ")"      

  and showExp : exp -> string = function e ->
    let name = giveName e in
	  match e with
	    | Sym ((("read"), _), _, _, _) -> 
        "in(c, " ^ name ^ ");";

	    | Sym ((("nonce"), _), _, _, _) -> 
        "new " ^ name ^ ";";
	
	    | Sym (("write", _), [e], _, _) -> 
	      "out(c, " ^ showExp e ^ ");"
	                                                                                       
	    | Sym ((("IfEq"), _), [e1; e2], _, _) ->
	      "if " ^ showExp e1 ^ " = " ^ showExp e2 ^ " then "
	
	    | Sym ((("event"), _), [e], _, _) ->
	      "event " ^ showExp e ^ ";"

      | Sym ((("let"), _), [e], _, _) ->
        "let " ^ giveName e ^ " = " ^ showExp e ^ " in"
	
	    | _ -> showExpBody e

  in
  showExp e

let containsSym : string -> exp -> bool = fun s e ->
  
  let contains : exp -> exp = function
    | Sym ((s', _), _, _, _) when s' = s -> raise Exit
    | e -> e
  in
  
  try ignore (visitExpPost contains e); false with Exit -> true

let cleanupParsingRules : parsingRule list -> exp list -> parsingRule list = fun ps es ->
  filter (fun p -> exists (containsSym (parserName p)) es) ps

let showPiProcess : exp list -> string = fun es ->
  resetNames ();
  let es = splitByType es in
  (* let es = elimCommonSubs es in *)
  let result = String.concat "\n" (map showPiExp es) ^ " 0.\n" in
  result

let print_indent s = print_endline ("  " ^ s)

let writePi : exp list -> exp list -> unit = fun client server ->
  
  let lastParser : string ref = ref "" in
  
  let printConcat : piFunInfo -> unit = function
    | (name, Basic _) -> print_endline ""; print_endline ("data " ^ name ^ "/" ^ string_of_int (assoc name !arities) ^ ".")
    | _ -> ()
  in

  let showParsingRule : parsingRule -> string = function ((parserName, concatName), e) -> 
    if isValidParse e then
    let numargs = assoc concatName !arities in
    let result = match e with
      | Sym (("arg", _), [Int (i, _)], _, _) -> "x" ^ (Int64.to_string i)
      | e -> showPiExp e
    in
    let newParser = (parserName <> !lastParser) in
    let firstParser = (!lastParser = "") in
    lastParser := parserName;
    let punctuation = if firstParser then "" else if newParser then ".\n" else ";\n" in
    punctuation ^ (if newParser then "reduc \n\  " else  "  ") ^
	    (parserName ^ "(" ^ concatName ^ "(" ^ 
	     String.concat ", " (map (fun i -> "x" ^ string_of_int i) (0 -- (numargs - 1))) ^ "))"
	     ^ " = " ^ result)
    else ""

  in

  let printConstant : string -> unit = fun s -> print_endline ("fun " ^ s ^ "/0.") in

  let clientProc = showPiProcess client in
  let serverProc = showPiProcess server in

  parsingRules := cleanupParsingRules !parsingRules (client @ server);

  let reducs = if !parsingRules = [] then "" else (String.concat "" (map showParsingRule !parsingRules)) ^ "." in

  print_endline "free c.";

  iter print_endline !crypto;

  iter printConstant !constants;

  iter printConcat !concats;
  
  print_endline "";
  
  print_endline reducs;

  iter print_endline !query;
  
  print_endline "";
                                                      
  print_endline "let A = ";
  print_endline clientProc;
  print_endline "let B = ";
  print_endline serverProc;
  
  iter print_endline !env  
  
  (*
  print_endline "process !";
  (* iter printKey !keys; *)
  print_indent "new keyAB;";
  print_indent "(!A | !B)"
  *)

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

let boringEvent : exp -> bool = fun e ->
  (containsPtr e) || (isCastEq e) || (isArithComparison e) || (isArithmeticWrite e) ||
  (isArithmeticEq e) || (isLenWrite e)
 
let interestingEvent e = not (boringEvent e)

let cryptographicEvent e = not (isAuxiliaryIf e)

let preprocess e = 
  
  let rec stripCast : exp -> exp = function
      (* FIXME: need to preserve identity? *)
    | (Sym (("castToInt", _), [a; _], _, _)) as e ->
      addFact (eq [e; a]);
      stripCast a
    | e -> e
  in
  
  let rewriteCrypto : exp -> exp = function
    | Sym (("HMAC", fixity), [String hash; msg; key], l, tag) -> Sym (("HMAC_" ^ hash, fixity), [msg; key], l, tag)
    | e -> e
  in
  
  let e' = Exp.preprocess e in
  let e' = visitExpLenPre stripCast e' in
  let e' = visitExpPre rewriteCrypto e' in
  e'

let procAndFilter es = filter interestingEvent (map (visitExpPre preprocess) es)

let postprocess = filter cryptographicEvent

(*************************************************)
(** {1 Main} *)
(*************************************************)

(* let showIML : exp list -> string = fun es -> resetNames (); showIML es *)

;;
begin
  inlineAll := false;

  (* server is typically the process executed first, i.e. P1 *)
  let server = execute (open_in Sys.argv.(1)) in
  let client = execute (open_in Sys.argv.(2)) in

  verbose := true;
  debugEnabled := true;
  
  if !verbose then prerr_endline "raw IML:";
  if !verbose then prerr_endline (showIMLRaw client);
  if !verbose then prerr_endline (showIMLRaw server);

  let server = procAndFilter server in
  let client = procAndFilter client in

  if !verbose then prerr_endline "filtered IML:";
  if !verbose then prerr_endline (showIML client);
  if !verbose then prerr_endline (showIML server);
  
  let (client, clientConcats) = extractConcats client in
  let (server, serverConcats) = extractConcats server in
  let allConcats = clientConcats @ serverConcats in

  if !verbose then showFuns allConcats;
  if !verbose then prerr_endline (showIML client);
  if !verbose then prerr_endline (showIML server);

  insertConcats allConcats;

  if !verbose then showFuns !concats;

  let client = rewriteConcats client in
  let server = rewriteConcats server in

  if !verbose then prerr_endline (showIML client);
  if !verbose then prerr_endline (showIML server);

  cleanupConcats ();

  let (client, clientParsers) = extractParsers client in
  let (server, serverParsers) = extractParsers server in
  let allParsers = clientParsers @ serverParsers in

  if !verbose then showFuns allParsers;
  if !verbose then prerr_endline (showIML client);
  if !verbose then prerr_endline (showIML server);
  
  computeParsingRules allParsers;
  
  checkParsingSafety client;
  checkParsingSafety server;

  crypto := readFile (open_in "crypto.in");
  query := readFile (open_in "query.in");
  env := readFile (open_in "env.in");

  resetNames ();

  let client = postprocess client in
  let server = postprocess server in

  if !verbose then prerr_endline "postprocessed IML:";
  if !verbose then prerr_endline (showIML client);
  if !verbose then prerr_endline (showIML server);

  writePi client server;
end;


