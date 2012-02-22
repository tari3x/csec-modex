
open List

open Types
open Execute
open Exp
open Utils
open Transform
open Imltypes
open Solver

open Cryptoverif.Types
open Cryptoverif.Syntax
open Cryptoverif.Stringmap



(*************************************************)
(** {1 Typechecking} *)
(*************************************************)

let templateFile = ref ""

(** {2 Collecting Types from the Environment} *)
(*****************************)

let convertFunType: typet list * typet -> ftype = fun (ts, t) ->
  map (fun t -> parseType t.tname) ts, parseType t.tname 

let collectEnvTypes : unit -> unit = fun () -> 
  
  let doEntry : string -> env_entry -> unit = fun k -> function
	  | EFunc f -> funTypes := (f.f_name, convertFunType f.f_type) :: !funTypes 
    | EEvent f ->
      (* for some reason it adds an extra bitstring parameter in front of the ones I define *)
      let (atypes, rtype) = f.f_type in
      funTypes := (f.f_name, convertFunType (tl atypes, rtype)) :: !funTypes
	  | EVar b -> funTypes := (b.sname, convertFunType ([], b.btype)) :: !funTypes
	  | _ -> ()
  in
  
  StringMap.iter doEntry !env

let rec collectInputProcessTypes : inputprocess -> unit = fun q -> 
  
  let rec collectPattern : pattern -> unit = function
    | PatVar b -> funTypes := (b.sname, convertFunType ([], b.btype)) :: !funTypes
    | PatTuple (_, pats) -> iter collectPattern pats 
    | PatEqual _ -> ()
  in
  
  match q.i_desc with
	  | Nil -> ()
	  | Par (q, q') -> collectInputProcessTypes q; collectInputProcessTypes q'
	  | Repl (_, q) -> collectInputProcessTypes q
	  | Input (_, pat, q) -> collectPattern pat; collectOutputProcessTypes q

and collectOutputProcessTypes : process -> unit = fun p ->
  match p.p_desc with
	  | Yield -> ()
	  | Restr (b, p) ->
      funTypes  := (b.sname, convertFunType ([], b.btype)) :: !funTypes;
      collectOutputProcessTypes p
	  | Test (_, p, p') -> collectOutputProcessTypes p; collectOutputProcessTypes p'
	  | Find _ -> fail "collectTypes: unexpected find construct"
	  | Output (_, _, q) -> collectInputProcessTypes q
	  | Let (pat, _, p, p') ->
      collectPatternTypes pat;  
      collectOutputProcessTypes p; collectOutputProcessTypes p'
	  | EventP (_, p) -> collectOutputProcessTypes p

and collectPatternTypes: pattern -> unit = function
  | PatVar b -> funTypes := (b.sname, convertFunType ([], b.btype)) :: !funTypes 
  | PatTuple (_, pats) -> iter collectPatternTypes pats
  | PatEqual _ -> ()

let collectConstTypes : unit -> unit = fun () ->
  let collect : string -> unit = fun c ->
    funTypes := (c, ([], mstring)) :: !funTypes
  in
  List.iter collect !constants

let collectFunTypes : piFunInfo list -> unit = fun fs ->
  let collect : piFunInfo -> unit = fun (fname, _) ->
    let arity = assoc fname !arities in
    funTypes := (fname, (replicate arity mstring, mstring)) :: !funTypes
  in
  List.iter collect fs

let collectTypes : unit -> unit = fun () ->
  let (_, _, _, _, queries, _, q) = read_file !templateFile in
  collectEnvTypes ();
  collectInputProcessTypes q;
  collectConstTypes ()
  (* collectFunTypes !concats;
  collectFunTypes !parsers; *)


(** {2 Checking types} *)
(*****************************)


let subtype: imltype -> imltype -> bool = fun t t' ->
  match t, t' with
    | _, MStringBot -> true
    | MStringBot, _ -> false
    | _, MString _  -> true
    | MString _, _  -> false 
    | _, Named _    -> t = t'
	  | Named _, _    -> false
	  | Bounded (i, _), Bounded (i', _) -> i <= i'
	  | Fixed (i, _), Bounded (i', _)   -> i <= i'
	  | Fixed (i, _), Fixed (i', _)     -> i = i'
	  | _ -> false

let meet : imltype -> imltype -> imltype = fun t t' ->
  if subtype t t' then t
  else if subtype t' t then t'
  else fail ("cannot compute intersection of types " ^ showType t ^ " and " ^ showType t')


let checkType : pCtx -> exp -> exp = fun ctx ->
  let mkTypeFact : exp -> imltype -> exp = fun e -> function
    | MStringBot -> tt
    | MString _  -> tt
    | Fixed (n, _)    -> eq [mkInt n; getLen e]
    | Bounded (n, _)  -> grEq (mkInt n) (getLen e)
    | Named n         -> unknown () (* fail ("checkType: generic named type: e = " ^ dump e ^ ", t = " ^ n) *)
  in

  let proveType: ftype -> exp -> unit = function (argTypes, resType) -> function
    | Sym ((f, _), es, _, _) as e when isFormatFun f || f = "read" ->

      let args = mkFormalArgs (length es) in
      
      (* replace es with formal argument expressions and expand all format function definitions *)
      let rewrite: exp -> exp = fun e -> expandFormatFuns (substMany es args e) in 

      let eDef = rewrite e in
      let ctx = map rewrite ctx in

      (*
      debug ("typecheck: e_def = " ^ dump e_def);
      debug ("typecheck: context = " ^ dumpList ctx);
      *)

      let argFacts = map2 mkTypeFact args argTypes in
      let resFact = mkTypeFact eDef resType in
      
      debug ("proving type " ^ showFtype f (argTypes, resType));
      solver_debug := true;
      resetFacts ();
      iter addFact argFacts;
      iter addFact ctx;
      if not (isTrue resFact) then
        fail ("typecheck: cannot prove type " ^ showFtype f (argTypes, resType));
      solver_debug := false;
   
    | _ -> fail "proveType: unexpected expression"
  in

  let cast: imltype -> imltype -> exp -> exp = fun t t_e e ->
      if t = t_e then e
    else if subtype t_e t then
      mkCast t_e t e
    (*
       Inverse casts should not be allowed, functions should not be forced to check their argument type.
      (* sometimes unequal types may be equivalent (like mstring with alias), so we need to orient them somehow *)
    else if subtype t_e t && t_e < t then
      mkCast t_e t e
    else if subtype t t_e && t < t_e then
      (* 
        We don't want cast functions to be pattern-matched, because it makes writing
        some rewrite rules more difficult (like in RPC-enc). 
      *)
      (* mkInverseCast t t_e e *)
      mkCast t_e t e
    *)
    else 
      fail ("typecheck: cannot introduce a typecast for " ^ dump e ^ " from " ^ showType t_e ^ " to " ^ showType t)
  in
    
  let rec check: imltype -> exp -> exp = fun t e ->
    debug ("\n==============================\nchecking type of " ^ dump e);
    match e with
    | Sym (("If", _), [e'], _, _) -> replaceArgs [check boolType e'] e
    | Sym ((("write"), _), _, _, _) when isArithmeticWrite e -> e
      (* being liberal with what we write *)
    | Sym ((("write"), _), [e'], _, _) -> replaceArgs [check (getType e') e'] e (* (map (check mstring) es) *) 
      (* for some reason CV considers events to be of bool type *)
    | Sym ((("event"), _), es, _, _) -> replaceArgs (map (check boolType) es) e
    
    | Sym (("IfEq", _), [e1; e2], _, _) ->
      let t1 = getType e1 in
      let t2 = getType e2 in
      let t = meet t1 t2 in
      replaceArgs [check t e1; check t e2] e
      
    | Sym ((("new" | "newT" | "var" | "const"), _), _, _, _) -> 
      let t_e = getType e in
      cast t t_e e

    | Sym (("read", _), _, _, _) when mem_assoc (expId e) !readTypes -> 
      debug ("has type: " ^ dump e);
      let t_e = getType e in
      debug ("the type is " ^ showType t_e);      
      cast t t_e e
                  
    | Sym (("read", _), _, _, _) -> 
      debug ("checking typeless: " ^ dump e);
      proveType ([], t) e; 
      debug ("type proved: " ^ showType t);
      readTypes := (expId e, t) :: !readTypes;
      e
                  
    | Sym ((f, _), es, _, _) when mem_assoc f !funTypes ->
      let (argTypes, t_e) = assoc f !funTypes in
            
      if isFormatFun f then proveType (argTypes, t_e) e;

      let es' = 
        try map2 check argTypes es 
        with Invalid_argument _ -> fail ("wrong number of arguments in " ^ dump e);
      in
      let e' = replaceArgs es' e in

      cast t t_e e'

    | Sym ((f, _), es, _, _) ->
      let (argTypes, t_e) = (map getType es, t) in
      
      if isFormatFun f then proveType (argTypes, t_e) e;

      funTypes := (f, (argTypes, t_e)) :: !funTypes;
      let es' = 
        try map2 check argTypes es 
        with Invalid_argument _ -> fail ("wrong number of arguments in " ^ dump e);
      in
      replaceArgs es' e
      
    | e -> fail ("typecheck: unexpected expression: " ^ dump e)
  in
  
  check mstring
  (* List.map (visitAllSubexp check) *) (* visitExpBodyPost *) 


let typecheck: exp list -> exp list = mapWithCtx checkType


(*************************************************)
(** {1 Use pattern matching where possible} *)
(*************************************************)

(**
    Using pattern matching is only possible when the encoder is injective, and we actually don't check that,
    as this is not necessarily implied by having a safe parser.
    We rely on the fact that CV will reject the pattern matching if encoder is not marked as [compos].
*)

type cvprocess = exp list * pMeta

(** Safe inverses fail on anything outside the range of the function. *)
let isSafeInverse: piFun -> bool = fun f ->
  isSafeParser f ||
  match Str.split (Str.regexp "_") f with
    | "inverse" :: _ -> true
    | _ -> false 

let inverseOf: piFun -> piFun * int = fun f ->
  try List.assoc f !safeParsers with
  Not_found -> (Str.replace_first (Str.regexp "inverse_") "" f, 0)

let usePatterns: cvprocess -> cvprocess = function (p, meta) ->
  
  (* Pairs (c, e) for which we have inserted 
     let c(x_1, ..., x_n) = e in *)
  let matched: (piFun * exp) list ref = ref [] in

  let isMatched : (piFun * exp) -> bool = fun (c, e) ->
    exists (fun (c', e') -> c = c' && equal e e') !matched
  in

  (* return the variable corresponding to p_i(e) where p_i is the ith inverse of c *)
  let mkPatVar: piFun -> exp -> int -> exp = fun c e i ->
	  let p_e = Sym (("inverse_" ^ c, Prefix), [e; mkInt i], Unknown, freshDet ()) in
    
    (* debug ("making a pattern variable for " ^ dump p_e); *)
    
	  let m = getMeta p_e in
	  m.defined <- true;
	  mkVar (giveName p_e) p_e
  in
  
  let mkPatternMatch: piFun * exp -> exp list = fun (c, e) ->
    if isMatched (c, e) then []
    else
    begin
      
      (* debug ("making a pattern match for c = " ^ c ^ ", e = " ^ dump e); *)
      
	    let arity = 
        try List.assoc c !arities
        with Not_found -> 1 in
	    let vars = List.map (mkPatVar c e) (0 -- (arity - 1)) in
	    let pat = Sym ((c, Prefix), vars, Unknown, NoTag) in 
	    matched := (c, e) :: !matched;
	    [mkLet pat e]
    end
  in

  (* collect all (c, e), s.t. the expression contains p(e) and p is safe on c *)
  let collectMatches : exp -> (piFun * exp) list = fun e ->
    
    let matches: (piFun * exp) list ref = ref [] in 
    
    let collect : exp -> unit = function
      | Sym ((p, _), [e], _, _) when isSafeInverse p ->
        let (c, _) = inverseOf p in
        matches := (c, e) :: !matches;
      | _ -> ()
    in
    visitAllSubexp collect e; !matches
  in

  (* for every expression that contains p(e) with safe p insert let c(...) = e at the front *)
  let rec insert : exp list -> exp list = function
    | e :: es ->
      let matches = collectMatches e in
      let pats = map mkPatternMatch matches in
      List.concat pats @ [e] @ insert es 
    | [] -> []
  in
  
  let replace: exp -> exp = fun e -> match e with
    | Sym ((p, _), [e], _, _) when isSafeInverse p ->
      let (c, i) = inverseOf p in
      mkPatVar c e i
    | e -> e
  in
  
  (* remove let x = p(e) in, replace all p(e) with safe p by variables defined in pattern decompositions *)
  (* pre-order is important because otherwise we might replace e before replacing p(e) and that leads to naming inconsistencies *)
  let cleanup: exp list -> exp list = map (visitExpPre replace) in

  setActiveMeta meta;
  let p' = cleanup (insert p) in 
  p', getActiveMeta ()

(*************************************************)
(** {1 Regularity Properties} *)
(*************************************************)

let zeroTypes: unit -> imltype list = fun () ->

  let zts: imltype list ref = ref [] in
  
  let addType: (string * ftype) -> unit = fun (c, (ts, t)) ->
    if isConcat c then zts := t :: ts @ !zts;
  in 
  
  iter addType !funTypes;
  nub !zts

let zeroFunName: imltype -> string = fun t -> "Z" ^ showType t

(*************************************************)
(** {1 Input and Output Merging} *)
(*************************************************)

let mergeInOut : exp list -> exp list = fun es ->

  (* let dummy = mkVar "dummy" (concat []) in *) 

  let rec mergeIn : exp list -> exp list -> exp list = fun vs es -> match (vs, es) with
    | vs, Sym (("read", _), [v], _, _) :: es' -> mergeIn (v :: vs) es'
    | [], e :: es' -> e :: mergeIn [] es'
    | vs, ((Sym (("write", _), _, _, _)) as e) :: es' ->
      Sym (("read", Prefix), vs, Unknown, freshNondet ()) :: e :: mergeIn [] es' 
    | vs, e :: es' -> e :: mergeIn vs es'
    | [], [] -> 
      [Sym (("read", Prefix), [], Unknown, freshNondet ())] 
    | vs, [] -> 
      [Sym (("read", Prefix), vs, Unknown, freshNondet ())]
  in

  let rec mergeOut : exp list -> exp list -> exp list = fun vs es -> match (vs, es) with
    | vs, Sym (("write", _), [v], _, _) :: es' -> mergeOut (v :: vs) es'
    | [], e :: es' -> e :: mergeOut [] es'
    | vs, ((Sym (("read", _), _, _, _)) as e) :: es' ->
      Sym (("write", Prefix), vs, Unknown, freshNondet ()) :: e :: mergeOut [] es' 
    | vs, e :: es' -> e :: mergeOut vs es'
    | [], [] -> 
      [Sym (("yield", Prefix), [], Unknown, freshNondet ())] 
    | vs, [] -> 
      [Sym (("write", Prefix), vs, Unknown, freshNondet ())]
  in
      
  List.rev (mergeIn [] (List.rev (mergeOut [] es)))

(*************************************************)
(** {1 CV Output} *)
(*************************************************)
  
let showCVExp : exp -> string = fun e ->

  let rec showExpBody : exp -> string = function 
    | Sym (("const", _), [String c], _, _) -> c
    | Sym (("var", _), [String s], _, _) -> s
    | Sym ((s, _), es, len, id) ->
      s ^ "(" ^ String.concat ", " (map showExp es) ^ ")"
    | e -> "unexpected{" ^ dump e ^ "}"

  and showInVar : imltype -> exp -> string = fun t -> function
	  | Sym (("var", _), [String name], l, _) -> name ^ ": " ^ showType t
	  | _ -> failwith "showInVar: not a var"

  and showExp : exp -> string = function e ->
    (* debug ("showing " ^ dump e); *)
    match e with
	    | Sym (("read", _), vs, _, _) -> 
	      "in(c_in, (" ^ String.concat ", " (map (fun v -> showInVar (getType v) v) vs) ^ "));";
	
	    | Sym (("new", _), [v], l, _) -> 
        let t = lenToType l in
	      "new " ^ showInVar t v ^ ";";

      | Sym (("newT", _), [v; String t], l, _) -> 
        "new " ^ showInVar (parseType t) v ^ ";";
    	
	    | Sym (("write", _), es, _, _) -> 
	      "out(c_out, (" ^ String.concat ", " (map showIExp es) ^ "));";

      | Sym (("yield", _), [], _, _) -> 
        "yield.";
                                                                                                                                                                                	                                                                                       
	    | Sym ((("IfEq"), _), [e1; e2], _, _) ->
	      "if " ^ showExp e1 ^ " = " ^ showExp e2 ^ " then "

	    | Sym ((("If"), _), [e], _, _) ->
	      "if " ^ showExp e ^ " then "
    	
	    | Sym ((("event"), _), [e'], _, _) ->
	      "event " ^ showExp e' ^ ";"
	
	    | Sym ((("let"), _), [pat; rhs], _, _) ->
	      "let " ^ showExp pat ^ " = " ^ showExp rhs ^ " in"
	
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

let showCVProcess : cvprocess -> string = function (es, (m, t)) ->
  meta := m;
  nameTags := t; 
  (* let es = splitByType es in *)
  (* let es = elimCommonSubs es in *)
  let zero = 
    if es = [] then " 0 .\n" else
    match last es with
      | Sym (("yield", _), [], _, _) -> "\n"
      | _ -> " 0 .\n"
  in
  let result = String.concat "\n" (map showCVExp es) ^ zero in
  result

let print_indent s = print_endline ("  " ^ s)

let writeCV : cvprocess -> cvprocess -> unit = fun client server ->
  
  let printConcatRaw: piFun -> bool -> unit = fun name isInjective -> 
    let compos = if isInjective then " [compos]." else "." in
    print_endline ("fun " ^ showFtype name (assoc name !funTypes) ^ compos)
  in
    
  let printConcat : piFunInfo -> unit = function (name, _) as c ->
    debug ("printing " ^ name);
    print_endline ("(* " ^ showFun c ^ " *)");
    printConcatRaw name (isInjectiveConcat true c);
    print_endline ""
  in

  let printParser : piFunInfo -> unit = function
    | (name, Basic _) as p -> 
      print_endline ("(* " ^ showFun p ^ " *)");
      print_endline ("fun " ^ showFtype name (assoc name !funTypes) ^ ".");
      print_endline "";
      (* print_endline ("fun " ^ name ^ "(mstring): mstring.") *)
    | _ -> ()
  in
  
	let printCast: imltype * imltype -> unit = fun (t, t') ->
	  print_endline ("fun " ^ castFun t t' ^ "(" ^ showType t ^ "): " ^ showType t' ^ " [compos].")
  in
  
  let printCastEq: imltype * imltype -> unit = fun (t, t') ->
    if List.mem (t', t) !casts then 
    begin
      (* this is a cast between two equal (aliased) types *)
      print_endline ("forall x: " ^ showType t ^ ";");
      print_endline ("  " ^ castFun t' t ^ "(" ^ castFun t t' ^ "(x)) = x.")
    end
  in
  
  let printConstant : string -> unit = fun s ->
    let e = try assoc s !constDefs with Not_found -> fail "impossible: printConstant" in
    print_endline ("(* " ^ dump e ^ " *)");
    print_endline ("const " ^ s ^ ": mstring.") 
  in

  let printDisjoint: piFun * piFun -> unit = fun (c1, c2) ->
    debug ("printing" ^ c1 ^ " " ^ c2);
    try
    begin    
	    let id = ref 0 in
	
	    let formalArg: imltype -> string = fun _ -> id := !id + 1; "var" ^ string_of_int !id in
	    let showArg: string -> imltype -> string = fun v t -> v ^ ": " ^ showType t in
	
	    let (argTypes1, t1) = assoc c1 !funTypes in
	    let (argTypes2, t2) = assoc c2 !funTypes in
	
	    if t1 = t2 then
	    begin
		    let args1 = map formalArg argTypes1 in
		    let args2 = map formalArg argTypes2 in
		    
		    print_endline ("forall " ^ String.concat ", " (map2 showArg args1 argTypes1) ^ ", " ^ 
		                               String.concat ", " (map2 showArg args2 argTypes2) ^ ";");
		    print_endline ("  " ^ c1 ^ "(" ^ String.concat ", " args1 ^ ") <> " ^ c2 ^ "(" ^ String.concat ", " args2 ^ ").");
	    end
    end with Not_found -> ()
  in

  let printZeroFun: imltype -> unit = fun t ->
    let tname = showType t in
    print_endline ("fun " ^ zeroFunName t ^ "(" ^ tname ^ "): " ^ tname ^ ".")
  in

  let printConcatRegular: piFun -> unit = fun c ->
    let (ts, t) = assoc c !funTypes in
    
    let zc = "Z" ^ c in
    funTypes := (zc, (ts, t)) :: !funTypes;
    printConcatRaw zc false;
    
    let id = ref 0 in

    let formalArg: imltype -> string = fun _ -> id := !id + 1; "var" ^ string_of_int !id in
    let showArg: string -> imltype -> string = fun v t -> v ^ ": " ^ showType t in
    let applyZero: string -> imltype -> string  = fun v t -> zeroFunName t ^ "(" ^ v ^ ")" in

    let args = map formalArg ts in

    print_endline ("forall " ^ String.concat ", " (map2 showArg args ts) ^ ";");
    print_endline ("  " ^ zeroFunName t ^ "(" ^ c  ^ "(" ^ String.concat ", " args ^ ")) = " 
                    ^ zc ^ "(" ^ String.concat ", " (map2 applyZero args ts) ^ ").");
  in        

  let clientProc = showCVProcess client in
  let serverProc = showCVProcess server in

  (*
  print_endline "channel c_in, c_out.";
  print_endline "type mstring.";
  *)

  iter print_endline !crypto;

  print_endline "\n(*************************** \n Constants \n***************************)\n";
  iter printConstant !constants;

  print_endline "\n(*************************** \n  Formatting Functions \n***************************)\n";
  iter printConcat !concats;
  iter printParser !parsers;
  print_endline "";
  iter printDisjoint !disjointPairs;

  print_endline "\n(*************************** \n  Zero Functions \n***************************)\n";
  iter printZeroFun (zeroTypes ()); 

  print_endline "\n(*************************** \n  Length-Regularity \n***************************)\n";
  iter printConcatRegular (assoc_keys !concats);
                  
  print_endline "\n(*************************** \n  Typecasting \n***************************)\n";
  iter printCast !casts;
  iter printCastEq !casts; 
  
  print_endline "";

  iter print_endline !crypto2;
  iter print_endline !query;
  
  print_endline "\n(*************************** \n  Model \n***************************)\n";
  print_endline "let A = ";
  print_endline clientProc;
  print_endline "let B = ";
  print_endline serverProc;

  iter print_endline !envp  
  
  (*
  print_endline "process !";
  (* iter printKey !keys; *)
  print_indent "new keyAB;";
  print_indent "(!A | !B)"
  *)

(*************************************************)
(** {1 Main} *)
(*************************************************)

;;
begin
  inlineAll := false;

  (*
  let server = input_value (open_in_bin Sys.argv.(1)) in
  let client = input_value (open_in_bin Sys.argv.(2)) in
  *)
  let (client, server) = rawIn (open_in_bin Sys.argv.(1)) in

  verbose := true;
  debugEnabled := true;

  if !verbose then prerr_endline "\nraw IML:";
  if !verbose then prerr_endline (showSimpleIMLRaw client);
  if !verbose then prerr_endline (showSimpleIMLRaw server);

  let server = procAndFilter server in
  let client = procAndFilter client in

  if !verbose then prerr_endline "\nfiltered IML:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let (client, clientConcats) = extractConcats client in
  let (server, serverConcats) = extractConcats server in
  let allConcats = clientConcats @ serverConcats in

  if !verbose then showFuns allConcats;
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  (* 
    Don't try splitting concats to achieve full disjointness.
    First, it is not always possible (metering).
    Second, processes are easier to typecheck without nested concats.
  *)
  insertConcats ~needDisjoint:false allConcats;

  if !verbose then showFuns !concats;

  let client = rewriteConcats client in
  let server = rewriteConcats server in

  let client = extractConstConcats client in
  let server = extractConstConcats server in

  if !verbose then prerr_endline "\nIML after constant concats extraction:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  cleanupConcats (client @ server);
      
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let client = extractParsers client in
  let server = extractParsers server in

  if !verbose then prerr_endline "\nafter parsing extraction:";
  if !verbose then showFuns !parsers;
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  computeParsingRules !parsers;

  if !verbose then prerr_endline "\nafter parsing extraction (reminder):";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  computeSafeParsers client;
  computeSafeParsers server;

  if !verbose then prerr_endline "\nafter parsing extraction (reminder):";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  (* Typechecking *)
  Cryptoverif.Settings.lib_name := Sys.argv.(2);
  templateFile := Sys.argv.(3);
  readTemplate (open_in !templateFile);
  collectTypes ();
  dumpTypes ();
  let client = typecheck client in
  let server = typecheck server in
  if !verbose then prerr_endline "\nIML after typechecking:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let client = postprocess client in
  let server = postprocess server in
  if !verbose then prerr_endline "\npostprocessed IML:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let client = extractConstants client in
  let server = extractConstants server in

  if !verbose then prerr_endline "\nIML after constant extraction:";
  if !verbose then prerr_endline (showSimpleIML client);
  if !verbose then prerr_endline (showSimpleIML server);

  let (client, clientMeta) = usePatterns (client, emptyMeta ()) in
  let (server, serverMeta) = usePatterns (server, emptyMeta ()) in

  if !verbose then prerr_endline "\nafter inserting pattern matching:\n";
  if !verbose then prerr_endline (showStructuredIML client clientMeta);
  if !verbose then prerr_endline (showStructuredIML server serverMeta);

  cleanupParsers (client @ server);

  let (client, clientMeta) = splitByType (client, clientMeta) in
  let (server, serverMeta) = splitByType (server, serverMeta) in
  
  if !verbose then prerr_endline "\nafter splitting expressions:\n";
  if !verbose then prerr_endline (showStructuredIML client clientMeta);
  if !verbose then prerr_endline (showStructuredIML server serverMeta);

  (*
  if !verbose then prerr_endline "\nafter splitting expressions twice:\n";
  if !verbose then prerr_endline (showIML (splitByType client));
  if !verbose then prerr_endline (showIML (splitByType server));
  *)

  let client = mergeInOut client in
  let server = mergeInOut server in

  if !verbose then prerr_endline "\nafter merging inputs and outputs:";
  if !verbose then prerr_endline (showStructuredIML client clientMeta);
  if !verbose then prerr_endline (showStructuredIML server serverMeta);

  writeCV (client, clientMeta) (server, serverMeta);
end;

