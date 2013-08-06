
open Common

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Exp.T
open Iml.Pat.T
open Iml.Stmt.T

module E = Iml.Exp
module S = Solver

open Transform_imltrace
open Transform

open Printf

type cvfact = CVFact.t

module Template: sig

  type t 
  
  val crypto: t -> string list
  val crypto2: t -> string list
  val query: t -> string list
  val envp: t -> string list
  val typehints: t -> string list
  val model: t -> string list

  val readFile: cv_lib_name:string -> name:string -> t

  val collectTypes: t -> Typing.typeCtx * Typing.funTypeCtx
  
end = struct

  module CV = Cryptoverif

  open CV.Types
  open CV.Syntax
  open CV.Stringmap
  
  type t = {
    crypto: string list;
    (** Printed after the automatically generated facts *)
    crypto2: string list;
    query : string list;
    envp: string list;
    (**
      These are used for typechecking, but are not repeated in the actual model output.
    *)
    typehints: string list;
    (**
      This part is dropped.
    *)
    model: string list; 
    q: CV.Types.inputprocess;
    env: CV.Types.env_entry CV.Stringmap.StringMap.t }
    
  let crypto t = t.crypto
  let crypto2 t = t.crypto2
  let query t = t.query
  let envp t = t.envp
  let typehints t = t.typehints
  let model t = t.model
 

  let readFile ~cv_lib_name ~name = 
  
    let crypto = ref [] in
    let crypto2 = ref [] in
    let query = ref [] in
    let envp = ref [] in
    let typehints = ref [] in
    let model = ref [] in
  
    let rec splitTemplate: string list ref -> string list -> unit = fun dest -> function
      | l1 :: l2 :: ls' when trim l2 = "<Environment>" -> splitTemplate envp (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Query>" -> splitTemplate query (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Model>" -> splitTemplate model (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Type hints>" -> splitTemplate typehints (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Crypto2>" -> splitTemplate crypto2 (((l1 ^ "\n" ^ l2) :: ls'))
      | l :: ls'  -> dest := !dest @ [l]; splitTemplate dest ls'   
      | [] -> ()  
    in
  
    let c = open_in name in
    splitTemplate crypto (readFile c);
    Cryptoverif.Settings.lib_name := cv_lib_name;
    let (_, _, _, _, _, _, q) = read_file name in
    {crypto = !crypto; crypto2 = !crypto2; query = !query; envp = !envp; typehints = !typehints; model = !model; 
     q; env = !CV.Stringmap.env }
  
  
  let collectTypes t =
  
    let types = ref [] in
    let funTypes = ref [] in
  
    let convertFunType: typet list * typet -> FunType.t = fun (ts, t) ->
      List.map (fun t -> Type.ofString t.tname) ts, Type.ofString t.tname 
    in
  
    let collectEnvTypes env =
    
      let doEntry : string -> env_entry -> unit = fun k -> function
        | EFunc f ->
          (* Constants are encoded as functions with no arguments, but we want to treat them as variables *)
          let (ts, t) = convertFunType f.f_type in
          if ts = [] then
            types := (f.f_name, t) :: !types
          else
            funTypes := (f.f_name, (ts, t)) :: !funTypes 
        | EEvent f ->
          (* for some reason it adds an extra bitstring parameter in front of the ones I define *)
          let (atypes, rtype) = f.f_type in
          funTypes := (f.f_name, convertFunType (List.tl atypes, rtype)) :: !funTypes
        | EVar b -> types := (b.sname, Type.ofString b.btype.tname) :: !types
        | _ -> ()
      in
    StringMap.iter doEntry env
    in
    
    let rec collectInputProcessTypes : inputprocess -> unit = fun q -> 
    
      let rec collectPattern : pattern -> unit = function
        | PatVar b -> types := (b.sname, Type.ofString b.btype.tname) :: !types
        | PatTuple (_, pats) -> List.iter collectPattern pats 
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
            types  := (b.sname, Type.ofString b.btype.tname) :: !types;
            collectOutputProcessTypes p
          | Test (_, p, p') -> collectOutputProcessTypes p; collectOutputProcessTypes p'
          | Find _ -> fail "collectTypes: unexpected find construct"
          | Output (_, _, q) -> collectInputProcessTypes q
          | Let (pat, _, p, p') ->
            collectPatternTypes pat;  
            collectOutputProcessTypes p; collectOutputProcessTypes p'
          | EventP (_, p) -> collectOutputProcessTypes p
  
    and collectPatternTypes: pattern -> unit = function
      | PatVar b -> types := (b.sname, Type.ofString b.btype.tname) :: !types 
      | PatTuple (_, pats) -> List.iter collectPatternTypes pats
      | PatEqual _ -> ()
    in
        
    collectEnvTypes t.env;
    collectInputProcessTypes t.q;
    Var.Map.ofList !types,
    Sym.Map.ofList (List.map (fun (f, (ts, t)) -> (Sym.T.Fun (f, List.length ts), (ts, t))) !funTypes)
end

(********************************************************)
(** {1 Replace inverse functions by pattern matching} *)
(********************************************************)

let isInverse f = 
  match Str.split (Str.regexp "_") f with
    | "inverse" :: _ -> true
    | _ -> false 

let inverseOf f = Fun (Str.replace_first (Str.regexp "inverse_") "" f, 1)

let rec checkNoInverse e = 
  match e with
  | Sym (Fun (f, _), _) when isInverse f -> 
    fail "inverse function not directly in let-bindig: %s" (E.toString e)
  | e -> List.iter checkNoInverse (E.children e)

let rec matchInverse p =
  match p with
    | Let (VPat v, Sym (Fun (f, _), [e])) :: p when isInverse f ->
      Let (FPat (inverseOf f, [VPat v]), e) :: matchInverse p

    | s :: p -> 
      List.iter checkNoInverse (Stmt.children s);
      s :: matchInverse p
          
    | [] -> []


(*************************************************)
(** {1 Use pattern matching for safe parsing} *)
(*************************************************)

let mkPattern f_c arity v i =
  let pat = replicate arity Underscore in
  FPat (f_c, set_element i (VPat v) pat) 
  

(**
  Expects formatting-normal form.
*)
let matchSafeParsers (parsers: symDefs) (concats: symDefs) parsingEqs facts p =

  let rec doMatch facts = function 
    | (Let (VPat v, Sym (f_p, [e])) as s) :: p when Sym.Map.mem f_p parsers ->
      begin match safeParse concats parsingEqs facts f_p e with
        | Some (f_c, i) -> 
          Let (mkPattern f_c (Sym.arity f_c) v i, e) :: doMatch facts p
        | None -> 
          s :: doMatch facts p
      end

    | AuxTest e :: p -> 
      AuxTest e :: doMatch (facts @ [e]) p
      
    | s :: p -> s :: doMatch facts p
                              
    | [] -> []
  in
  doMatch facts p


let rec mergePatterns p =

  let merge vpat vpat' = 
    match vpat, vpat' with
      | VPat v, _ | _, VPat v  -> VPat v
      | Underscore, Underscore -> Underscore
      | _ -> failwith "mergePatterns: impossible"
  in

  let rec mergePattern = List.map2 merge in
  
  let rec matchVars pat pat' =
    match pat, pat' with
      | VPat v :: pat, VPat v' :: pat' -> (v', Var v) :: matchVars pat pat'
      | _ :: pat, _ :: pat' -> matchVars pat pat'
      | [], [] -> []
      | _ -> failwith "matchVars: impossible"
  in

  let rec collectPattern f pat e p = 
    match p with
    | Let (FPat (f', pat'), e') :: p when f = f' && e = e' ->
      let pat = mergePattern pat pat' in
      let vs, vs' = List.split (matchVars pat pat') in 
      let p = Iml.subst vs vs' p in
      collectPattern f pat e p
      
    | s :: p -> 
      let p, pat = collectPattern f pat e p in
      s :: p, pat
     
    | [] -> [], pat
  in

  match p with 
    | Let (FPat (f, pat), e) :: p ->
      let p, pat = collectPattern f pat e p in
      Let (FPat (f, pat), e) :: mergePatterns p
      
    | s :: p -> s :: mergePatterns p
      
    | [] -> [] 

(*************************************************)
(** {1 Regularity Properties} *)
(*************************************************)

let zeroFunSym t = Fun ("Z" ^ Type.toString t, 1) 
let zeroFunPrimeSym t = Fun ("Z" ^ Type.toString t ^ "_prime", 1) 
let zeroSym t = Const ("zero_" ^ Type.toString t)
      
(**
  Return the zero equations, zero function definitions and types 
  (including definitions and types for zero constants of fixed types).
  
  Generate the following equations:
  
    - for each conc: T1 x ... x Tn -> T
      ZT(conc(x1, ..., xn)) = ZT'(conc(ZT1(x1), ..., ZTn(xn)))
      
    - for each cast_T1_T2:
      ZT2(cast_T1_T2(x)) = ZT2'(cast_T1_T2(ZT1(x)))
      
    - for each fixed type T that occurs anywhere in argument types in funTypes:
      ZT(x) = ZeroT
*)
let zeroFacts (concats: symDefs) 
              (casts: (Type.t * Type.t) list) 
              (funTypes: Typing.funTypeCtx): cvfact list * symDefs * Typing.funTypeCtx = 
              
  (* Types for which we need to generate ZT, ZT', and possibly ZeroT *)
  let zts: imltype list ref = ref [] in
  
  let zeroFun t =
    zts := t :: !zts;
    zeroFunSym t  
  in

  (* Assume that zeroFun will be called for all of these, so no need to add to zts. *)
  let zeroFunPrime t = zeroFunPrimeSym t in
  
  let zeroOf e t = Sym (zeroFun t, [e]) in
  
  (* Suitable for generating symDefs and Typing.funTypeCtx *)
  let zFunInfo t = 
    let zt = zeroFunSym t in
    let zt' = zeroFunPrimeSym t in
    let zero_t = zeroSym t in
    [(zt,  Unknown), (zt,  ([t], t)); 
     (zt', Unknown), (zt', ([t], t));
     (zero_t, Unknown), (zero_t, ([], t))]
  in    
  
  let concatFact c = 
    let ts, t = Sym.Map.find c funTypes in
    let args = mkFormalArgs (Sym.arity c) |> List.map E.var in
    let zt = zeroFun t in
    let zt' = zeroFunPrime t in
    S.eqBitstring [Sym (zt, [Sym (c, args)]); 
                   Sym (zt', [Sym (c, List.map2 zeroOf args ts)])]
  in
  
  let castFact (t1, t2) =
    let sym = Cast (t1, t2) in
    let x = Var "x" in
    let zt2 = zeroFun t2 in
    let zt2' = zeroFunPrime t2 in
    S.eqBitstring [Sym (zt2,  [Sym (sym, [x])]); 
                   Sym (zt2', [Sym (sym, [zeroOf x t1])])]
  in 
  
  let constFact t =
    let zt = zeroFun t in
    let zero_t = Sym (zeroSym t, []) in 
    let x = Var "x" in 
    S.eqBitstring [Sym (zt, [x]); zero_t]
  in
  
  (*
    Remove information for symbols that are already present in the template 
    (such as the zero function in the definition of the encryption).
  *)
  let cleanup bindings = 
    List.filter (fun (sym, _) -> not (Sym.Map.mem sym funTypes)) bindings
  in
  
  let concat_facts = List.map concatFact (Sym.Map.keys concats) in
  let cast_facts = List.map castFact casts in
  let fixed_types =
    Sym.Map.values funTypes
    |> List2.concat_map (fun (ts, _) -> ts) 
    |> List.filter (function Fixed _ -> true | _ -> false) 
    |> List2.nub
  in
  let const_facts = List.map constFact fixed_types in
  let z_defs, z_types = List2.concat_map zFunInfo (List2.nub !zts) |> List.split in
  let z_defs = cleanup z_defs |> Sym.Map.ofList in
  let z_types = cleanup z_types |> Sym.Map.ofList in
  let facts = List.map (CVFact.make (Sym.Map.disjointUnion [funTypes; z_types])) 
                       (concat_facts @ cast_facts @ const_facts) 
  in
  facts, z_defs, z_types

(********************************************************)
(** {1 Auxiliary Test Properties} *)
(********************************************************)

let prime = function
  | Fun (s, n) -> Fun (s ^ "_prime", n) 
  | sym -> fail "auxiliaryFacts: impossible auxiliary symbol: %s" (Sym.toString sym)
    
let addAuxiliaryPrimed auxiliary funTypes = 
  let auxiliary_primed = 
    Sym.Map.bindings auxiliary
    |> List.map (fun (sym, def) -> (prime sym, def))
    |> Sym.Map.ofList
  in 
  let types_primed =
    Sym.Map.bindings auxiliary
    |> List.map (fun (sym, _) -> (prime sym, Sym.Map.find sym funTypes))
    |> Sym.Map.ofList
  in
  Sym.Map.disjointUnion [auxiliary; auxiliary_primed], Sym.Map.disjointUnion [funTypes; types_primed] 
    
(*
  There are two ways to check 
    len(x) = len(y) /\ def[x/arg] => def[y/arg].
  
  The first way is to do length substitutions and then check syntactic equality. 
  One needs to expand lengths because of things like
    !(castToInt[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + castToInt[false,4,false,8](len55)))     
  
  The other way is to use the solver directly, but then you need to show overflow safety as well.
  When formalising, you need to replace auxiliary facts by hardened facts that check overflow safety.
  
  The second option bis conceptually simpler, but less efficient.
  Another problem with the second option is that it is tricky to tell the solver to assume overflow
  safety for an expression. One cannot just extract the overflow safety fact, because that itself
  may not be overflow safe. For these reasons I'm using the first option now.
*)
let auxiliaryFacts (concats: symDefs) (auxiliary: symDefs) (funTypes: Typing.funTypeCtx): cvfact list =

  (* facts for a single auxiliary test *)
  let facts sym def argTypes = 

    let num_args = List.length argTypes in
    
    let zeroOf v t = Sym (zeroFunSym t, [Var v]) in
  
    let rec replaceLen v = function
      | Len (Var v') when v' = v -> Var (Var.fresh "len") 
      | e -> E.descend (replaceLen v) e
    in

    let rec expandLens = function
      | Len (Concat es) -> 
        List.map E.len es |> E.sum |> expandLens
      | e -> E.descend expandLens e
    in

    let canErase arg =
      let x = Var (Var.fresh "x") in
      let y = Var (Var.fresh "y") in
      let def = replaceLen arg def in
      let def_x = E.subst [arg] [x] def in
      let def_y = E.subst [arg] [y] def in
      debug "canErase: comparing \n%s and \n%s" (E.toString def_x) (E.toString def_y);
      def_x = def_y
    in
  
    (* FIXME: looks like t isn't being used any more *)
    let concatPairs arg t =
      let pair c = 
        match Sym.Map.maybe_find c funTypes with
          | Some (ts, t') (* when t = t' *) -> 
            let c_def = Sym.Map.find c concats in

            (* Rename args of c_def to avoid collision with args of def. *)
            let c_args = List.map (fun _ -> Var.fresh "c_arg") (1 -- (Sym.arity c)) in
            let c_def = E.substV (mkFormalArgs (Sym.arity c)) c_args c_def in 
            
            let def = 
              E.subst [arg] [c_def] def 
                (* We may be substituting an encoder inside a parser, so we need to simplify. *)
              |> silent Simplify.deepSimplify
                (* Deal with stuff like 
                   !(castToInt[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + castToInt[false,4,false,8](len55))) 
                *)
              |> expandLens 
                (* Replace all argument lengths by fresh variables *)
              |> List.fold_right replaceLen c_args 
            in
                
            let xs = List.map (fun _ -> Var.fresh "x") (1 -- (Sym.arity c)) in
            let ys = List.map (fun _ -> Var.fresh "y") (1 -- (Sym.arity c)) in
            let def_x = E.substV c_args xs def in
            let def_y = E.substV c_args ys def in
            debug "concatPairs: comparing \n%s and \n%s" (E.toString def_x) (E.toString def_y);
            if def_x = def_y then
                let zxs = List.map2 zeroOf xs ts in
                let xs = List.map E.var xs in
                Some (Typing.cast t' Bitstring (Sym (c, xs)), 
                      Typing.cast t' Bitstring (Sym (c, zxs)))
            else None
          | _ -> None
      in
      List2.filter_map pair (Sym.Map.keys concats)
     in 
        
    let rec argPairs xs ts: (exp * exp) list list =
      match xs, ts with
        | [], [] -> [[]]
        | x :: xs, t :: ts when canErase x ->
          List.map (fun args -> (Var x, zeroOf x t) :: args) (argPairs xs ts)
        | x :: xs, t :: ts ->
          let pairs = (Var x, Var x) :: concatPairs x t in
          List2.cross_product (fun pair args -> pair :: args) pairs (argPairs xs ts)
        | _ -> fail "argPairs: impossible"
    in
    
    let mkFact (args1, args2) =
      S.eqBitstring [Sym (sym, args1); Sym (prime sym, args2)] |> CVFact.make funTypes
    in
  
    argPairs (mkFormalArgs num_args) argTypes
      (* remove trivial equations *)
    |> List.map List.split 
    |> List.filter (fun (args1, args2) -> args1 <> args2)
    |> List.map mkFact 
  in
  
  Sym.Map.bindings auxiliary
  |> List2.concat_map (fun (sym, def) -> 
    debug "Auxiliary facts: checking %s: %s" (Sym.toString sym) (E.toString def);
    let (ts, _) = Sym.Map.find sym funTypes in
    facts sym def ts)


(*************************************************)
(** {1 Input and Output Merging} *)
(*************************************************)

let mergeInOut p =

  let rec mergeIn (vs: var list) p = 
  match (vs, p) with
    | vs, In [v] :: p -> mergeIn (v :: vs) p
    | [], s :: p -> s :: mergeIn [] p
    | vs, (Out _ as s) :: p ->
      In vs :: s :: mergeIn [] p 
    | vs, s :: p -> s :: mergeIn vs p
    | vs, [] -> [In vs] (* including vs =  [] *)
  in

  (*
    Requires only-variables-in-write form.
  *)
  let rec mergeOut es p = 
  match (es, p) with
    | es, Out [e] :: p -> mergeOut (e :: es) p
    | [], s :: p -> s :: mergeOut [] p
    | es, (In _ as s) :: p ->
      Out es :: s :: mergeOut [] p 
    | es, s :: p -> s :: mergeOut es p
    | [], [] -> [Yield] 
    | es, [] -> [Out es]
  in
      
  List.rev (mergeIn [] (List.rev (mergeOut [] p)))  

(*************************************************)
(** {1 The full model} *)
(*************************************************)

module Model = struct
  type t = {
    client: iml;
    server: iml;
    constants: exp Var.Map.t;
    template: Template.t;
    varTypes: Typing.typeCtx;
    funTypes: Typing.funTypeCtx;
    
    concats: symDefs;
    parsers: symDefs;
    arith: symDefs;
    auxiliary: symDefs;
    zeroFuns: symDefs;
    
    auxiliaryFacts: cvfact list;
    zeroFacts: cvfact list;
    parsingEqs: parsingEq list;
    encoderFacts: encoderFact list;
  }
end
  
open Model

(*************************************************)
(** {1 CV Output} *)
(*************************************************)

let printf a = fprintf Common.out_channel a

let showCVStmt: Stmt.t -> string = fun s ->

  let rec showExpBody : exp -> string = function 
    | Var v -> v
    | Sym (Const s, []) -> s
    | Sym (s, es) ->
      Sym.toString s ^ "(" ^ String.concat ", " (List.map showExpBody es) ^ ")"
    | Annotation (_, e) -> showExpBody e
    | e -> "unexpected{" ^ E.dump e ^ "}"

  and showInVar t name = name ^ ": " ^ Type.toString t
  in

  match s with
    | In [v] -> 
      "in(c_in, " ^ showInVar Bitstring v ^ ");";
    
    | In vs -> 
      "in(c_in, (" ^ String.concat ", " (List.map (showInVar Bitstring) vs) ^ "));";

    | New (v, t) -> 
      "new " ^ showInVar t v ^ ";";

    | Out [e] -> 
      "out(c_out, " ^ showExpBody e ^ ");";

    | Out es -> 
      "out(c_out, (" ^ String.concat ", " (List.map showExpBody es) ^ "));";

    | TestEq (e1, e2) ->
      "if " ^ showExpBody e1 ^ " = " ^ showExpBody e2 ^ " then "

    | AuxTest e ->
      "if " ^ showExpBody e ^ " then "

    | Assume e ->
      Printf.sprintf "assume %s in" (showExpBody e)

    | GenTest e ->
      "if " ^ showExpBody e ^ " then "
                                                
    | Event (name, es) -> 
      "event " ^ name ^ "(" ^ String.concat ", " (List.map showExpBody es) ^ ");"
        
    | Let (pat, e) ->
      "let " ^ Pat.dump pat ^ " = " ^ showExpBody e ^ " in"
      
    | Yield -> "yield ."
      
    | Comment s -> sprintf "(* %s *)" s 

let showCVProcess p =
  let zero = 
    if p = [] then " 0 .\n" else
    match last p with
      | Yield -> "\n"
      | _ -> " 0 .\n"
  in
  let result = String.concat "\n" (List.map showCVStmt p) ^ zero in
  result

let print_indent s = print_endline ("  " ^ s)

(*
  FIXME: we aren't even printing the parsing rules, are we?
*)
let writeCV model =

  let casts = nub (Typing.casts model.client @ Typing.casts model.server) in

  let printFunDef isInjective sym def =
    if def <> Unknown then 
      print_endline ("(* " ^ showFun sym def ^ " *)");
    let compos = if isInjective then " [compos]." else "." in
    match sym with
      | Const s -> 
        let _, t = Sym.Map.find sym model.funTypes in
        print_endline ("const " ^ s ^ ": " ^ Type.toString t ^ ".");
        print_endline ""
      | sym -> 
        print_endline ("fun " ^ Sym.cvDeclaration sym (Sym.Map.find sym model.funTypes) ^ compos);
        print_endline ""
  in
    
  let printConcat sym def =
    printFunDef (isInjectiveConcat sym def) sym def;
  in
  
	let printCast: imltype * imltype -> unit = fun (t, t') ->
	  print_endline ("fun " ^ Sym.toString (Cast (t, t')) ^ "(" ^ Type.toString t ^ "): " ^ Type.toString t' ^ " [compos].")
  in

  (* TODO: most of these can now be printed by converting to CVFacts *)  
  let printCastEq: imltype * imltype -> unit = fun (t, t') ->
    (* check that the inverse function is defined at all *)
    if List.mem (t', t) casts && Type.subtype t t' then 
    begin
      print_endline ("forall x: " ^ Type.toString t ^ ";");
      print_endline ("  " ^ Sym.toString (Cast (t', t)) ^ "(" ^ Sym.toString (Cast (t, t')) ^ "(x)) = x.")
    end
  in
  
  let printConstant name def =
    let t = Var.Map.find name model.varTypes in 
    print_endline ("(* " ^ E.dump def ^ " *)");
    print_endline ("const " ^ name ^ ": " ^ Type.toString t ^ ".") 
  in

  let printRelation c1 c2 op =
    try
    begin    
        let id = ref 0 in
    
        let formalArg: imltype -> string = fun _ -> id := !id + 1; "var" ^ string_of_int !id in
        let showArg: string -> imltype -> string = fun v t -> v ^ ": " ^ Type.toString t in
    
        let (argTypes1, t1) = Sym.Map.find c1 model.funTypes in
        let (argTypes2, t2) = Sym.Map.find c2 model.funTypes in
    
        (* FIXME: should this be made part of transformations? *)
        if t1 = t2 && (op = "<>" || argTypes1 = argTypes2) then
        begin
            let args1 = List.map formalArg argTypes1 in
            let args2 = 
              if op = "<>" then List.map formalArg argTypes2 
              else args1 
            in
            let all_args = nub (List.map2 showArg args1 argTypes1 @ List.map2 showArg args2 argTypes2) in
            
            printf "forall %s;\n" (String.concat ", " all_args); 
            printf "  %s(%s) %s %s(%s).\n\n" 
              (Sym.toString c1) (String.concat ", " args1) 
              op
              (Sym.toString c2) (String.concat ", " args2);
        end
    end with Not_found -> ()
  in  

  let printEncoderFact = function
    | Disjoint (s, s') -> printRelation s s' "<>"
    | Equal    (s, s') -> printRelation s s' "="
  in
  
  let printCVFact fact = print_endline (CVFact.toString fact) in

  let clientProc = showCVProcess model.client in
  let serverProc = showCVProcess model.server in

  List.iter print_endline (Template.crypto model.template);

  print_endline "\n(*************************** \n Constants \n***************************)\n";
  Var.Map.iter printConstant model.constants;

  print_endline "\n(*************************** \n  Formatting Functions \n***************************)\n";
  Sym.Map.iter printConcat model.concats;
  Sym.Map.iter (printFunDef false) model.parsers;
  print_endline "";
  List.iter printEncoderFact model.encoderFacts;

  print_endline "\n(*************************** \n  Arithmetic Functions \n***************************)\n";
  Sym.Map.iter (printFunDef false) model.arith;

  print_endline "\n(*************************** \n  Auxiliary Tests \n***************************)\n";
  Sym.Map.iter (printFunDef false) model.auxiliary;

  print_endline "\n(*************************** \n  Zero Functions \n***************************)\n";
  Sym.Map.iter (printFunDef false) model.zeroFuns; 

  print_endline "\n(*************************** \n  Typecasting \n***************************)\n";
  List.iter printCast casts;
  List.iter printCastEq casts; 

  print_endline "\n(*************************** \n  Auxiliary Facts \n***************************)\n";
  List.iter printCVFact model.auxiliaryFacts;

  print_endline "\n(*************************** \n  Zero Facts \n***************************)\n";
  List.iter printCVFact model.zeroFacts;
  
  print_endline "";

  List.iter print_endline (Template.crypto2 model.template);
  List.iter print_endline (Template.query model.template);
  
  print_endline "\n(*************************** \n  Model \n***************************)\n";
  print_endline "let A = ";
  print_endline clientProc;
  print_endline "let B = ";
  print_endline serverProc;

  List.iter print_endline (Template.envp model.template)
  
(*************************************************)
(** {1 Main} *)
(*************************************************)

let verbose = true

let rec removeCasts = function
  | Sym (Op (Sym.Op.T.CastToInt, _), [e]) -> removeCasts e
  | e -> E.descend removeCasts e

let debugIML client server title = 
  if verbose then prerr_title title;
  if verbose then prerr_endline "Client = ";
  if verbose then prerr_endline (Iml.toString (Iml.map removeCasts client));
  if verbose then prerr_endline "Server = ";
  if verbose then prerr_endline (Iml.toString (Iml.map removeCasts server))
 

let main () =  
  (*
  let server = input_value (open_in_bin Sys.argv.(1)) in
  let client = input_value (open_in_bin Sys.argv.(2)) in
  *)
  let (client, server) = Symex.rawIn (open_in_bin Sys.argv.(1)) in

  let server = server |> removeComments |> rewriteCrypto in
  let client = client |> removeComments |> rewriteCrypto in

  debugIML client server "initial IML";

  let server = removeTrailingComputations server in
  let client = removeTrailingComputations client in
  debugIML client server "IML after removing trailing computations";

  let server = normalForm server in
  let client = normalForm client in
  debugIML client server "IML in normal form";

  let server = simplifyDoubleLets server in
  let client = simplifyDoubleLets client in
  debugIML client server "IML after simplifying double lets";

  let client = applyNameAnnotations client in
  let server = applyNameAnnotations server in
  debugIML client server "IML after applying all name annotations";

  let client, clientConcats = extractConcats client in
  let server, serverConcats = extractConcats server in
  let concats = Sym.Map.disjointUnion [clientConcats; serverConcats] in

  debugIML client server "IML after concat extraction";
  if verbose then showFuns concats;
 
  let client, clientParsers = extractParsers client in
  let server, serverParsers = extractParsers server in
  let parsers = Sym.Map.disjointUnion [clientParsers; serverParsers] in

  debugIML client server "IML after parser extraction";
  if verbose then showFuns parsers;

  let server, serverArith = extractArithmetic server in
  let client, clientArith = extractArithmetic client in
  let arith = Sym.Map.disjointUnion [serverArith; clientArith] in
  debugIML client server "IML after replacing arithmetic expressions";
  if verbose then showFuns arith;

  let server, serverAuxiliary = extractAuxiliary server in
  let client, clientAuxiliary = extractAuxiliary client in
  let auxiliary = Sym.Map.disjointUnion [serverAuxiliary; clientAuxiliary] in
  debugIML client server "IML after adding formal versions of auxiliary tests";

  let client, clientConstants = extractConstants concats client in
  let server, serverConstants = extractConstants concats server in
  let constants = Var.Map.disjointUnion [serverConstants; clientConstants] in
  debugIML client server "IML after constant extraction";

  let concats = cleanupDefs (client @ server) concats in
  let parsers = cleanupDefs (client @ server) parsers in
  
  (************************
    Typechecking
  *************************)
  
  let template = Template.readFile ~cv_lib_name:Sys.argv.(2) ~name:Sys.argv.(3) in
  let templateVarTypes, funTypes = Template.collectTypes template in
  prerr_title "Template Function Types: ";
  Typing.dumpFunTypes funTypes;
  prerr_title "Template Variable Types: ";
  Typing.dumpTypes templateVarTypes;
  
  let inferredVarTypes = Typing.merge [Typing.infer funTypes client; Typing.infer funTypes server] in
  prerr_title "Inferred Variable Types";
  Typing.dumpTypes inferredVarTypes;
  let varTypes = Typing.merge [templateVarTypes; inferredVarTypes] in 
  
  let clientFormatterTypes = Typing.deriveUnknownTypes funTypes varTypes client in
  let serverFormatterTypes = Typing.deriveUnknownTypes funTypes varTypes server in
  
  let defs = Sym.Map.disjointUnion [concats; parsers; auxiliary; arith] in
  Typing.checkMissingTypes defs ~templateTypes:funTypes ~inferredTypes:clientFormatterTypes client;
  Typing.checkMissingTypes defs ~templateTypes:funTypes ~inferredTypes:serverFormatterTypes server;

  prerr_title "Inferred Client Types";
  Typing.dumpFunTypes clientFormatterTypes;

  prerr_title "Inferred Server Types";
  Typing.dumpFunTypes serverFormatterTypes;
      
  let funTypes = Typing.mergeFunTypes [funTypes; clientFormatterTypes; serverFormatterTypes] in

  let client = with_debug (Typing.check defs funTypes templateVarTypes []) client in 
  let server = with_debug (Typing.check defs funTypes templateVarTypes []) server in
  
  debugIML client server "IML after typechecking";

  Typing.checkRobustSafety concats funTypes;

  (************************
    Formatting facts
  *************************)

  let parsingEqs = computeParsingRules funTypes parsers concats in
  
  prerr_title "Parsing Equations";
  List.iter (fun eq -> prerr_endline (showParsingEq ~funTypes concats eq)) parsingEqs;
  
  let parsers = cleanupDefs (client @ server) parsers in
  let parsingEqs = cleanupParsingEqs (client @ server) parsingEqs in
  
  let encoderFacts = encoderFacts (Sym.Map.bindings concats) in
  
  (************************
    Pattern matching
  *************************)

  let client = matchInverse client in
  let server = matchInverse server in

  let client = matchSafeParsers parsers concats parsingEqs [] client in
  let server = matchSafeParsers parsers concats parsingEqs [] server in

  let client = mergePatterns client in
  let server = mergePatterns server in
  
  debugIML client server "IML after inserting pattern matching";

  (********************************************
    Bring the process into IO-alternating form
  *********************************************)

  let client = mergeInOut client in
  let server = mergeInOut server in

  debugIML client server "IML after merging inputs and outputs";

  (************************
    Auxiliary tests
  *************************)

  let auxiliaryFacts = auxiliaryFacts concats auxiliary funTypes in
  let auxiliary, funTypes = addAuxiliaryPrimed auxiliary funTypes in
  let client = removeAuxiliary client in
  let server = removeAuxiliary server in
  debugIML client server "IML after removing auxiliary ifs";


  (************************
    Zero facts
  *************************)

  let casts = List2.nub (Typing.casts client @ Typing.casts server) in
  let zeroFacts, zeroFuns, zeroTypes = zeroFacts concats casts funTypes in 
  let funTypes = Sym.Map.disjointUnion [funTypes; zeroTypes] in

  writeCV {
    client; server;
    template;
    constants;
    varTypes; 
    funTypes; 
    parsers; 
    concats; 
    arith; 
    auxiliary;
    zeroFuns;
    auxiliaryFacts;
    zeroFacts; 
    parsingEqs; 
    encoderFacts }


;;

(* 
  Trying to get both the full text of the exception and
  the backtrace. Waiting for a fix for 
  http://caml.inria.fr/mantis/view.php?id=5040
*)

Printexc.register_printer (function 
  | Failure s -> Some s
  | _ -> None);
;;

Printexc.print main () 

