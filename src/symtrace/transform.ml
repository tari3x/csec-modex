(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)

open Common

open Iml
open Iml.Type.T
open Iml.Sym.T
open Iml.Sym.Op.T
open Iml.Exp.T
open Iml.Pat.T
open Iml.Stmt.T

module E = Iml.Exp
module S = Solver

open Transform_imltrace

open Printf

(*************************************************)
(** {1 Types} *)
(*************************************************)

(**
  We represent a lambda expression with n arguments by an expression containing variables
  (mkArg 0) to (mkArg (n - 1)).
*)
type symDef = exp

type symDefs = symDef Sym.Map.t

(**
  [parser(concat) = result]
*)
type parsingEq = (sym * sym) * exp

type fact = Solver.fact

(*************************************************)
(** {1 Formal Arguments} *)
(*************************************************)

let mkArg id = ("arg" ^ string_of_int id)

(** 
  [lenarg(id) = len(arg(id))]
*)
let mkArgLen len id = 
  let l = Len (Var (mkArg id)) in
  (* FIXME: remove this *)
  S.addFact (S.ge l E.zero);
  l

let mkFormalArgs n = List.map mkArg (0 -- (n - 1))

(*************************************************)
(** {1 Debug Output} *)
(*************************************************)

let showFun sym def =
  E.typecheck Bitstring def;
  Sym.toString sym ^ " := " ^ (E.toString def)
  (* | (s, Rewrite e) -> Sym.toString s ^ "/" ^ string_of_int (List.assoc s !arities) ^ " ~> " ^ (E.toString e) *)

let showFuns : symDefs -> unit = fun cs ->
  prerr_endline "";
  Sym.Map.iter (fun s info -> prerr_endline (showFun s info)) cs;
  prerr_endline ""


(*************************************************)
(** {1 Helpers} *)
(*************************************************)

(* TODO: make these local *)
let concatId : int ref = ref 0
let parserId : int ref = ref 0

let newConcatSym ~arity =
  Fun ("conc" ^ string_of_int (increment concatId), arity)  

let newParserSym () = 
  Fun ("parse" ^ string_of_int (increment parserId), 1)  


let findDefinition f defs: symDef =
  match Sym.Map.maybe_find f defs with
    | Some def -> def
    | _ -> fail "Could not find definition for %s" (Sym.toString f)

let showParsingEq ?funTypes concats (((p, c), e): parsingEq) =
  let arity = Sym.arity c in
  let args = mkFormalArgs arity in
  let header = match funTypes with
    | Some funTypes ->
      let ts, _ = Sym.Map.find c funTypes in
      List.map2 (fun arg t -> arg ^ ": " ^ Type.toString t) args ts 
      |> String.concat ", "
      |> sprintf "forall %s;\n" 
    | None -> ""
  in  
  sprintf "%s%s(%s(%s)) = %s" header (Sym.toString p) (Sym.toString c) (String.concat ", " args) (E.toString e)


(*************************************************)
(** {1 Typing} *)
(*************************************************)


module Typing: sig

  type typeCtx = Type.t Var.Map.t
  type funTypeCtx = FunType.t Sym.Map.t

  val inferExp: funTypeCtx -> Type.t -> exp -> typeCtx
  val infer: funTypeCtx -> iml -> typeCtx
  
  val deriveUnknownTypes: funTypeCtx -> typeCtx -> iml -> funTypeCtx
  
  val check: symDefs -> funTypeCtx -> typeCtx -> fact list -> iml -> iml
  
  val merge: typeCtx list -> typeCtx 
  
  val mergeFunTypes: funTypeCtx list -> funTypeCtx
  
  val dumpTypes: typeCtx -> unit
  val dumpFunTypes: funTypeCtx -> unit
  
  val cast: Type.t -> Type.t -> exp -> exp
  val casts: iml -> (Type.t * Type.t) list

  (**
    Check robust safety of concats, as defined in the paper.
  *)
  val checkRobustSafety: symDefs -> funTypeCtx -> unit
  
  (**
    Check that all functions for which we don't have a definition have a type.
  *)
  val checkMissingTypes: symDefs -> templateTypes:funTypeCtx -> inferredTypes:funTypeCtx -> iml -> unit
  
end = struct

  type typeCtx = Type.t Var.Map.t
  type funTypeCtx = FunType.t Sym.Map.t
  
  let merge (ctxs: typeCtx list): typeCtx = 
    let mergeTypes _ t1 t2 = 
      match t1, t2 with
        | Some t, None | None, Some t -> Some t
        | Some t1, Some t2 -> Some (Type.meet t1 t2)
        | None, None -> None
    in
    List.fold_left (Var.Map.merge mergeTypes) Var.Map.empty ctxs

  let mergeFunTypes (ctxs: funTypeCtx list): funTypeCtx = 
    let mergeTypes f t1 t2 = 
      match t1, t2 with
        | Some t, None | None, Some t -> Some t
        | Some t1, Some t2 -> 
          fail "colliding types: %s and %s" (Sym.cvDeclaration f t1) (Sym.cvDeclaration f t2) 
        | None, None -> None
    in
    List.fold_left (Sym.Map.merge mergeTypes) Sym.Map.empty ctxs

  let dumpTypes ctx = 
    Var.Map.iter (fun v t -> prerr_endline (sprintf "%s:  %s" v (Type.toString t))) ctx;
    prerr_endline ""

  let dumpFunTypes : funTypeCtx -> unit = fun funTypes ->
    Sym.Map.iter (fun f t -> prerr_endline (Sym.cvDeclaration f t)) funTypes;
    prerr_endline ""  

  let expType funTypes varTypes = function
    | Var v when Var.Map.mem v varTypes -> Var.Map.find v varTypes
    | Annotation(TypeHint t, _) -> t
    | Sym(f, es) when Sym.Map.mem f funTypes -> 
      let(_, t) = Sym.Map.find f funTypes in t
    | _ -> Bitstring
  
  let cast t t' e =
    if t = t' then e else
    Sym (Cast (t, t'), [e])
  
  let rec casts p = 
  
    let rec castsE e =
      let cs = concat_map castsE (E.children e) in
      match e with
      | Sym (Cast (t, t'), _) ->
        (t, t') :: cs 
      | _ -> cs
    in
    
    match p with
      | s :: p -> concat_map castsE (Stmt.children s) @ casts p
      | [] -> []


  let rec inferExp (funTypes: funTypeCtx) t = function 
    | Var v -> Var.Map.singleton v t
    
    | Annotation(TypeHint t, e) -> inferExp funTypes t e
              
    | Sym(f, es) when not (Sym.Map.mem f funTypes) -> merge (List.map (inferExp funTypes Bitstring) es) 
  
    | Sym(f, es) ->
      let (ts, _) = Sym.Map.find f funTypes in
      merge (List.map2 (inferExp funTypes) ts es) 
      
    | Annotation(_, e) -> (inferExp funTypes) t e
    
    | e -> fail "inferExpTypes: unexpected expression %s" (E.dump e)

            
  let infer (funTypes: funTypeCtx) (p: iml): typeCtx = 
  
    let expType funTypes e = expType funTypes Var.Map.empty e in
    let inferExp = inferExp funTypes in
   
    let rec infer = function
      | Let (VPat v, e) :: p ->  
        let t = expType funTypes e in
        let ctxE = inferExp t e in
        let ctxP = infer p in
        let ctxV = Var.Map.singleton v t in
        merge [ctxE; ctxP; ctxV]
        
      | Let ((FPat _ | Underscore), _) :: _ -> fail "inferTypes: let patterns not supported: %s" (Iml.toString p)
        
      | New (v, t) :: p -> 
        let ctxP = infer p in
        let ctxV = Var.Map.singleton v t in
        merge [ctxP; ctxV]
    
      | In vs :: p -> 
        let ctxP = infer p in
        let ctxV = Var.Map.ofList (List.map (fun vs -> vs, Bitstring) vs) in
        merge [ctxP; ctxV]
      
      | AuxTest _ :: p -> infer p

      | GenTest e :: p -> 
        let ctxE = inferExp Bool e in
        let ctxP = infer p in
        merge [ctxE; ctxP]        
                        
      | TestEq (e1, e2) :: p -> 
        let ctx1 = inferExp Bitstring e1 in
        let ctx2 = inferExp Bitstring e2 in
        let ctxP = infer p in
        merge [ctx1; ctx2; ctxP]
        
      | Assume e :: p ->
        infer p
      
      | Event (ev, es) :: p ->
        (* Events symbols of type bool in CV *) 
        let ctxE = inferExp Bool (Sym (Fun (ev, List.length es), es)) in
        let ctxP = infer p in
        merge [ctxE; ctxP]
      
      | (Comment _ | Out _ | Yield) as s :: p -> 
        let ctxS = List.map (inferExp Bitstring) (Stmt.children s) in
        let ctxP = infer p in
        merge (ctxP :: ctxS)
        
      | [] -> Var.Map.empty
    in
    
    infer p
    
  (**
    Returns only the context for formatter functions. Merge with user functions yourself.
  
    Assumes that the process is in the formatting-normal form, that is,
    every formatter application has the form let [x = f(x1, ..., xn)]. 
    
    We replace all argument types of auxiliary tests by bitstring. Consider
    
      in(c_in, (msg4: bitstring, cipher2: bitstring));
      if auxiliary11(cipher2, msg4) then 
      let msg6 = D(cast_bitstring_bounded_1077_ciphertext(cipher2), key2) in ...
    
    We cannot require that cipher2 is bounded_1077_ciphertext when auxiliary11 is invoked,
    because belonging to the type is what auxiliary11 checks in the first place.
  *)
  let deriveUnknownTypes funTypes (ctx: typeCtx) (p: iml): funTypeCtx = 
  
    let rec derive s = 
      match s with
      | Let (VPat v, Sym (f, vs)) when not (Sym.Map.mem f funTypes) ->
        let ts = 
          List.map (function | Var v -> Var.Map.find v ctx 
                             | _ -> fail "formatting-normal form expected: %s" (Stmt.toString s))
          vs
        in                   
        Some (f, (ts, Var.Map.find v ctx))
        
      | GenTest (Sym (f, vs)) when not (Sym.Map.mem f funTypes) -> 
        let ts = 
          List.map (function | Var v -> Bitstring 
                             | _ -> fail "malformed test statement: %s" (Stmt.toString s))
          vs
        in
        Some (f, (ts, Bool))
        
      | _ -> None 
        
    in Sym.Map.ofList (filter_map derive p)
        
  let proveType facts ((argTypes, resType): FunType.t) (f: sym) (f_def: exp) (args: exp list): bool =
  
    if List.length args <> List.length argTypes then
      fail "wrong number of arguments: %s(%s)" (Sym.toString f) (E.dumpList args);

    let formalArgs = mkFormalArgs (List.length args) in
    let e_f = E.subst formalArgs args f_def in

    (*
    debug ("typecheck: e_def = " ^ E.dump e_def);
    debug ("typecheck: context = " ^ dumpList ctx);
    *)

    let argFacts = List.map2 S.inType args argTypes in
    let resFact = S.inType e_f resType in
    
    debug "proving type %s" (Sym.cvDeclaration f (argTypes, resType));
    S.implies (argFacts @ facts) [resFact]


  let eraseTypeAnnotations p = 
    let rec erase = function
      | Annotation (TypeHint _, e) -> erase e
      | e -> E.descend erase e
    in
    Iml.map erase p


  let check (defs: symDefs) (funTypes: funTypeCtx) (ctx: typeCtx) (facts: fact list) (p: iml): iml = 

    let typefacts ctx = 
      Var.Map.bindings ctx 
      |> List.map (fun (v, t ) -> S.inType (Var v) t)
    in

    let rec checkExp ctx facts t' e: exp = 
    match e with
      | Var v -> 
        let t = Var.Map.find v ctx in
        if not (S.implies (facts @ typefacts ctx) [S.inType (Var v) t']) then
          fail  "cannot prove type: %s: %s" v (Type.toString t');
        cast t t' e
    
      | Sym (f, es) -> 
        let (ts, t) = Sym.Map.find f funTypes in
        let es' = List.map2 (checkExp ctx facts) ts es in
        let tt = Type.meet t t' in
        begin match Sym.Map.maybe_find f defs with
          | Some def -> 
            if not (proveType (facts @ typefacts ctx) (ts, tt) f def es) then
              fail "typecheck: cannot prove type %s" (Sym.cvDeclaration f (ts, tt))
          | None -> 
            if not (Type.subtype t t') then
              fail "typecheck: cannot prove type %s" (Sym.cvDeclaration f (ts, t'))
        end;
        cast t t' (Sym (f, es'))
        
        (* Type annotations are only used in inference, and ignored in typechecking *)
      | Annotation (a, e) -> Annotation (a, checkExp ctx facts t' e) 
        
      | e -> fail "checkExp: unexpected expression %s" (E.dump e)
    in
  
    let rec check ctx facts p =
    match p with
      | Let (VPat v, e) :: p ->
        let t = expType funTypes ctx e in
        let e' = checkExp ctx facts t e in
        let p' = check (Var.Map.add v t ctx) facts p in
        Let (VPat v, e') :: p' 
        
      | Let (_, _) :: _ -> fail "checkTypes: let patterns not supported: %s" (Iml.toString p)
        
      | AuxTest e :: p ->
        let p' = check ctx (facts @ [e]) p in
        AuxTest e :: p'
        
      | GenTest e :: p ->
        let e = checkExp ctx facts Bool e in
        let p = check ctx facts p in
        GenTest e :: p
        
      | TestEq (e1, e2) :: p ->
        let t1 = expType funTypes ctx e1 in
        let t2 = expType funTypes ctx e2 in
        let tt = Type.meet t1 t2 in
        let e1' = checkExp ctx facts tt e1 in
        let e2' = checkExp ctx facts tt e2 in
        (* Not adding a non-auxiliary test to facts *)
        let p' = check ctx facts p in
        TestEq(cast t1 tt e1', cast t2 tt e2') :: p'
        
      | Assume e :: p ->
        Assume e :: check ctx (facts @ [e]) p
    
      | In vs :: p -> 
        let ctxV = Var.Map.ofList (List.map (fun vs -> vs, Bitstring) vs) in
        let p' = check (merge [ctx; ctxV]) facts p in
        In vs :: p'
        
      | New (v, t) :: p ->
        begin match Type.stripName t with
        | Fixed _ ->  
          let p' = check  (Var.Map.add v t ctx) facts p in
          New (v, t) :: p' 
        | _ -> fail "fixed type expected in new expression: %s" (Stmt.toString (New (v, t)))
        end
            
      | Out es :: p ->
        let es' = List.map (fun e -> checkExp ctx facts (expType funTypes ctx e) e) es in
        let p' = check ctx facts p in
        Out es' :: p'
    
      | Event (ev, es) :: p ->
        let (ts, t) = Sym.Map.find (Fun (ev, List.length es)) funTypes in 
        let es' = List.map2 (fun e t -> checkExp ctx facts t e) es ts in
        let p' = check ctx facts p in
        Event (ev, es') :: p'
        
      | Yield :: p -> Yield :: check ctx facts p
        
      | Comment s :: p -> Comment s :: check ctx facts p
        
      | [] -> []
    in
  
    check ctx facts (eraseTypeAnnotations p)
    
    
  let checkRobustSafety (concats: symDefs) (funTypes: funTypeCtx) = 
  
    let safe f def = 
      let (ts, t) = Sym.Map.find f funTypes in
      let args = mkFormalArgs (Sym.arity f) |> List.map E.var in
      if not (proveType [] (ts, t) f def args && t <> Bitstringbot) then
        fail "function %s is not robustly safe" (Sym.cvDeclaration f (ts, t));
    in
    
    Sym.Map.iter safe concats

  let checkMissingTypes defs ~templateTypes ~inferredTypes p = 
    let rec check = function
      | Sym (f, es) ->
        if not (Sym.Map.mem f defs) && not (Sym.Map.mem f templateTypes) then
          begin match Sym.Map.maybe_find f inferredTypes with
            | Some t -> fail "No type found for function %s, suggested type: %s" (Sym.toString f) (Sym.cvDeclaration f t);
            | None -> fail "No type found for function %s" (Sym.toString f);
          end;
        List.iter check es
      | e -> List.iter check (E.children e)
    in
    Iml.iter check (removeAuxiliary p)

end


(*************************************************)
(** {1 Facts} *)
(*************************************************)

(* TODO: this will be merged with solver facts *)
module CVFact = struct
  type t = Forall of (var * Type.t) list * exp
  
  let make funTypes (e: exp): t =
    let ts = Typing.inferExp funTypes Bool e in
    Forall (Var.Map.bindings ts, e)

  let toString (Forall (args, e)) =
    let showVar (v, t) = v ^ ": " ^ Type.toString t in
    "forall " ^ String.concat ", " (List.map showVar args) ^ ";\n\t" ^ E.toString e ^ "."
         
end

(*************************************************)
(** {1 Crypto rewriting} *)
(*************************************************)

let rewrite e = 
  
  let rec rewrite : exp -> exp = function
    | Sym (Fun ("HMAC", 3), [String hash; msg; key]) -> Sym (Fun ("HMAC_" ^ hash, 2), [msg; key])
    | Sym (Fun ("SHA256", 1), [e]) ->
      (* we cannot use a CV rewrite rule cause the key needs to be freshly generated *)
      let sha256key = Var "SHA256_key" in 
      Sym (Fun ("SHA_hash", 2), [sha256key; e]) 
    (*
    | Sym (("IfEq", _), [Sym (("DSA_verify", _), es, l, tag); eOne], l', tag') when S.equalLen eOne one -> 
      Sym (("If", Prefix), [Sym (("DSA_check", Prefix), es, l, tag)], l', tag')
    *)
    | e -> E.descend rewrite e
  in

  let e = rewrite e in 
  e

let rewriteCrypto p =
  List.map (Stmt.descend rewrite) p


(*************************************************)
(** {1 Let simplification} *)
(*************************************************)

let simplifyLets p =
 
  (* Remove width annotations in lets as those are not useful *)
  let cleanup = function
    (* | Let (VPat v, Annotation (Width _, e)) -> Let (VPat v, e) *)
    | s -> s
  in

  let rec simplify = function
    | Let (VPat v, Var v') :: p -> simplify (Iml.subst [v] [Var v'] p) 
    | Let (VPat v, e) :: p when Iml.refcount v p = 0 -> simplify p
    | s :: p -> s :: simplify p
    | [] -> []
  in
  
  List.map cleanup p |> simplify

let simplifyDoubleLets p = 

  let rec simplify defs = function
    | Let (VPat v, Var v') :: p -> Let (VPat v, Var v') :: simplify defs p  
    | Let (VPat v, e) :: p -> 
      begin try
        let v'= List.assoc e defs in
        Let (VPat v, Var v') :: simplify defs p
      with Not_found ->
        Let (VPat v, e) :: simplify ((e, v) :: defs) p
      end
    | s :: p -> s :: simplify defs p
    | [] -> []
  in
  
  simplify [] p


(*************************************************)
(** {1 Name annotations} *)
(*************************************************)

(**
  Changes things like
    new var1: fixed_n;
    let var2 = var1 in
    let named_var = var2 in P
  (where there is a name annotation on var2) to 
    new named_var: fixed_n in P
  while checking that var1 does not occur in P.

  No renaming is done to free variables of course.
  
  Name annotations get removed in the end.
*)
  
let applyNameAnnotations p = 

  let free_vars = Iml.freeVars p in

  (* 
    Which variable should be renamed to which? No loops.
  *)
  let names = ref Var.Map.empty in
  
  let rec resolve name =
    match Var.Map.maybe_find name !names with
      | Some name' -> resolve name'
      | None -> name 
  in 

  (* Rename v1 and all members of its equivalence class to v2. *)
  let rec rename v1 v2 =
    match Var.Map.maybe_find v1 !names with
      | None ->
        (* We are at the top of the chain, add a new element above it *)
        if v1 <> v2 then
          names := Var.Map.add v1 v2 !names
      | Some v1' ->
        if v1 = v2 then
          (* v1 will become the new top, so we remove its own renaming *)
          names := Var.Map.remove v1 !names;
        rename v1' v2
  in

  let rec expName = function
    | Var v -> Some v
    | Annotation (Name name, e) -> Some name
    | Annotation (_, e) -> expName e
    | e -> None
  in 

  let rec collectNamesE = function
    | Annotation (Name name, e) ->
      begin match expName e with
          (* Do not rename free variables *)
        | Some name' when not (List.mem name' free_vars) -> 
          rename name' name
        | _ -> ()
      end;
      collectNamesE e
    | e -> List.iter collectNamesE (E.children e)
  in
      
  let collectNames = function
    | Let (VPat v, e) ->
      begin match expName e with
        | Some name -> rename v name 
        | _ -> ()
      end
    | s -> ()
  in
  
  (* We do substitution without regard for capture *)
  let substV vs vs' = Iml.map (E.substV vs vs') in
  
  (* Rename variables according to collected names *)
  let rec renameVars = function
    | Let (VPat v, e) :: p ->
      let v' = resolve v in
      Let (VPat v', e) :: renameVars (substV [v] [v'] p)
    | New (v, t) :: p ->
      let v' = resolve v in
      New (v', t) :: renameVars (substV [v] [v'] p)
    | In vs :: p ->
      let vs' = List.map resolve vs in
      In vs' :: renameVars (substV vs vs' p) 
    | s :: p -> s :: renameVars p
    | [] -> []
  in

  let rec removeNameAnnotations = function
    | Annotation (Name _, e) -> removeNameAnnotations e
    | e -> E.descend removeNameAnnotations e
  in 

  List.iter collectNames p;
  (* It is important that this comes second, 
     to make sure annotation renamings override 
     assignment renamings *)
  Iml.iter collectNamesE p;
  renameVars p |> Iml.map removeNameAnnotations |> simplifyLets
         
(*************************************************)
(** {1 Normal Form} *)
(*************************************************)

let isTag: exp -> bool = fun e -> E.isConcrete e 

let sortDefs defs =

  let gt s s' =
    match s, s' with
      | Let (_, e), Let (VPat v, _) -> List.mem v (E.vars e)
      | _ -> false
  in
  topsort gt defs


let normalForm p = 

  let rec normalize p = 
  
    let defs = ref [] in
  
    let mkVar = function
      | Var v -> Var v
      | e ->  
        let v = Var.fresh "" in
        defs := Let (VPat v, e) :: !defs;
        Var v 
    in
    
    (* remove expressions that are themselves lengths of an expression that follows *) 
    let rec removeLens = function
      | String s :: es -> String s :: removeLens es
      | e :: es ->
        if List.exists (fun e' -> S.equalInt (E.valueUnsigned e) (Len e')) es 
        then removeLens es
        else e :: removeLens es
      | [] -> []
    in
  
    (*
      This is the heuristic part - we convert an expression like 
      20 | 20 | x | y, 
      where len(x) = 20 and len(y) = 20 to
      len(x) | len(y) | x | y
      
      args is the list of arguments that we haven't found a length for yet. 
    *)
    let rec explicateLens args = function 
      | String s :: es -> String s :: explicateLens args es
      | e :: es ->
        begin match find_and_remove (fun e' -> S.equalInt (E.valueUnsigned e) (Len e')) args with
          | Some (e', args) -> 
            BS (Len e', (IntType.Unsigned, E.width_exn e)) :: explicateLens args es
          | None -> e :: explicateLens args es
        end
      | [] -> []
    in
  
    let rec extractAuxiliary e = 
      match e with 
      | e when isAuxiliary e -> E.descend extractAuxiliary e
      | e -> mkVar (extract e)

    (* Variables for same expressions will later be unified by simplifyLets *)
    and extractConcat = function
      | e when isTag e -> e
      | Len e -> Len (mkVar (extract e))
      | e -> mkVar (extract e) 
      
    and extractParser v m e =
      match e with
      | e when Type.subtype (E.typeOf e) Bitstring && S.equalBitstring m e -> v
      | e when Type.subtype (E.typeOf e) Type.Int && S.equalInt (Len m) e -> Len v
      | Sym (s, es) when Sym.isArithmetic s -> 
        E.descend (extractParser v m) e
      | Sym (Op (CastToInt, _), _) 
      | Val _
      | BS _
      | Range _ 
      | Int _ -> E.descend (extractParser v m) e
      | e -> fail "normalForm: unexpected parser subexpression %s" (E.dump e) (* mkVar (extract e) *)
      
    and extract e = 
      match e with
      | e when isAuxiliary e -> extractAuxiliary e
              
      | Concat es ->
        let args = removeLens (List.filter (non isTag) es) in
        let es = explicateLens args es in
        debug "extract concat: args = %s" (E.listToString args);
        debug "extract concat: es = %s" (E.listToString es);
        Concat (List.map extractConcat es)
        
      | Range (Range _, _, _) ->
        fail "extractParsers: nested range unsupported: %s" (E.dump e)
        
      | Range (m, pos, len) ->
        let v = mkVar (extract m) in
        extractParser v m e
        
      | e -> E.descend moveOut e
    
    and moveOut e = 
      match e with
        | Concat _ | Range _ -> mkVar (extract e)
        | e when isAuxiliary e -> mkVar (extract e)  
        | _ -> extract e
    in 
    
    match p with
      | AuxTest e :: p ->
        S.addFact e; 
        AuxTest e :: normalize p
        
      | Assume e :: p ->
        S.addFact e;
        Assume e :: normalize p
        
      | Let (VPat v, e) :: p ->
        S.addFact (S.eqBitstring [Var v; e]);
        let e = extract e in
        sortDefs !defs @ (Let (VPat v, e) :: normalize p)

      | Let _ :: _ ->
        fail "normalForm: impossible: let patterns unexpected"
                        
      | In vs as s :: p -> 
        List.iter (fun v -> S.addFact (S.isDefined (Var v))) vs;
        s :: normalize p
        
      | (GenTest _ | TestEq _ | Out _ | New _ | Event _ | Yield | Comment _ ) as s :: p ->
        let s = Stmt.descend moveOut s in
        sortDefs !defs @ (s :: normalize p)
        
      | [] -> []
  in
  S.resetFacts ();
  let p = normalize p in
  S.resetFacts ();
  simplifyLets p

(*************************************************)
(** {1 Extraction helper} *)
(*************************************************)

let extractDef e = 
  let vs = E.vars e in
  let args = mkFormalArgs (List.length vs) |> List.map E.var in
  let e = E.subst vs args e in
  vs, e
  
(*************************************************)
(** {1 Arithmetic expressions} *)
(*************************************************)

let extractArithmetic p: iml * symDefs =

  let defs = ref [] in

  let rec extract e = 
    match e with
    | e when isAuxiliary e -> 
      let vs, def = extractDef e in
      let f = Fun (Var.fresh "arithmetic", List.length vs) in
      defs := (f, def) :: !defs;
      let args = List.map E.var vs in
      Sym (f, args)
      
    | e -> E.descend extract e
  in   
   
  let p = mapWithoutAuxiliary extract p in
  p, Sym.Map.ofList !defs


(*************************************************)
(** {1 Constants} *)
(*************************************************)

(*
  TODO: just return Const symbols in a symDef
*)
(**
  Returns definitions of extracted constants. 
*)
let extractConstants concats p: iml * exp Var.Map.t = 
  
  let defs = ref Var.Map.empty in
  
  let mkConst name def =
    defs := Var.Map.add name def !defs;
    Var name
  in
  
	let rec extract e =
    match e with
    | Int ival -> mkConst ("integer_" ^ Int64.to_string ival) e
    | String s -> mkConst ("string_" ^ s) e
    | Sym (c, []) when Sym.Map.mem c concats ->
      let def = findDefinition c concats in
      mkConst ("const_" ^ (Sym.toString c)) def 
            
    | e -> E.descend extract e
  in
  
  let p = mapWithoutAuxiliary extract p in
  p, !defs



(*************************************************)
(** {1 Concatenations} *)
(*************************************************)

let extractConcats p: iml * symDefs =

  let concats: (sym * symDef) list ref = ref [] in

  (*
    Check whether the concat definition only consists of formal arguments
    (no lengths or tags).
  *)
  let rec isTrivialConcat: exp list -> bool = function
    | Var _ :: es -> isTrivialConcat es 
    | [] -> true
    | _ :: es -> false
  in

  let extract : exp -> exp = function
    | Concat es as e ->
      debug "extract, e = %s" (E.dump (Concat es));
      let vs, def = extractDef e in 
      let f_c = newConcatSym (List.length vs) in
      concats := (f_c, def) :: !concats;
      debug "extract, e_new = %s" (E.dump def);
      begin match def with
        | Concat es when isTrivialConcat es ->
          fail
            "The concatenation does not contain argument lengths or tags. This may lead to non-termination. %s"
            (E.dump def)
        | _ -> ()
      end;
      let args = List.map E.var vs in      
      Sym (f_c, args)
      
    | e -> e
  in
      
  let p = mapWithoutAuxiliary extract p in
  p, Sym.Map.ofList !concats

(**
  If [useTypeInfo], we don't require lengths for arguments of fixed-length types. 
*)
let isInjectiveConcat sym def =
  (*
  debug "isInjectiveConcat: %s" (E.toString def);
  *)
	match def with 
  | Concat es ->
    (* if useTypeInfo then
      fail ("useTypeInfo: fix code")
      (*
	    let (ts, _) = 
	      try List.assoc name !funTypes
	      with Not_found -> fail ("isInjectiveConcat: concat " ^ name ^ " has no type") in
	    check ts [] es
      *)
    else *) begin
      let args = List.filter (function Var _ -> true | _ -> false) es in
      let lens = List.filter (function Len _ -> true | _ -> false) es in
      let argsWithoutLens = 
        filter_out (fun v -> 
          List.exists (fun l -> S.equalInt (Len v) l) lens)
          args
      in
      (*
      debug "args: %s" (E.listToString args);
      debug "lens: %s" (E.listToString lens);
      debug "argsWithoutLens: %s" (E.listToString argsWithoutLens);
      *)
      
      List.length argsWithoutLens <= 1
    end
  | _ -> true


type encoderFact = 
  | Disjoint of sym * sym
  | Equal of sym * sym
    
let encoderFact (s, e) (s', e') = 
  
  let rec scan es es' =
    debug "encoderFact: matching %s and %s" (E.dumpList es) (E.dumpList es'); 
    match es, es' with
      | e :: es, e' :: es' when S.equalBitstring e e' -> scan es es'
      | e :: es, e' :: es' when isTag e && isTag e' && S.equalInt (Len e) (Len e') -> Some (Disjoint (s, s'))
      | [], [] -> Some (Equal (s, s'))
      | _ -> None
  in
  match e, e' with
    | Concat es, Concat es' -> scan es es'
    | _ -> failwith "encoderFact: impossible"

        
let rec encoderFacts: (sym * symDef) list -> encoderFact list = function
  | c :: cs -> 
    filter_map (encoderFact c) cs @ encoderFacts cs
  | [] -> []
  

    
(*************************************************)
(** {1 Extracting Parsers} *)
(*************************************************)

let extractParsers p =

  let parsers = ref [] in
 
  let extract e = 
    match e with
    | Range (Var v, _, _) ->
      debug "adding parser for the expression %s" (E.toString e);
      
      let vs, def = extractDef e in
      if vs <> [v] then fail "extractParsers: impossible";
      
      let f_p = newParserSym () in
      
      (*
      debug ("adding parser, " ^ Sym.toString f_p ^"(x) = " ^ E.dump def);
      *)
      
      parsers := (f_p, def) :: !parsers;
      
      let args = List.map E.var vs in
      Sym (f_p, args)
      
    | e -> e
  in
      
  let p = mapWithoutAuxiliary extract p in
  p, Sym.Map.ofList !parsers


(*************************************************)
(** {1 Extracting Auxiliary Test Conditions} *)
(*************************************************)

(**
  Returns arities of extracted expressions.
*)
let extractAuxiliary p: iml * symDefs =

  let arities = ref [] in

  let rec extract = function
    | AuxTest e :: p ->  
      let vs, def = extractDef e in
      let f = Fun (Var.fresh "auxiliary", List.length vs) in
      arities := (f, def) :: !arities;
      let args = List.map E.var vs in
      GenTest (Sym (f, args)) :: AuxTest e :: extract p
      
    | s :: p -> s :: extract p
    | [] -> []
  in   
   
  let p = extract p in
  p, Sym.Map.ofList !arities



(*************************************************)
(** {1 Parsing Rules} *)
(*************************************************)

let computeParsingRules funTypes (parsers: symDefs) (concats: symDefs): parsingEq list =
  
  let parsingEqs = ref [] in
  
  let checkType nargs p c e =
    let (pts, pt) = Sym.Map.find p funTypes in
    let (cts, ct) = Sym.Map.find c funTypes in
    if pts <> [ct] then false else
    begin
      let args = mkFormalArgs nargs |> List.map E.var in 
      List2.any (List.map2 (fun arg t -> arg = e && t = pt) args cts) 
    end
  in
    
  let applyParser f_p parserDef f_c concatDef =
    (*
    debug ("applyParser, parser: " ^ showFun parser);
    debug ("applyParser, concat: " ^ showFun concat);
    *)
    let arg = mkArg 0 in

    let e = E.subst [arg] [concatDef] parserDef in 
    
    debug "applyParser: e after subst arg = %s" (E.dump e);

    S.addFact (S.isDefined concatDef);    
    let e' = Simplify.deepSimplify e in
    S.resetFacts ();
    
    debug "applyParser %s to %s: \n %s \n ~> %s \n" (Sym.toString f_p) (Sym.toString f_c)  
                                                    (E.dump e) (E.dump e');

    if checkType (Sym.arity f_c) f_p f_c e' then
      parsingEqs := !parsingEqs @ [((f_p, f_c), e')]
  in 
  
  (* replaceTagsInConcats (); *)
  Sym.Map.iter (fun f_p parser -> Sym.Map.iter (applyParser f_p parser) concats) parsers;
  !parsingEqs


(*************************************************)
(** {1 Parsing Safety} *)
(*************************************************)

let wellFormed e_c = 
  let args = List.filter (function Var _ -> true | _ -> false) e_c in
  let lens = List.filter (function Len _ -> true | _ -> false) e_c in
  (* debug "wellFormed: %s, args = %s, lens = %s" (E.listToString e_c) (E.listToString args) (E.listToString lens); *)
  if not (distinct args) || not (distinct lens) then false
  else 
    let argsWithLens = List.map (function Len v -> v | _ -> fail "wellFormed: impossible") lens in
    (* debug "wellFormed: argsWithLens = %s" (E.listToString argsWithLens); *)
    match multidiff (=) args argsWithLens with
      | [e] -> e = last e_c
      | _ -> false

let rec mkParsers ls ps es e_c = 
  let x = Var (mkArg 0) in
  match e_c with
    | e_i :: e_c ->
      let l = 
        match e_i, e_c with
          | _, [] ->
            Sym(MinusInt, [Len x; Simplify.sum ls])
          | Var _ as v, _ ->
            (* debug "looking for %s in %s" (E.dump v) (E.dumpList es); *) 
            (* Need comparison in this order as es will contain lengths of lengths *)
            List.nth ps (find_index_exn (function Len v' when v = v' -> true | _ -> false) es) 
          | e_i, _ -> 
            Len e_i
      in
      let p = Range(x, Simplify.sum ls, l) in
      mkParsers (ls @ [l]) (ps @ [p]) (es @ [e_i]) e_c
      
    | [] -> ps

let rec tagFacts ps e_c =
  match ps, e_c with
    | p :: ps, (Len _ | Var _) :: e_c ->
      tagFacts ps e_c
    | p :: ps, e_t :: e_c ->
      S.eqBitstring [p; e_t] :: tagFacts ps e_c
    | [], [] -> []
    | _ -> failwith "tagFacts: impossible"
      

let inrange facts e c c_def = 
  let x = mkArg 0 in
  match c_def with
  | Concat e_c when wellFormed e_c ->
    
    increase_debug_depth ();
    
    let ps = mkParsers [] [] [] e_c in
    debug ~raise_by:1 "inrange: parsers: %s\n" (E.listToString ps);
    let fields = List.map (with_debug ~depth:1 S.isDefined) ps in
    let tags = tagFacts ps e_c in
    
    let parse_facts = List.map (E.subst [x] [e]) (fields @ tags) in

    decrease_debug_depth ();

    S.implies facts parse_facts
    
  | _ -> false

let matchConcat parsingEqs facts p e (c, c_def) =
  debug "\nmatchConcat: checking %s(%s) against concat %s" (Sym.toString p) (E.toString e) (Sym.toString c);
  (*
    debug (sprintf "checkParsingSafety: the parser %s is not an inverse of %s" p c); 
    debug (sprintf "checkParsingSafety: no concat satisfies the application of %s to %s" p (dump e));
  *) 
  if not (silent ~depth:10 (isInjectiveConcat c) c_def) || not (inrange facts e c c_def) then None
  else 
    match maybe_assoc (p, c) parsingEqs with
      | Some (Var v) ->
        let vs = mkFormalArgs (Sym.arity c) in
        Some (c, find_index_exn ((=) v) vs)
      | _ -> None 

let safeParse (concats: symDefs) parsingEqs facts f_p e =
   first_some (matchConcat parsingEqs facts f_p e) (Sym.Map.bindings concats)


(*************************************************)
(** {1 Trailing computation} *)
(*************************************************)

(**
  Remove unobservable computations at the end of a process.
*)
let removeTrailingComputations p =

  let rec remove p = 
    match p with
    | (Out _ | Event _) :: _ -> p 
    | s :: p -> remove p
    | [] -> []
  in
  
  List.rev (remove (List.rev p))       

(*************************************************)
(** {1 Cleanup} *)
(*************************************************)

(*
(**
  Leave only basic concats. Also remove unused concats (those turned into constants).
*)
*)
let cleanupDefs p (defs: symDefs): symDefs =

  let containsSym c s = List.exists (E.containsSym c) (Stmt.children s) in

  Sym.Map.filter (fun s _ -> List.exists (containsSym s) p) defs
  
  
let cleanupParsingEqs p (eqs: parsingEq list): parsingEq list =

  let containsSym sym stmt = List.exists (E.containsSym sym) (Stmt.children stmt) in

  List.filter (fun ((f_p, _), _) -> List.exists (containsSym f_p) p) eqs


(* 680 lines *)
