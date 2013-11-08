
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

  val read_file: cv_lib_name:string -> name:string -> t

  val collect_types: t -> Typing.type_ctx * Typing.fun_type_ctx
  
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
 

  let read_file ~cv_lib_name ~name = 
  
    let crypto = ref [] in
    let crypto2 = ref [] in
    let query = ref [] in
    let envp = ref [] in
    let typehints = ref [] in
    let model = ref [] in
  
    let rec split_template: string list ref -> string list -> unit = fun dest -> function
      | l1 :: l2 :: ls' when trim l2 = "<Environment>" -> split_template envp (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Query>" -> split_template query (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Model>" -> split_template model (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Type hints>" -> split_template typehints (((l1 ^ "\n" ^ l2) :: ls'))
      | l1 :: l2 :: ls' when trim l2 = "<Crypto2>" -> split_template crypto2 (((l1 ^ "\n" ^ l2) :: ls'))
      | l :: ls'  -> dest := !dest @ [l]; split_template dest ls'   
      | [] -> ()  
    in
  
    let c = open_in name in
    split_template crypto (Common.read_file c);
    Cryptoverif.Settings.lib_name := cv_lib_name;
    let (_, _, _, _, _, _, q) = read_file name in
    {crypto = !crypto; crypto2 = !crypto2; query = !query; envp = !envp; typehints = !typehints; model = !model; 
     q; env = !CV.Stringmap.env }
  
  
  let collect_types t =
  
    let types = ref [] in
    let fun_types = ref [] in
  
    let convert_fun_type: typet list * typet -> Fun_type.t = fun (ts, t) ->
      List.map (fun t -> Type.of_string t.tname) ts, Type.of_string t.tname 
    in
  
    let collect_env_types env =
    
      let do_entry : string -> env_entry -> unit = fun k -> function
        | EFunc f ->
          (* Constants are encoded as functions with no arguments, but we want to treat them as variables *)
          let (ts, t) = convert_fun_type f.f_type in
          if ts = [] then
            types := (f.f_name, t) :: !types
          else
            fun_types := (f.f_name, (ts, t)) :: !fun_types 
        | EEvent f ->
          (* for some reason it adds an extra bitstring parameter in front of the ones I define *)
          let (atypes, rtype) = f.f_type in
          fun_types := (f.f_name, convert_fun_type (List.tl atypes, rtype)) :: !fun_types
        | EVar b -> types := (b.sname, Type.of_string b.btype.tname) :: !types
        | _ -> ()
      in
    StringMap.iter do_entry env
    in
    
    let rec collect_input_process_types : inputprocess -> unit = fun q -> 
    
      let rec collect_pattern : pattern -> unit = function
        | PatVar b -> types := (b.sname, Type.of_string b.btype.tname) :: !types
        | PatTuple (_, pats) -> List.iter collect_pattern pats 
        | PatEqual _ -> ()
      in
      
      match q.i_desc with
          | Nil -> ()
          | Par (q, q') -> collect_input_process_types q; collect_input_process_types q'
          | Repl (_, q) -> collect_input_process_types q
          | Input (_, pat, q) -> collect_pattern pat; collect_output_process_types q
  
    and collect_output_process_types : process -> unit = fun p ->
      match p.p_desc with
          | Yield -> ()
          | Restr (b, p) ->
            types  := (b.sname, Type.of_string b.btype.tname) :: !types;
            collect_output_process_types p
          | Test (_, p, p') -> collect_output_process_types p; collect_output_process_types p'
          | Find _ -> fail "collect_types: unexpected find construct"
          | Output (_, _, q) -> collect_input_process_types q
          | Let (pat, _, p, p') ->
            collect_pattern_types pat;  
            collect_output_process_types p; collect_output_process_types p'
          | EventP (_, p) -> collect_output_process_types p
  
    and collect_pattern_types: pattern -> unit = function
      | PatVar b -> types := (b.sname, Type.of_string b.btype.tname) :: !types 
      | PatTuple (_, pats) -> List.iter collect_pattern_types pats
      | PatEqual _ -> ()
    in
        
    collect_env_types t.env;
    collect_input_process_types t.q;
    Var.Map.of_list !types,
    Sym.Map.of_list (List.map (fun (f, (ts, t)) -> (Sym.T.Fun (f, List.length ts), (ts, t))) !fun_types)
end

(********************************************************)
(** {1 Replace inverse functions by pattern matching} *)
(********************************************************)

let is_inverse f = 
  match Str.split (Str.regexp "_") f with
    | "inverse" :: _ -> true
    | _ -> false 

let inverse_of f = Fun (Str.replace_first (Str.regexp "inverse_") "" f, 1)

let rec check_no_inverse e = 
  match e with
  | Sym (Fun (f, _), _) when is_inverse f -> 
    fail "inverse function not directly in let-bindig: %s" (E.to_string e)
  | e -> List.iter check_no_inverse (E.children e)

let rec match_inverse p =
  match p with
    | Let (VPat v, Sym (Fun (f, _), [e])) :: p when is_inverse f ->
      Let (FPat (inverse_of f, [VPat v]), e) :: match_inverse p

    | s :: p -> 
      List.iter check_no_inverse (Stmt.children s);
      s :: match_inverse p
          
    | [] -> []


(*************************************************)
(** {1 Use pattern matching for safe parsing} *)
(*************************************************)

let mk_pattern f_c arity v i =
  let pat = List.replicate arity Underscore in
  FPat (f_c, List.set_element i (VPat v) pat) 
  
(**
  Expects formatting-normal form.
*)
let match_safe_parsers (parsers: sym_defs) (concats: sym_defs) parsing_eqs facts p =

  let rec do_match facts = function 
    | (Let (VPat v, Sym (f_p, [e])) as s) :: p when Sym.Map.mem f_p parsers ->
      begin match safe_parse concats parsing_eqs facts f_p e with
        | Some (f_c, i) -> 
          Let (mk_pattern f_c (Sym.arity f_c) v i, e) :: do_match facts p
        | None -> 
          s :: do_match facts p
      end

    | Aux_test e :: p -> 
      Aux_test e :: do_match (facts @ [e]) p
      
    | Assume e :: p ->
      Assume e :: do_match (facts @ [e]) p 
      
    | s :: p -> s :: do_match facts p
                              
    | [] -> []
  in
  do_match facts p


let rec merge_patterns p =

  let merge vpat vpat' = 
    match vpat, vpat' with
      | VPat v, _ | _, VPat v  -> VPat v
      | Underscore, Underscore -> Underscore
      | _ -> failwith "merge_patterns: impossible"
  in

  let rec merge_pattern = List.map2 merge in
  
  let rec match_vars pat pat' =
    match pat, pat' with
      | VPat v :: pat, VPat v' :: pat' -> (v', Var v) :: match_vars pat pat'
      | _ :: pat, _ :: pat' -> match_vars pat pat'
      | [], [] -> []
      | _ -> failwith "match_vars: impossible"
  in

  let rec collect_pattern f pat e p = 
    match p with
    | Let (FPat (f', pat'), e') :: p when f = f' && e = e' ->
      let pat = merge_pattern pat pat' in
      let vs, vs' = List.split (match_vars pat pat') in 
      let p = Iml.subst vs vs' p in
      collect_pattern f pat e p
      
    | s :: p -> 
      let p, pat = collect_pattern f pat e p in
      s :: p, pat
     
    | [] -> [], pat
  in

  match p with 
    | Let (FPat (f, pat), e) :: p ->
      let p, pat = collect_pattern f pat e p in
      Let (FPat (f, pat), e) :: merge_patterns p
      
    | s :: p -> s :: merge_patterns p
      
    | [] -> [] 

(*************************************************)
(** {1 Regularity Properties} *)
(*************************************************)

let zero_fun_sym t = Fun ("Z" ^ Type.to_string t, 1) 
let zero_fun_prime_sym t = Fun ("Z" ^ Type.to_string t ^ "_prime", 1) 
let zero_sym t = Const ("zero_" ^ Type.to_string t)
      
(**
  Return the zero equations, zero function definitions and types 
  (including definitions and types for zero constants of fixed types).
  
  Generate the following equations:
  
    - for each conc : T1 x ... x Tn -> T
      ZT(conc(x1, ..., xn)) = ZT'(conc(ZT1(x1), ..., ZTn(xn)))
      
    - for each cast_T1_T2:
      ZT2(cast_T1_T2(x)) = ZT2'(cast_T1_T2(ZT1(x)))
      
    - for each fixed type T that occurs anywhere in argument types in fun_types:
      ZT(x) = Zero_t
*)
let zero_facts (concats: sym_defs) 
              (casts: (Type.t * Type.t) list) 
              (fun_types: Typing.fun_type_ctx): cvfact list * sym_defs * Typing.fun_type_ctx = 
              
  (* Types for which we need to generate ZT, ZT', and possibly Zero_t *)
  let zts: imltype list ref = ref [] in
  
  let zero_fun t =
    zts := t :: !zts;
    zero_fun_sym t  
  in

  (* Assume that zero_fun will be called for all of these, so no need to add to zts. *)
  let zero_fun_prime t = zero_fun_prime_sym t in
  
  let zero_of e t = Sym (zero_fun t, [e]) in
  
  (* Suitable for generating sym_defs and Typing.fun_type_ctx *)
  let z_fun_info t = 
    let zt = zero_fun_sym t in
    let zt' = zero_fun_prime_sym t in
    let zero_t = zero_sym t in
    [(zt,  Unknown), (zt,  ([t], t)); 
     (zt', Unknown), (zt', ([t], t));
     (zero_t, Unknown), (zero_t, ([], t))]
  in    
  
  let concat_fact c = 
    let ts, t = Sym.Map.find c fun_types in
    let args = mk_formal_args (Sym.arity c) |> List.map ~f:E.var in
    let zt = zero_fun t in
    let zt' = zero_fun_prime t in
    S.eq_bitstring [Sym (zt, [Sym (c, args)]); 
                   Sym (zt', [Sym (c, List.map2 zero_of args ts)])]
  in
  
  let cast_fact (t1, t2) =
    let sym = Cast (t1, t2) in
    let x = Var "x" in
    let zt2 = zero_fun t2 in
    let zt2' = zero_fun_prime t2 in
    S.eq_bitstring [Sym (zt2,  [Sym (sym, [x])]); 
                   Sym (zt2', [Sym (sym, [zero_of x t1])])]
  in 
  
  let const_fact t =
    let zt = zero_fun t in
    let zero_t = Sym (zero_sym t, []) in 
    let x = Var "x" in 
    S.eq_bitstring [Sym (zt, [x]); zero_t]
  in
  
  (*
    Remove information for symbols that are already present in the template 
    (such as the zero function in the definition of the encryption).
  *)
  let cleanup bindings = 
    List.filter (fun (sym, _) -> not (Sym.Map.mem sym fun_types)) bindings
  in
  
  let concat_facts = List.map concat_fact (Sym.Map.keys concats) in
  let cast_facts = List.map cast_fact casts in
  let fixed_types =
    Sym.Map.values fun_types
    |> List.concat_map ~f:(fun (ts, _) -> ts) 
    |> List.filter ~f:Type.has_fixed_length
    |> List.nub
  in
  let const_facts = List.map const_fact fixed_types in
  let z_defs, z_types = List.concat_map z_fun_info (List.nub !zts) |> List.split in
  let z_defs = cleanup z_defs |> Sym.Map.of_list in
  let z_types = cleanup z_types |> Sym.Map.of_list in
  let facts = List.map (CVFact.make (Sym.Map.disjoint_union [fun_types; z_types])) 
                       (concat_facts @ cast_facts @ const_facts) 
  in
  facts, z_defs, z_types

(********************************************************)
(** {1 Auxiliary Test Properties} *)
(********************************************************)

let prime = function
  | Fun (s, n) -> Fun (s ^ "_prime", n) 
  | sym -> fail "auxiliary_facts: impossible auxiliary symbol: %s" (Sym.to_string sym)
    
let add_auxiliary_primed auxiliary fun_types = 
  let auxiliary_primed = 
    Sym.Map.bindings auxiliary
    |> List.map ~f:(fun (sym, def) -> (prime sym, def))
    |> Sym.Map.of_list
  in 
  let types_primed =
    Sym.Map.bindings auxiliary
    |> List.map ~f:(fun (sym, _) -> (prime sym, Sym.Map.find sym fun_types))
    |> Sym.Map.of_list
  in
  Sym.Map.disjoint_union [auxiliary; auxiliary_primed], Sym.Map.disjoint_union [fun_types; types_primed] 
    
(*
  There are two ways to check 
    (len(x) = len(y)) => (def[x/arg] = def[y/arg]).
  
  The first way is to do length substitutions and then check syntactic equality. 
  One needs to expand lengths because of things like
    !(cast_to_int[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + cast_to_int[false,4,false,8](len55)))     
  
  The other way is to use the solver directly, but then you need to show overflow safety as well.
  When formalising, you need to replace auxiliary facts by hardened facts that check overflow safety.
  
  The second option is conceptually simpler, but less efficient.
  Another problem with the second option is that it is tricky to tell the solver to assume overflow
  safety for an expression. One cannot just extract the overflow safety fact, because that itself
  may not be overflow safe. For these reasons I'm using the first option now.
*)
let auxiliary_facts (concats: sym_defs) (auxiliary: sym_defs) (fun_types: Typing.fun_type_ctx): cvfact list =

  (* facts for a single auxiliary test *)
  let facts sym def arg_types = 

    let num_args = List.length arg_types in
    
    let zero_of v t = Sym (zero_fun_sym t, [Var v]) in
  
    let rec replace_len v = function
      | Len (Var v') when v' = v -> Var (Var.fresh "len") 
      | e -> E.descend (replace_len v) e
    in

    let rec expand_lens = function
      | Len (Concat es) -> 
        List.map E.len es |> E.sum |> expand_lens
      | e -> E.descend expand_lens e
    in

    let can_erase arg =
      let x = Var (Var.fresh "x") in
      let y = Var (Var.fresh "y") in
      let def = replace_len arg def in
      let def_x = E.subst [arg] [x] def in
      let def_y = E.subst [arg] [y] def in
      debug "can_erase: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
      def_x = def_y
    in
  
    let concat_pairs arg =
      let pair c = 
        match Sym.Map.maybe_find c fun_types with
          | Some (ts, t') (* when t = t' *) -> 
            let c_def = Sym.Map.find c concats in

            (* Rename args of c_def to avoid collision with args of def. *)
            let c_args = List.map (fun _ -> Var.fresh "c_arg") (1 -- (Sym.arity c)) in
            let c_def = E.subst_v (mk_formal_args (Sym.arity c)) c_args c_def in
            (* For simplifcation. *) 
            S.add_fact (S.is_defined c_def);

            let def = 
              E.subst [arg] [c_def] def 
                (* We may be substituting an encoder inside a parser, so we need to simplify. *)
              |> Simplify.full_simplify
                (* Deal with stuff like 
                   !(cast_to_int[false,4,false,8](len("p"|len54|x92|x93)) <= (i5 + cast_to_int[false,4,false,8](len55))) 
                *)
              |> expand_lens 
                (* Replace all argument lengths by fresh variables *)
              |> List.fold_right replace_len c_args 
            in
                
            let xs = List.map (fun _ -> Var.fresh "x") (1 -- (Sym.arity c)) in
            let ys = List.map (fun _ -> Var.fresh "y") (1 -- (Sym.arity c)) in
            let def_x = E.subst_v c_args xs def in
            let def_y = E.subst_v c_args ys def in
            debug "concat_pairs: comparing \n%s and \n%s" (E.to_string def_x) (E.to_string def_y);
            if def_x = def_y then
                let zxs = List.map2 zero_of xs ts in
                let xs = List.map E.var xs in
                Some (Typing.cast t' Bitstring (Sym (c, xs)), 
                      Typing.cast t' Bitstring (Sym (c, zxs)))
            else None
          | _ -> None
      in
      List.filter_map pair (Sym.Map.keys concats)
     in 
        
    let rec arg_pairs xs ts: (exp * exp) list list =
      match xs, ts with
        | [], [] -> [[]]
        | x :: xs, t :: ts when can_erase x ->
          List.map (fun args -> (Var x, zero_of x t) :: args) (arg_pairs xs ts)
        | x :: xs, t :: ts ->
          let pairs = (Var x, Var x) :: concat_pairs x in
          List.cross_product (fun pair args -> pair :: args) pairs (arg_pairs xs ts)
        | _ -> fail "arg_pairs: impossible"
    in
    
    let mk_fact (args1, args2) =
      S.eq_bitstring [Sym (sym, args1); Sym (prime sym, args2)] |> CVFact.make fun_types
    in
  
    arg_pairs (mk_formal_args num_args) arg_types
      (* remove trivial equations *)
    |> List.map ~f:List.split 
    |> List.filter ~f:(fun (args1, args2) -> args1 <> args2)
    |> List.map ~f:mk_fact 
  in
  
  S.reset_facts ();
  Sym.Map.bindings auxiliary
  |> List.concat_map ~f:(fun (sym, def) -> 
    debug "Auxiliary facts: checking %s: %s" (Sym.to_string sym) (E.to_string def);
    let (ts, _) = Sym.Map.find sym fun_types in
    facts sym def ts)


(*************************************************)
(** {1 Input and Output Merging} *)
(*************************************************)

let merge_in_out p =

  let rec merge_in (vs: var list) p = 
  match (vs, p) with
    | vs, In [v] :: p -> merge_in (v :: vs) p
    | [], s :: p -> s :: merge_in [] p
    | vs, (Out _ as s) :: p ->
      In vs :: s :: merge_in [] p 
    | vs, s :: p -> s :: merge_in vs p
    | vs, [] -> [In vs] (* including vs =  [] *)
  in

  (*
    Requires only-variables-in-write form.
  *)
  let rec merge_out es p = 
  match (es, p) with
    | es, Out [e] :: p -> merge_out (e :: es) p
    | [], s :: p -> s :: merge_out [] p
    | es, (In _ as s) :: p ->
      Out es :: s :: merge_out [] p 
    | es, s :: p -> s :: merge_out es p
    | [], [] -> [Yield] 
    | es, [] -> [Out es]
  in
      
  List.rev (merge_in [] (List.rev (merge_out [] p)))  

(*************************************************)
(** {1 The full model} *)
(*************************************************)

module Model = struct
  type t = {
    client: iml;
    server: iml;
    constants: exp Var.Map.t;
    template: Template.t;
    var_types: Typing.type_ctx;
    fun_types: Typing.fun_type_ctx;
    
    concats: sym_defs;
    parsers: sym_defs;
    arith: sym_defs;
    auxiliary: sym_defs;
    zero_funs: sym_defs;
    
    auxiliary_facts: cvfact list;
    zero_facts: cvfact list;
    parsing_eqs: parsing_eq list;
    encoder_facts: encoder_fact list;
  }
end
  
open Model

(*************************************************)
(** {1 CV Output} *)
(*************************************************)

let printf a = fprintf Common.out_channel a

let show_cVStmt: Stmt.t -> string = fun s ->

  let rec show_exp_body : exp -> string = function 
    | Var v -> v
    | Sym (Const s, []) -> s
    | Sym (s, es) ->
      Sym.to_string s ^ "(" ^ String.concat ", " (List.map show_exp_body es) ^ ")"
    | Annotation (_, e) -> show_exp_body e
    | e -> "unexpected{" ^ E.dump e ^ "}"

  and show_in_var t name = name ^ ": " ^ Type.to_string t
  in

  match s with
    | In [v] -> 
      "in(c_in, " ^ show_in_var Bitstring v ^ ");";
    
    | In vs -> 
      "in(c_in, (" ^ String.concat ", " (List.map (show_in_var Bitstring) vs) ^ "));";

    | New (v, t) -> 
      "new " ^ show_in_var t v ^ ";";

    | Out [e] -> 
      "out(c_out, " ^ show_exp_body e ^ ");";

    | Out es -> 
      "out(c_out, (" ^ String.concat ", " (List.map show_exp_body es) ^ "));";

    | Test_eq (e1, e2) ->
      "if " ^ show_exp_body e1 ^ " = " ^ show_exp_body e2 ^ " then "

    | Aux_test e ->
      "if " ^ show_exp_body e ^ " then "

    | Assume e ->
      Printf.sprintf "assume %s in" (show_exp_body e)

    | Test e ->
      "if " ^ show_exp_body e ^ " then "
                                                
    | Event (name, es) -> 
      "event " ^ name ^ "(" ^ String.concat ", " (List.map show_exp_body es) ^ ");"
        
    | Let (pat, e) ->
      "let " ^ Pat.dump pat ^ " = " ^ show_exp_body e ^ " in"
      
    | Yield -> "yield ."
      
    | Comment s -> sprintf "(* %s *)" s 

let show_cVProcess p =
  let zero = 
    if p = [] then " 0 .\n" else
    match List.last p with
      | Yield -> "\n"
      | _ -> " 0 .\n"
  in
  let result = String.concat "\n" (List.map show_cVStmt p) ^ zero in
  result

let print_indent s = print_endline ("  " ^ s)

(*
  FIXME: we aren't even printing the parsing rules, are we?
*)
let write_cV model =

  let casts = List.nub (Typing.casts model.client @ Typing.casts model.server) in

  let print_fun_def is_injective sym def =
    if def <> Unknown then 
      print_endline ("(* " ^ show_fun sym def ^ " *)");
    let compos = if is_injective then " [compos]." else "." in
    match sym with
      | Const s -> 
        let _, t = Sym.Map.find sym model.fun_types in
        print_endline ("const " ^ s ^ ": " ^ Type.to_string t ^ ".");
        print_endline ""
      | sym -> 
        print_endline ("fun " ^ Sym.cv_declaration sym (Sym.Map.find sym model.fun_types) ^ compos);
        print_endline ""
  in
    
  let print_concat sym def =
    print_fun_def (is_injective_concat sym def) sym def;
  in
  
	let print_cast: imltype * imltype -> unit = fun (t, t') ->
	  print_endline ("fun " ^ Sym.to_string (Cast (t, t')) ^ "(" ^ Type.to_string t ^ "): " ^ Type.to_string t' ^ " [compos].")
  in

  (* TODO: most of these can now be printed by converting to CVFacts *)  
  let print_cast_eq: imltype * imltype -> unit = fun (t, t') ->
    (* check that the inverse function is defined at all *)
    if List.mem (t', t) casts && Type.subtype t t' then 
    begin
      print_endline ("forall x: " ^ Type.to_string t ^ ";");
      print_endline ("  " ^ Sym.to_string (Cast (t', t)) ^ "(" ^ Sym.to_string (Cast (t, t')) ^ "(x)) = x.")
    end
  in
  
  let print_constant name def =
    let t = Var.Map.find name model.var_types in 
    print_endline ("(* " ^ E.dump def ^ " *)");
    print_endline ("const " ^ name ^ ": " ^ Type.to_string t ^ ".") 
  in

  let print_relation c1 c2 op =
    try
    begin    
        let id = ref 0 in
    
        let formal_arg: imltype -> string = fun _ -> id := !id + 1; "var" ^ string_of_int !id in
        let show_arg: string -> imltype -> string = fun v t -> v ^ ": " ^ Type.to_string t in
    
        let (arg_types1, t1) = Sym.Map.find c1 model.fun_types in
        let (arg_types2, t2) = Sym.Map.find c2 model.fun_types in
    
        (* FIXME: should this be made part of transformations? *)
        if t1 = t2 && (op = "<>" || arg_types1 = arg_types2) then
        begin
            let args1 = List.map formal_arg arg_types1 in
            let args2 = 
              if op = "<>" then List.map formal_arg arg_types2 
              else args1 
            in
            let all_args = List.nub (List.map2 show_arg args1 arg_types1 @ List.map2 show_arg args2 arg_types2) in
            
            printf "forall %s;\n" (String.concat ", " all_args); 
            printf "  %s(%s) %s %s(%s).\n\n" 
              (Sym.to_string c1) (String.concat ", " args1) 
              op
              (Sym.to_string c2) (String.concat ", " args2);
        end
    end with Not_found -> ()
  in  

  let print_encoder_fact = function
    | Disjoint (s, s') -> print_relation s s' "<>"
    | Equal    (s, s') -> print_relation s s' "="
  in
  
  let print_cv_fact fact = print_endline (CVFact.to_string fact) in

  let client_proc = show_cVProcess model.client in
  let server_proc = show_cVProcess model.server in

  List.iter print_endline (Template.crypto model.template);

  print_endline "\n(*************************** \n Constants \n***************************)\n";
  Var.Map.iter print_constant model.constants;

  print_endline "\n(*************************** \n  Formatting Functions \n***************************)\n";
  Sym.Map.iter print_concat model.concats;
  Sym.Map.iter (print_fun_def false) model.parsers;
  print_endline "";
  List.iter print_encoder_fact model.encoder_facts;

  print_endline "\n(*************************** \n  Arithmetic Functions \n***************************)\n";
  Sym.Map.iter (print_fun_def false) model.arith;

  print_endline "\n(*************************** \n  Auxiliary Tests \n***************************)\n";
  Sym.Map.iter (print_fun_def false) model.auxiliary;

  print_endline "\n(*************************** \n  Zero Functions \n***************************)\n";
  Sym.Map.iter (print_fun_def false) model.zero_funs; 

  print_endline "\n(*************************** \n  Typecasting \n***************************)\n";
  List.iter print_cast casts;
  List.iter print_cast_eq casts; 

  print_endline "\n(*************************** \n  Auxiliary Facts \n***************************)\n";
  List.iter print_cv_fact model.auxiliary_facts;

  print_endline "\n(*************************** \n  Zero Facts \n***************************)\n";
  List.iter print_cv_fact model.zero_facts;
  
  print_endline "";

  List.iter print_endline (Template.crypto2 model.template);
  List.iter print_endline (Template.query model.template);
  
  print_endline "\n(*************************** \n  Model \n***************************)\n";
  print_endline "let client = ";
  print_endline client_proc;
  print_endline "let server = ";
  print_endline server_proc;

  List.iter print_endline (Template.envp model.template)
  
(*************************************************)
(** {1 Main} *)
(*************************************************)

let verbose = true

let rec remove_casts = function
  | Sym (Op (Sym.Op.T.Cast_to_int, _), [e]) -> remove_casts e
  | e -> E.descend remove_casts e

let debug_iML client server title = 
  if verbose then prerr_title title;
  if verbose then prerr_endline "Client = ";
  if verbose then prerr_endline (Iml.to_string client);
  if verbose then prerr_endline "Server = ";
  if verbose then prerr_endline (Iml.to_string server)
 
let setup_debug () =
  set_debug (fun labels ->
    let at_most_n_under n l =
      match List.find_index ((=) l) labels with
      | None -> false
      | Some i -> i <= n
    in
       at_most_n_under (-1) "Typing.check"
    || at_most_n_under (-1) "Typing.check_robust_safety"  
    || at_most_n_under (-1) "parsing_eqs"
    || at_most_n_under 0 "auxiliary_facts"
    || false) 
    
let main () = 

  setup_debug ();

  let (client, server) = Symex.raw_in (open_in_bin Sys.argv.(1)) in

  let server = server |> remove_comments |> rewrite_crypto in
  let client = client |> remove_comments |> rewrite_crypto in

  debug_iML client server "initial IML";

  let server = remove_trailing_computations server in
  let client = remove_trailing_computations client in
  debug_iML client server "IML after removing trailing computations";

  let server = normal_form server in
  let client = normal_form client in
  debug_iML client server "IML in normal form";

  let server = simplify_double_lets server in
  let client = simplify_double_lets client in
  debug_iML client server "IML after simplifying double lets";

  let client = apply_name_annotations client in
  let server = apply_name_annotations server in
  debug_iML client server "IML after applying all name annotations";

  let client, client_concats = extract_concats client in
  let server, server_concats = extract_concats server in
  let concats = Sym.Map.disjoint_union [client_concats; server_concats] in

  debug_iML client server "IML after concat extraction";
  if verbose then show_funs concats;
 
  let client, client_parsers = extract_parsers client in
  let server, server_parsers = extract_parsers server in
  let parsers = Sym.Map.disjoint_union [client_parsers; server_parsers] in

  debug_iML client server "IML after parser extraction";
  if verbose then show_funs parsers;

  let server, server_arith = extract_arithmetic server in
  let client, client_arith = extract_arithmetic client in
  let arith = Sym.Map.disjoint_union [server_arith; client_arith] in
  debug_iML client server "IML after replacing arithmetic expressions";
  if verbose then show_funs arith;

  let server, server_auxiliary = extract_auxiliary server in
  let client, client_auxiliary = extract_auxiliary client in
  let auxiliary = Sym.Map.disjoint_union [server_auxiliary; client_auxiliary] in
  debug_iML client server "IML after adding formal versions of auxiliary tests";

  let client, client_constants = extract_constants concats client in
  let server, server_constants = extract_constants concats server in
  let constants = Var.Map.disjoint_union [server_constants; client_constants] in
  debug_iML client server "IML after constant extraction";

  let concats = cleanup_defs (client @ server) concats in
  let parsers = cleanup_defs (client @ server) parsers in
  
  (************************
    Typechecking
  *************************)
  
  let template = Template.read_file ~cv_lib_name:Sys.argv.(2) ~name:Sys.argv.(3) in
  let template_var_types, fun_types = Template.collect_types template in
  prerr_title "Template Function Types: ";
  Typing.dump_fun_types fun_types;
  prerr_title "Template Variable Types: ";
  Typing.dump_types template_var_types;
  
  let inferred_var_types = Typing.merge [Typing.infer fun_types client; Typing.infer fun_types server] in
  prerr_title "Inferred Variable Types";
  Typing.dump_types inferred_var_types;
  let var_types = Typing.merge [template_var_types; inferred_var_types] in 
  
  let client_formatter_types = Typing.derive_unknown_types fun_types var_types client in
  let server_formatter_types = Typing.derive_unknown_types fun_types var_types server in
  
  let defs = Sym.Map.disjoint_union [concats; parsers; auxiliary; arith] in
  Typing.check_missing_types defs ~template_types:fun_types ~inferred_types:client_formatter_types client;
  Typing.check_missing_types defs ~template_types:fun_types ~inferred_types:server_formatter_types server;

  prerr_title "Inferred Client Types";
  Typing.dump_fun_types client_formatter_types;

  prerr_title "Inferred Server Types";
  Typing.dump_fun_types server_formatter_types;
      
  let fun_types = Typing.merge_fun_types [fun_types; client_formatter_types; server_formatter_types] in

  let client = with_debug "Typing.check" (Typing.check defs fun_types template_var_types []) client in 
  let server = with_debug "Typing.check" (Typing.check defs fun_types template_var_types []) server in
  
  debug_iML client server "IML after typechecking";

  with_debug "Typing.check_robust_safety" (Typing.check_robust_safety concats) fun_types;

  (************************
    Formatting facts
  *************************)

  let parsing_eqs = with_debug "parsing_eqs" (compute_parsing_rules fun_types parsers) concats in
  
  prerr_title "Parsing Equations";
  List.iter (fun eq -> prerr_endline (show_parsing_eq ~fun_types concats eq)) parsing_eqs;
  
  let parsers = cleanup_defs (client @ server) parsers in
  let parsing_eqs = cleanup_parsing_eqs (client @ server) parsing_eqs in
  
  let encoder_facts = encoder_facts (Sym.Map.bindings concats) in
  
  (************************
    Pattern matching
  *************************)

  let client = match_inverse client in
  let server = match_inverse server in

  let client = match_safe_parsers parsers concats parsing_eqs [] client in
  let server = match_safe_parsers parsers concats parsing_eqs [] server in

  let client = merge_patterns client in
  let server = merge_patterns server in
  
  debug_iML client server "IML after inserting pattern matching";

  (********************************************
    Bring the process into IO-alternating form
  *********************************************)

  let client = merge_in_out client in
  let server = merge_in_out server in

  debug_iML client server "IML after merging inputs and outputs";

  (************************
    Auxiliary tests
  *************************)

  let auxiliary_facts = with_debug "auxiliary_facts" (auxiliary_facts concats auxiliary) fun_types in
  let auxiliary, fun_types = add_auxiliary_primed auxiliary fun_types in
  let client = remove_auxiliary client in
  let server = remove_auxiliary server in
  debug_iML client server "IML after removing auxiliary ifs";

  (************************
    Zero facts
  *************************)

  let casts = List.nub (Typing.casts client @ Typing.casts server) in
  let zero_facts, zero_funs, zero_types = zero_facts concats casts fun_types in 
  let fun_types = Sym.Map.disjoint_union [fun_types; zero_types] in

  write_cV {
    client; server;
    template;
    constants;
    var_types; 
    fun_types; 
    parsers; 
    concats; 
    arith; 
    auxiliary;
    zero_funs;
    auxiliary_facts;
    zero_facts; 
    parsing_eqs; 
    encoder_facts }


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

