(* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 * Copyright (c) 2010-2011, Mihhail Aizatulin (avatar@hot.ee)
 *
 * See LICENSE file for copyright notice.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 *)

(*
  Changes by Misha (OUTDATED):
  
    - Store and Load now also supply the sizeof() the stored/loaded variable
    
    - HandleReturn and ClearFrame (renamed from ClearStack) now get the number
      of function parameters, so that calling a function works even when the stack is not empty.
      
    - Return now gets a bool indicating whether the returned value is symbolic (false if void).
    
    - Call now also supplies the name and the address of the function.
      
    - A new function Invoke() is inserted right before a call and given the called function address.
*)

open Cil
open Formatcil

module E = Errormsg

open List

open Common

(*************************************************)
(** {1 State} *)
(*************************************************)

let opaqueWrappers : StrSet.t ref = ref StrSet.empty

let idCount = ref 0

(*************************************************)
(** {1 General Purpose} *)
(*************************************************)

let isSome o =
  match o with
    | Some _ -> true
    | None   -> false

let concatMap f ls =
  let rec doIt res ls =
    match ls with
      | [] -> List.rev res
      | (x::xs) -> doIt (List.rev_append (f x) res) xs
  in
    doIt [] ls
  

(*************************************************)
(** {1 Helpers} *)
(*************************************************)

(* this initialises typeOfSizeOf *)
let _ = initCIL ()


let getNewId () = ((idCount := !idCount + 1); !idCount)

let noAddr = zero

let shouldSkipFunction f = hasAttribute "crest_skip" f.vattr

let prependToBlock (is : instr list) (b : block) =
  b.bstmts <- mkStmt (Instr is) :: b.bstmts

(* These definitions must match those in "libcrest/crest.h". *)
let idType   = intType
let bidType  = intType
let fidType  = uintType
let valType  = TInt (ILongLong, [])
let chrType  = TInt (IChar, [])
let addrType = TInt (IULong, [])
let sizeType = !typeOfSizeOf
let boolType = TInt (IUChar, [])
let opType   = intType  (* enum *)
let strType  = charConstPtrType
(* A generic function pointer *)
let funPtrType = cType "void (*)()" []


let checkHasAddress (_, off) = 
  let rec containsBitField off =
    match off with
      | NoOffset         -> false
      | Field (fi, off) -> (isSome fi.fbitfield) || (containsBitField off)
      | Index (_, off)  -> containsBitField off
  in
    if not (containsBitField off) then ()
    else 
      E.error "bitfields not supported"

let funReturnType : typ -> typ = function
	| TFun (t, _, _, _) -> t
	| _ -> failwith "funReturnType: not a function"

let isVoidFunType : typ -> bool = function
	| TFun (TVoid _, _, _, _) -> true
	| _ -> false

let isVarargFunType : typ -> bool = function
	| TFun (_, _, true, _) -> true
	| _ -> false  

let opaque : varinfo -> varinfo = fun v ->
  { v with vname = "__crest_" ^ v.vname ^ "_opaque"; vstorage = Static } 

let needsOpaqueWrapper : varinfo -> bool = fun v ->
     isOpaque v && isFunctionType v.vtype 
  && not (isProxied v)
  && not (isVarargFunType v.vtype)

(*************************************************)
(** {1 Visitors} *)
(*************************************************)

class crestInstrumentVisitor f =
  (*
   * Get handles to the instrumentation functions.
   *
   * NOTE: If the file we are instrumenting includes "crest.h", this
   * code will grab the varinfo's from the included declarations.
   * Otherwise, it will create declarations for these functions.
   *)
  (* let bidArg  = ("bid",  bidType,  []) in *)
  (* let fidArg  = ("fid",  fidType,  []) in *)
  (* let idArg  = ("id",  idType,  []) in *)  
  let valArg  = ("val",  valType,  []) in
  (* let numArg  = ("num",  valType,  []) in *)
  (* let addrArg = ("addr", addrType, []) in *)
  (* let sizeArg = ("size", sizeType, []) in *)
  let opArg   = ("op",   strType,   []) in
  let boolArg = ("b",    boolType, []) in
  let nameArg = ("name", strType,  []) in
  let strArg  = ("strVal", strType,  []) in
  let chrArg  = ("chrVal", chrType,  []) in
  let funPtrArg = ("funPtr", funPtrType, []) in

  let mkInstFunc name args =
    let ty = TFun (voidType, Some args, false, []) in
    let func = findOrCreateFunc f ("__Crest" ^ name) ty in
      func.vstorage <- Extern ;
      func.vattr <- [Attr ("crest_skip", [])] ;
      func
  in
  
  let initFunc : string -> varinfo = fun name ->
    let f = makeGlobalVar ("__crest_" ^ name ^ "_init") (cType "void ()()" []) in
    {f with vstorage = Extern}
  in

  let invokeFunc      = mkInstFunc "Invoke" [funPtrArg] in
  (* let loadFunc         = mkInstFunc "Load"  [addrArg; sizeArg; valArg] in *)
  (* let storeFunc        = mkInstFunc "Store" [addrArg; sizeArg] in *)
  (* let clearFrameFunc   = mkInstFunc "ClearFrame" [numArg] in *)
  let clearFunc        = mkInstFunc "Clear" [valArg] in
  (* let apply1Func       = mkInstFunc "Apply1" [opArg; valArg] in
  let apply2Func       = mkInstFunc "Apply2" [opArg; valArg] in *)
  let applyNFunc       = mkInstFunc "ApplyN" [opArg; valArg] in
  let simplifyFunc     = mkInstFunc "Simplify" [valArg] in
  let muteFunc         = mkInstFunc "Mute" [] in
  let unmuteFunc       = mkInstFunc "Unmute" [] in
  let nondetFunc       = mkInstFunc "Nondet" [] in
  let branchFunc       = mkInstFunc "Branch" [boolArg] in
  let callFunc         = mkInstFunc "Call" [nameArg; funPtrArg] in
  let returnFunc       = mkInstFunc "Return" [boolArg] in
  (* let handleReturnFunc = mkInstFunc "HandleReturn" [valArg; numArg] in *)
  let storeFunc        = mkInstFunc "Store" [] in
  let loadIntFunc      = mkInstFunc "LoadInt" [valArg] in
  let loadMemFunc      = mkInstFunc "LoadMem" [] in
  let loadCStringFunc  = mkInstFunc "LoadCString" [strArg] in
  let loadStringFunc   = mkInstFunc "LoadString" [strArg] in
  let loadCharFunc     = mkInstFunc "LoadChar" [chrArg] in
  let loadTypeSizeFunc = mkInstFunc "LoadTypeSize" [strArg] in
  let setLenFunc       = mkInstFunc "SetLen" [] in
  let setPtrStepFunc   = mkInstFunc "SetPtrStep" [] in
  let loadStackPtrFunc = mkInstFunc "LoadStackPtr" [nameArg] in
  let fieldOffsetFunc  = mkInstFunc "FieldOffset" [strArg] in
  let indexOffsetFunc  = mkInstFunc "IndexOffset" [] in
  let locationFunc     = mkInstFunc "Location" [strArg] in
  let doneFunc         = mkInstFunc "Done" [] in

  (*
   * Functions to create calls to the above instrumentation functions.
   *)
  let mkInstCall func args =
    let args' = args in
      Call (None, Lval (var func), args', locUnknown)
  in

  (* FIXME: Use strings straight away *)
  let unaryOpCode = function
    | Neg -> "-"  | BNot -> "~"  |  LNot -> "!"
  in

  let binaryOpCode = function
    | PlusA   -> "+"   | MinusA  ->  "-"   | Mult  -> "*"    | Div   -> "/"
    | Mod     -> "%"   | BAnd    ->  "&"   | BOr   -> "BOR"  | BXor  -> "^"
    | Shiftlt -> "<<"  | Shiftrt ->  ">>"  | LAnd  -> "&&"   | LOr   -> "LOR"
    | Eq      -> "=="  | Ne      ->  "!="  | Gt    -> ">"    | Le    -> "<="
    | Lt      -> "<"   | Ge      ->  ">="

    | PlusPI  -> "PlusPI"
    | IndexPI -> "PlusPI" (* sic *)
    | MinusPI -> "MinusPI"
    | MinusPP -> "MinusPP"
  in

  (* let toAddress e = CastE (addrType, e) in *)

  (* let addressOf e = toAddress (mkAddrOrStartOf e) in *)

  let toValue e =
      if isPointerType (typeOf e) then
        CastE (valType, CastE (addrType, e))
      else
        CastE (valType, e)
  in

  (* let sizeOf addr =
    match isInteger addr with
      | None    -> SizeOfE (Lval (mkMem addr NoOffset));
      | Some 0L -> integer 0
      | _       -> failwith "sizeOf: unexpected argument"
  in *)
  
  let mkFunAddr : varinfo -> exp = fun f ->
    mkCast (mkAddrOf (Var f, NoOffset)) funPtrType
  in

  (* let mkInvoke f               = mkInstCall invokeFunc [mkFunAddr f] in *)
  (* let mkLoad addr value        = mkInstCall loadFunc [toAddr addr; sizeOf addr; toValue value] in *)
  (* let mkStore addr             = mkInstCall storeFunc [toAddr addr; sizeOf addr] in *)
  (* let mkClearFrame num         = mkInstCall clearFrameFunc [integer num] in *)
  let mkClear num              = mkInstCall clearFunc [integer num] in
  (* let mkApply1 op value        = mkInstCall apply1Func [mkString op; toValue value] in
  let mkApply2 op value        = mkInstCall apply2Func [mkString op; toValue value] in *)
  let mkApplyN f n             = mkInstCall applyNFunc [mkString f; integer n] in
  let mkSimplify value         = mkInstCall simplifyFunc [toValue value] in
  let mkMute ()                = mkInstCall muteFunc [] in
  let mkUnmute ()              = mkInstCall unmuteFunc [] in
  let mkNondet ()              = mkInstCall nondetFunc [] in
  let mkBranch b               = mkInstCall branchFunc [integer b] in
  let mkCall f                 = mkInstCall callFunc 
                                 [mkString f.vname; mkFunAddr f] in
  (* FIXME: isSym is obsolete where everything is symbolic - but still need a void indication? *)
  let mkReturn b               = mkInstCall returnFunc [integer b] in
  (* let mkHandleReturn value num = mkInstCall handleReturnFunc [toValue value; integer num] in *)
  let mkStore ()               = mkInstCall storeFunc [] in
  let mkLoadInt value          = mkInstCall loadIntFunc [toValue value] in
  let mkLoadMem ()             = mkInstCall loadMemFunc [] in
  let mkLoadCString s          = mkInstCall loadCStringFunc [mkString s] in
  let mkLoadString s           = mkInstCall loadStringFunc [mkString s] in
  let mkLoadChar c             = mkInstCall loadCharFunc [Const (CChr c)] in
  let mkLoadTypeSize s         = mkInstCall loadTypeSizeFunc [mkString s] in
  let mkSetLen ()              = mkInstCall setLenFunc [] in
  let mkSetPtrStep ()          = mkInstCall setPtrStepFunc [] in
  let mkLoadStackPtr name      = mkInstCall loadStackPtrFunc [mkString name] in
  let mkFieldOffset f          = mkInstCall fieldOffsetFunc [mkString (f.fname)] in
  let mkIndexOffset ()         = mkInstCall indexOffsetFunc [] in 
  let mkLocation l             = mkInstCall locationFunc [mkString (Pretty.sprint 100 (d_loc () l))] in   
  let mkInit v                 = mkInstCall invokeFunc [mkFunAddr (initFunc v.vname)] in
  let mkDone ()                = mkInstCall doneFunc [] in

  let mkRef v = mkLoadStackPtr (mkUniqueName v) in

  (* FIXME: CIL only knows about machine-dependent integer kinds? Yep, so keep thinking. *)
  (** This one doesn't set length of sizeOf, but it can be done extra if needed *)
  let rec instrumentSizeOf : typ -> instr list = function
    | TPtr _ -> [mkApplyN "ptrLen" 0]
    | t -> match sizeOf t with
	      | Const (CInt64 _) as c -> [mkLoadInt c] 
	      | SizeOf t'             -> [mkLoadTypeSize (Pretty.sprint 100 (d_typsig () (typeSig t)))]
	      | _                     -> E.s (error "instrumentSizeOf: unexpected sizeOf result")
  
  (** FIXME: not sound, switch to the symbolic version. *)
  (* let rec instrumentSizeOf : typ -> instr list = function t -> [mkLoadInt (SizeOf t)] *)
  
  and setLen : typ -> instr list = function t ->
    (instrumentSizeOf t) @ [mkSetLen ()]
  
  (** 
	  Takes the pointer type, not the base type.
	  Silently does nothing if not a pointer.
   *)
  and setPtrStep : typ -> instr list = function
    | TPtr (t, _) -> (instrumentSizeOf t) @ [mkSetPtrStep ()]
    | _           -> []

  and instrumentConst : constant -> instr list = function
    | CInt64 _ as c -> [mkLoadInt (Const c)] @ (setLen (typeOf (Const c)))
    | CStr   s      -> [mkLoadCString s]
    | CChr   c      -> [mkLoadChar c]
    | CWStr  _      -> E.s (error "instrumentConst: wide character strings not supported")
    | CReal  _      -> E.s (error "instrumentConst: reals not supported")
    | CEnum  _      -> E.s (error "instrumentConst: enums temporarily not supported")

  and instrumentLval' (host, offset) =

	  let instrumentHost : lhost -> instr list = function 
 		    | Var v -> [mkRef v] 
		    | Mem e -> instrumentExpr e 
	  in
    
	  let rec instrumentOffset : typ -> offset -> instr list = fun t o ->
       
      let setStep : typ -> instr list = fun t -> (instrumentSizeOf t) @ [mkSetPtrStep ()] in

	    let extendType : typ -> offset -> typ = fun t -> function
	      | NoOffset -> t
	      | Field (f, _) -> typeOffset t (Field (f, NoOffset))
	      | Index (e, _) -> typeOffset t (Index (e, NoOffset))
	    in
	    
	    let t' = extendType t o in
      setStep t @
	    match o with
	        | NoOffset      -> []
	        | Field (f, o') -> [mkFieldOffset f] @ (instrumentOffset t' o')
	        | Index (e, o') -> (instrumentExpr e) @ [mkIndexOffset ()] @ (instrumentOffset t' o')

    in
    (instrumentHost host) @ (instrumentOffset (typeOfLval (host, NoOffset)) offset)

  and initHost : lhost -> instr list = function
    | Var v when v.vglob && not (isFunctionType v.vtype) -> 
      if isOpaque v then
        let host = (Var v, NoOffset) in
        [mkApplyN v.vname 0] @ (setLen (typeOfLval host)) @ (instrumentLval' host) @ [mkStore ()]
      else
        [mkInit v]
    | _ -> []

  and instrumentLval (host, offset) = (initHost host) @ instrumentLval' (host, offset)

  and instrumentCast : typ -> instr list = fun t ->
    let castOp = if isPointerType t then "castToPtr" else "castToInt" in
    [mkLoadString (Pretty.sprint 500 (d_typsig () (typeSig t))); mkApplyN castOp 2]

  (*
   * Instrument an expression.
   *)
  and instrumentExpr e = 
    match e with
      | Const c -> 
          instrumentConst c
  
      | Lval lv ->
          checkHasAddress lv;
          (instrumentLval lv) @ [mkLoadMem ()]
  
      | SizeOf t ->
          instrumentSizeOf t @ (setLen (!typeOfSizeOf))
          
      | SizeOfE e ->
          instrumentSizeOf (typeOf e) @ (setLen (!typeOfSizeOf))
  
      | SizeOfStr s ->
          [mkLoadInt (integer (String.length s))] @ (setLen (!typeOfSizeOf))
  
      | UnOp (op, e, t) ->
          (instrumentExpr e) @ [mkApplyN (unaryOpCode op) 1; mkSimplify e] @ (setLen t) @ [mkDone ()]
  
      | BinOp (op, e1, e2, t) ->
          (instrumentExpr e1) @ (instrumentExpr e2) @ [mkApplyN (binaryOpCode op) 2; mkSimplify e] @ (setLen t) @ [mkDone ()]
  
      | CastE (t, e) ->
        if isPointerType t && isZero e then
          [mkLoadStackPtr "nullPtr"] @ (setPtrStep t)
        (* else if isPointerType t && not (isPointerType (typeOf e)) then
          E.s (error "instrumentExpr: cast to pointer of non-zero expression") *)
        else
          instrumentExpr e @ instrumentCast t @ [mkSimplify e] @ (setLen t) @ (setPtrStep t) @ [mkDone ()] 
 
      | AddrOf lv ->
          (instrumentLval lv)
          
      | StartOf lv ->
          (instrumentLval (addOffsetLval (Index (zero, NoOffset)) lv))
  
      | (AlignOf _ | AlignOfE _) -> E.s (error "instrumentExpr: __alignof_ not supported")

  and instrumentAssignment : lval -> exp -> instr list = fun lv e ->
    (instrumentExpr e) @ (instrumentLval lv) @ [mkStore ()]

  and instrumentInit : varinfo -> init -> instr list = fun v init -> 
    let rec instr : lval -> init -> instr list = fun lv -> function
      | SingleInit e -> instrumentAssignment lv e
      | CompoundInit (_, inits) -> concat (map (function (o, i) -> instr (addOffsetLval o lv) i) inits)
    in
    instr (Var v, NoOffset) init 

  and instrumentResult : typ -> string -> exp list -> instr list = fun t fname args ->
	  if isVoidType t then
	    [mkClear (length args)]
	  else if isPointerType t then
	    [mkClear (length args); mkLoadStackPtr (fname ^ "()"); mkNondet ()] @ (setPtrStep t)
	  else
	    [mkApplyN (fname ^ "()") (length args); mkNondet ()] @ (setLen t)

  in 
  let opaqueWrapper : varinfo -> global list = fun v ->
    
	  if StrSet.mem v.vname !opaqueWrappers then []
	  else 
	  begin
	    opaqueWrappers := StrSet.add v.vname !opaqueWrappers;
    
	    let nameFormal : varinfo -> varinfo = fun v ->
	      if v.vname = "" then v.vname <- "__crest_tmp" ^ (string_of_int (getNewId ()));
	      v
	    in
	
	    let v' = opaque v in
		  let f = emptyFunction "" in
	    f.svar <- v';
	    setFunctionTypeMakeFormals f (typeOfLval (Var v', NoOffset));
	    setFormals f (map nameFormal f.sformals);
	
	    let returnType = funReturnType v'.vtype in
	    let args = map (fun v -> Lval (Var v, NoOffset)) f.sformals in
	     
	    let (call, return) = 
	      if isVoidType returnType then 
	        (Call (None, Lval (Var v, NoOffset), args, locUnknown), [])
	      else
	        let ret = makeLocalVar f "__crest_ret" returnType in
	        (Call (Some (Var ret, NoOffset), Lval (Var v, NoOffset), args, locUnknown), 
	         [Return (Some (Lval (Var ret, NoOffset)), locUnknown)])
	    in
	
	    let opaqueResult = instrumentResult returnType v.vname args in
	    let body = [Instr (opaqueResult @ [mkMute (); call; mkUnmute ()])] @ return in
	    
		  f.sbody.bstmts <- map mkStmt body;
		  [GFun (f, locUnknown)]
    end
  in
  
object (self)
  inherit nopCilVisitor

  (*
   * Instrument a statement (branch or function return).
   *)
  method vstmt(s) =
    match s.skind with
      | If (e, b1, b2, l) ->
        self#queueInstr [mkLocation l];
        self#queueInstr (instrumentExpr e) ;
        prependToBlock [mkBranch 1] b1 ;
        prependToBlock [mkBranch 0] b2 ;
        DoChildren 

      | Return (Some e, l) ->
          self#queueInstr [mkLocation l];
          self#queueInstr (instrumentExpr e) ;
          self#queueInstr [mkReturn 0];
          (* This is for the case we are doing custom return - some overhead, but can be simplified in the static tool *)
          self#queueInstr (setLen (typeOf e));
          SkipChildren

      | Return (None, l) ->
          self#queueInstr [mkLocation l];
          self#queueInstr [mkReturn 1] ;
          SkipChildren

      | _ -> DoChildren

  (*
   * Instrument assignment and call statements.
   *)
  method vinst(i) =
    match i with
      | Set (lv, e, l) ->
          self#queueInstr [mkLocation l];
          checkHasAddress lv;
          self#queueInstr (instrumentAssignment lv e);
          SkipChildren

      (* Don't instrument calls to instrumentation functions themselves. *)
      | Call (_, Lval (Var f, NoOffset), _, _) when shouldSkipFunction f -> 
        SkipChildren

      | Call (ret, Lval f, args, l) ->

        let t = typeOfLval f in
        let call = 
          if isVarargFunType t then
            [mkMute(); i; mkUnmute ()] @ instrumentResult (funReturnType t) "vararg_result" args 
          else
            [i]
        in
        
	      let assignRet = match ret with
	       | Some lv ->
	         checkHasAddress lv;
	         (instrumentLval lv) @ [mkStore ()]
	       | _ -> 
	         if isVoidFunType t then [] else [mkClear 1]
        in
        ChangeTo ([mkLocation l] @ (concatMap instrumentExpr args) @ call @ assignRet)

      (* FIXME: for functions called through pointers make sure they are not symbolic *)
      | _ -> DoChildren


  (*
   * Instrument function entry.
   *)
  method vfunc(f) =
    if shouldSkipFunction f.svar then
      SkipChildren
    else
      let instParam v = (instrumentLval (Var v, NoOffset)) @ [mkStore ()] in
      let (_, _, isVarArgs, _) = splitFunctionType f.svar.vtype in
        if (not isVarArgs) then
          iter (flip prependToBlock f.sbody) (List.map instParam f.sformals) 
        else 
          E.s (error "varargs not supported");
        prependToBlock [mkCall f.svar] f.sbody ;
        DoChildren


  method vglob = function
    | GVar (v, {init = i}, loc) as g ->
      markCrestified v;
      let f = emptyFunction ("__crest_" ^ v.vname ^ "_init") in
      let initialised = makeGlobalVar ("__crest_" ^ v.vname ^ "_initialised") boolType in
      let doInit = match i with
        | (Some init) -> FI (instrumentInit v init)
        | None        -> FI []
      in
      let body =
        [mkStmtOneInstr (mkCall f.svar)] 
        @
        cStmts 
            "if(!initialised) {initialised = 1; {%I:doInit}}" 
            (fun n t -> makeTempVar f ~name:n t)
            loc
            [ ("initialised", Fv initialised); ("doInit", doInit) ] 
        @
        [mkStmtOneInstr (mkReturn 1)]
      in
      f.sbody.bstmts <- body;
      ChangeTo [g; GVar (initialised, {init = Some (SingleInit (integer 0))}, loc); GFun (f, loc)]

    | GFun (f, loc) as g ->
      markCrestified f.svar;
      if needsOpaqueWrapper f.svar then
        (* opaqueDefNames := f.svar.vname :: !opaqueDefNames; *)
        ChangeTo ([g] @ opaqueWrapper f.svar)
      else
        DoChildren

    | GVarDecl (v, loc) as g when needsOpaqueWrapper v ->
      ChangeTo ([g] @ opaqueWrapper v)

    | GVarDecl (v, loc) as g when not (isOpaque v) && not (isFunctionType v.vtype) ->
      let f = initFunc v.vname in
      ChangeTo [g; GVarDecl (f, loc)]
                  
    | _ -> DoChildren 

end

class opaqueReplaceVisitorClass = object
  inherit nopCilVisitor

  method vvrbl : varinfo -> varinfo visitAction = function
    | v when needsOpaqueWrapper v -> ChangeTo (opaque v)
    | _ -> SkipChildren

end

let addCrestInitializer f =
  let crestInitTy = TFun (voidType, Some [], false, []) in
  let crestInitFunc = findOrCreateFunc f "__CrestInit" crestInitTy in
  let globalInit = getGlobInit f in
  if not f.globinitcalled then
    f.globinit <- None
  else
  begin
    crestInitFunc.vstorage <- Extern ;
    crestInitFunc.vattr <- [Attr ("crest_skip", [])] ;
    prependToBlock [Call (None, Lval (var crestInitFunc), [], locUnknown)]
                   globalInit.sbody
  end

let feature : featureDescr =
  { fd_name = "CrestInstrument";
    fd_enabled = ref false;
    fd_description = "instrument a program for symbolic execution";
    fd_extraopt = [
      ("--root", 
          Arg.String (fun s -> compilationRoot := s), 
        " The root folder of the compilation.");
      ("--csec-config", Arg.String (fun s -> Mark.config := s),
        " The csec instrumentation configuration file.");        
    ];
    fd_post_check = true;
    fd_doit =
      function (f: file) ->
        setSrcPath f;
        Mark.markGlobals f;
        (* Simplify the code:
         *  - simplifying expressions with complex memory references
         *  - converting loops and switches into goto's and if's (* FIXME: do I like this? *)
         *  - transforming functions to have exactly one return *)
        Simplemem.feature.fd_doit f ;
        (* iterGlobals f prepareGlobalForCFG ; *)
        Oneret.feature.fd_doit f ;
        (* Finally instrument the program. *)
        visitCilFile (new opaqueReplaceVisitorClass) f;
        let instVisitor = new crestInstrumentVisitor f in
           visitCilFile (instVisitor :> cilVisitor) f; 
        (* Add a function to initialize the instrumentation library. *)
        addCrestInitializer f ;
        writeInfo ()
}
