(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


open Types
open Utils
open List

let ops : (string * (intval -> intval -> intval)) list = 
  [("+", Int64.add); ("-", Int64.add); ("*", Int64.mul)]

let arithSimplifyEq : (exp -> exp -> bool) -> bool -> exp -> exp = fun eq wantFold e ->

	let simplifySums : exp -> exp = function
	  | Sym ((op, fixity), es, len, id) as e ->
	
	    let elimZero : exp list -> exp list = fun es -> filter_out (eq zero) es in
	    
	    let mkSum : exp list -> exp = function
	        | []  -> zero
	        | [e] -> e
	        | es' -> Sym (("+", Infix), es', len, id)
	    in
	
      (* The proper way is to make the SMT solver perform the operation *)
      let mkOp : int64 -> (int * exp) -> int64 = fun n -> function
        | (sign, Int (m, _)) -> Int64.add n (Int64.mul (Int64.of_int sign) m)
        | _                  -> fail "mkOp: not an integer"
      in
  
	    let rec signs : int -> exp -> (int * exp) list = fun sign -> function
	      | Sym (("+", _), es,     _, _) -> concat (map (signs sign) es)
	      | Sym (("-", _), [a; b], _, _) -> (signs sign a) @ (signs (-1 * sign) b)
	      | e -> [(sign, e)]
	    in

	    let split : exp -> exp list * exp list = fun e ->
	      let es = signs 1 e in
        let (eInt, eSym) = if wantFold then partition (function (_, e) -> isInteger e) es 
                                       else ([], es) in 
	      let (ePos, eNeg) = partition (function (sign, _) -> sign = 1) eSym in
        let cInt = fold_left mkOp 0L eInt in
        (* FIXME: will Unknown length be enough? *)
	      ((if cInt = 0L then [] else [Int (cInt, Unknown)]) @ map snd ePos, map snd eNeg)
	    in
	    
	    let (ePos, eNeg) = split e in
	    begin
	      match (elimZero (multidiff eq ePos eNeg), elimZero (multidiff eq eNeg ePos)) with
	        | (ePos', [])    -> mkSum ePos'
	        | (ePos', eNeg') -> Sym (("-", Infix), [mkSum ePos'; mkSum eNeg'], len, id)
	    end
	
	  | e -> e
  in  

  (* TODO: deal with it like you deal with addition *)  
  let elimOne : exp -> exp = function
    | Sym ((op, fixity), es, len, id) when mem op ["*"; "/"] ->
      begin
          match filter_out (eq one) es with
            | []  -> one
            | [e] -> e
            | es' -> Sym ((op, fixity), es', len, id)
      end

    | e -> e
  in

  (* debug ("arithSimplify: " ^ dump e); *)
  elimOne (simplifySums e)
 
