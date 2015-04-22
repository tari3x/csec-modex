open Exp
open Common
open Typing

module E = Exp
module S = Solver

type t = Forall of (var * bitstring Type.t) list * fact

let create fun_types (e : fact) : t =
  let vs = E.vars e in
  let ts = Typing.infer_exp fun_types (Some Bool) e in
  match List.diff vs (Type_ctx.keys ts) with
  | [] -> Forall (Type_ctx.to_list ts, e)
  | vs ->
    let vs = String.concat vs ~sep:", " in
    fail "CV_fact.make: could not infer types for %s in %s"
      vs (E.to_string e)
