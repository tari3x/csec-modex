(*
	Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
	This file is distributed as part of csec-tools under a BSD license.
	See LICENSE file for copyright notice.
*)
 
(**
  Outputs all pairs (v, w) such that v is opaque, w is proxied and
  w is reachable from v.
  
  Quadratic implementation.
*) 

open List

open Common

let isOpaque : string * glob -> bool = fun (_, g) -> g.opaque && (not g.needs_proxy)

let isProxy : vertex -> bool = fun v -> let g = StrMap.find v !globs in g.needs_proxy

let printEdge : edge -> unit = function (v, w) ->
  print_endline (v ^ " " ^ w)

let reachable : vertex -> graph -> vertex list = fun v g ->
  
  (* Make this a set if you don't want to be quadratic *)
  let visited : vertex list ref = ref [] in

  let children : vertex -> vertex list = fun v ->
    map snd (filter (fun (src, _) -> src = v) g)
  in
  
  let rec visit : vertex -> unit = fun v -> 
    if not (mem v !visited) then 
    begin
        visited := v :: !visited;
        iter visit (children v);
    end
  in
  visit v; !visited

let badPairs : unit -> edge list = fun () ->
  
  let badSuccessors : vertex -> edge list = fun v ->
    map (fun w -> (v, w)) (filter isProxy (reachable v !callgraph)) 
  in
  
  let opaque_nodes = map fst (filter isOpaque (StrMap.bindings !globs)) in
  concat (map badSuccessors opaque_nodes)
  
;;
begin
  readInfo "callgraph.out" "globs.out";
  iter printEdge (badPairs ());
  (* print_endline "digraph {";
  (* print_endline "size=190"; *)
  print_endline "node [shape=none]"; *)
  (* iter print_edge (filter (function (v, w) -> mem v main_cc) graph); *)
  (* print_endline "}"; *)
end;
