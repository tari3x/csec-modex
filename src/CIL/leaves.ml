(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(**
  Compute leaves of a graph, in the connected component of the "main" node.
  
  Output those that are not proxied (or for which no proxy function exists), opaque or crestified
  
  Quadratic implementation.
*) 

open List

open Common

let isBad : vertex -> bool = fun v ->
  let glob = try 
    StrMap.find v !globs
    with Not_found -> fail ("isBad, not found: " ^ v) 
  in not glob.crestified

let isHandled : vertex -> bool = fun v ->
  let glob = try 
    StrMap.find v !globs
    with Not_found -> fail ("isHandled, not found: " ^ v) in 
  if glob.proxied then StrMap.mem (v ^ "_proxy") !globs else
  glob.opaque || (isInterfaceFun v)

let leaves : vertex -> graph -> vertex list = fun v g ->
  
  (* Make this a set if you don't want to be quadratic *)
	let visited : vertex list ref = ref [] in
	let leaves  : vertex list ref = ref [] in

  let children : vertex -> vertex list = fun v ->
  map snd (filter (fun (src, _) -> src = v) g)
  in
  
  let rec visit : vertex -> unit = fun v -> 
    if not (mem v !visited) && (not (isHandled v)) then 
    begin
	    visited := v :: !visited;
	    match children v with
	      | [] -> leaves := v :: !leaves
        | us -> iter visit us
    end
  in
  visit v; !leaves

;;
begin
  readInfo "callgraph.out" "globs.out";
  iter print_endline (filter isBad (leaves "main" !callgraph))
end;
