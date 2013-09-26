 
(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(**
  Lists all functions declared boring that are not reachable from "main" through functions
  that are neither opaque nor proxied.
  
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
  glob.proxied  || glob.opaque || (isInterfaceFun v)

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
      if not (isHandled v) then 
        iter visit (children v)
    end
  in
  visit v; !visited

;;
begin
  readInfo "callgraph.out" "globs.out";
  Mark.readConfig Sys.argv.(1);
  iter print_endline (diff !Mark.boringNames (reachable "main" !callgraph)) 
end;
