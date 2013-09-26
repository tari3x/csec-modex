(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(**
  Finds a leaf of a graph, in the connected component of the "main" node. Prints out the path.
  
  First tries to find a path that doesn't go through proxied, opaque, or interface functions.
  If that fails, tries again with all functions.
  
  Quadratic implementation.
*) 

open List

open Common

let notHandled : vertex -> bool = fun v ->
  let glob = try 
    StrMap.find v !globs
    with Not_found -> fail ("isHandled, not found: " ^ v) in 
    
  (* 
    The only case where is_proxy becomes important is BN_num_bytes, which
    is preprocessed to become the proxy call, and so appears in normal code.
  *)
  not (glob.is_proxy || glob.proxied || glob.opaque || isInterfaceFun v) 

(**
    Return a path from [v] to [w] or an empty list if there is no path.
*)
let findLeaf : bool -> vertex -> vertex -> graph -> vertex list = fun allowHandled v w g ->
  
  (* Make this a set if you don't want to be quadratic *)
	let visited : vertex list ref = ref [] in
	let path    : vertex list ref = ref [] in

  let children : vertex -> vertex list = fun v ->
    map snd (filter (fun (src, dest) -> src = v && (allowHandled || notHandled dest)) g)
  in
  
  let rec visit : vertex -> unit = fun v -> 
    if v = w then raise Exit;
    if not (mem v !visited) then 
    begin
      visited := v :: !visited;
      let old_path = !path in
      path := v :: !path;
      iter visit (children v);
      path := old_path;
    end
  in
  try visit v; [] with Exit -> !path

;;
begin
  readInfo "callgraph.out" "globs.out";
  let path = (rev (findLeaf false "main" Sys.argv.(1) !callgraph)) in
  if path <> [] then
     iter print_endline path
  else
  begin
    print_endline "No path without proxied or opaque functions found, trying with all functions:";
    iter print_endline (rev (findLeaf true "main" Sys.argv.(1) !callgraph))
  end 
end;
