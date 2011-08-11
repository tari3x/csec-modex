(*
    Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
    This file is distributed as part of csec-tools under a BSD license.
    See LICENSE file for copyright notice.
*)


(**
  Finds a leaf of a graph, in the connected component of the "main" node. Prints out the path.
  
  Quadratic implementation.
*) 

open List

open Common

(**
    Return a path from [v] to [w] or an empty list if there is no path.
*)
let findLeaf : vertex -> vertex -> graph -> vertex list = fun v w g ->
  
  (* Make this a set if you don't want to be quadratic *)
	let visited : vertex list ref = ref [] in
	let path    : vertex list ref = ref [] in

  let children : vertex -> vertex list = fun v ->
  map snd (filter (fun (src, _) -> src = v) g)
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
  iter print_endline (rev (findLeaf "main" Sys.argv.(1) !callgraph))
end;
