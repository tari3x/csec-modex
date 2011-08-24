open Yices
open Printf

let () =
  let ctx = mk_context () in
  let e1 = mk_fresh_bool_var ctx in
  let e2 = mk_fresh_bool_var ctx in
  let eq1 = mk_eq ctx e1 e2 in
  assert_simple ctx eq1; (* assert is a reserved keyword in ocaml *)
  dump_context ctx;
  begin match check ctx with
  | True ->
    let m = get_model ctx in
    let f b = match b with True -> "true" | False -> "false" | Undef -> "undef" in
    printf "e1 = %s\n" (f (get_value m (get_var_decl e1)));
    printf "e2 = %s\n" (f (get_value m (get_var_decl e2)));
  | False ->
    printf "unsatisfiable\n";
  | Undef ->
    printf "unknown\n";
  end;
  del_context ctx
