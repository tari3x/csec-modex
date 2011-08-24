(* File generated from yices.idl *)

type context
and typ
and expr
and var_decl
and model
and assertion_id = int
and lbool =
  | False
  | Undef
  | True
and var_decl_iterator
and unsat_core = assertion_id array

external version : unit -> string
	= "camlidl_yices_yices_version"

external set_verbosity : int -> unit
	= "camlidl_yices_yices_set_verbosity"

external set_max_num_conflicts_in_maxsat_iteration : int -> unit
	= "camlidl_yices_yices_set_max_num_conflicts_in_maxsat_iteration"

external enable_type_checker : bool -> unit
	= "camlidl_yices_yices_enable_type_checker"

external set_max_num_iterations_in_maxsat : int -> unit
	= "camlidl_yices_yices_set_max_num_iterations_in_maxsat"

external set_maxsat_initial_cost : int64 -> unit
	= "camlidl_yices_yices_set_maxsat_initial_cost"

external set_arith_only : bool -> unit
	= "camlidl_yices_yices_set_arith_only"

external enable_log_file : string -> unit
	= "camlidl_yices_yices_enable_log_file"

external mk_context : unit -> context
	= "camlidl_yices_yices_mk_context"

external del_context : context -> unit
	= "camlidl_yices_yices_del_context"

external reset : context -> unit
	= "camlidl_yices_yices_reset"

external dump_context : context -> unit
	= "camlidl_yices_yices_dump_context"

external push : context -> unit
	= "camlidl_yices_yices_push"

external pop : context -> unit
	= "camlidl_yices_yices_pop"

external assert_simple : context -> expr -> unit
	= "camlidl_yices_yices_assert"

external assert_weighted : context -> expr -> int64 -> assertion_id
	= "camlidl_yices_yices_assert_weighted"

external assert_retractable : context -> expr -> assertion_id
	= "camlidl_yices_yices_assert_retractable"

external retract : context -> assertion_id -> unit
	= "camlidl_yices_yices_retract"

external inconsistent : context -> int
	= "camlidl_yices_yices_inconsistent"

external check : context -> lbool
	= "camlidl_yices_yices_check"

external find_weighted_model : context -> bool -> lbool
	= "camlidl_yices_yices_find_weighted_model"

external max_sat : context -> lbool
	= "camlidl_yices_yices_max_sat"

external max_sat_cost_leq : context -> int64 -> lbool
	= "camlidl_yices_yices_max_sat_cost_leq"

external get_unsat_core : context -> unsat_core
	= "camlidl_yices_get_unsat_core"

external get_model : context -> model
	= "camlidl_yices_yices_get_model"

external evaluate_in_model : model -> expr -> lbool
	= "camlidl_yices_yices_evaluate_in_model"

external get_value : model -> var_decl -> lbool
	= "camlidl_yices_yices_get_value"

external get_int_value : model -> var_decl -> int32
	= "camlidl_yices_yices_get_int_value"

external get_arith_value : model -> var_decl -> int32 * int32
	= "camlidl_yices_yices_get_arith_value"

external get_double_value : model -> var_decl -> float
	= "camlidl_yices_yices_get_double_value"

external get_bitvector_value : model -> var_decl -> int -> bool array
	= "camlidl_yices_yices_get_bitvector_value"

let get_bv_value = get_bitvector_value
external get_rational_value_as_string : model -> var_decl -> string
	= "camlidl_yices_get_rational_value_as_string"

external get_integer_value_as_string : model -> var_decl -> string
	= "camlidl_yices_get_integer_value_as_string"

let get_ratio_value m d =  Ratio.ratio_of_string (get_rational_value_as_string m d);;

let get_big_int_value m d =  Big_int.big_int_of_string (get_integer_value_as_string m d);;

external get_assertion_value : model -> assertion_id -> bool
	= "camlidl_yices_yices_get_assertion_value"

external display_model : model -> unit
	= "camlidl_yices_yices_display_model"

external get_cost : model -> int64
	= "camlidl_yices_yices_get_cost"

external get_cost_as_double : model -> float
	= "camlidl_yices_yices_get_cost_as_double"

external mk_type : context -> string -> typ
	= "camlidl_yices_yices_mk_type"

let number_type_name = "number";;
let real_type_name = "real";;
let int_type_name = "int";;
let nat_type_name = "nat";;
let bool_type_name = "bool";;
let any_type_name = "any";;

external mk_function_type : context -> typ array -> typ -> typ
	= "camlidl_yices_yices_mk_function_type"

external mk_bitvector_type : context -> int -> typ
	= "camlidl_yices_yices_mk_bitvector_type"

let mk_bv_type = mk_bitvector_type
external mk_tuple_type : context -> typ array -> typ
	= "camlidl_yices_yices_mk_tuple_type"

external mk_true : context -> expr
	= "camlidl_yices_yices_mk_true"

external mk_false : context -> expr
	= "camlidl_yices_yices_mk_false"

external mk_bool_var : context -> string -> expr
	= "camlidl_yices_yices_mk_bool_var"

external mk_fresh_bool_var : context -> expr
	= "camlidl_yices_yices_mk_fresh_bool_var"

external get_var_decl : expr -> var_decl
	= "camlidl_yices_yices_get_var_decl"

external mk_bool_var_decl : context -> string -> var_decl
	= "camlidl_yices_yices_mk_bool_var_decl"

external get_var_decl_name : var_decl -> string
	= "camlidl_yices_yices_get_var_decl_name"

external mk_bool_var_from_decl : context -> var_decl -> expr
	= "camlidl_yices_yices_mk_bool_var_from_decl"

external mk_or : context -> expr array -> expr
	= "camlidl_yices_yices_mk_or"

external mk_and : context -> expr array -> expr
	= "camlidl_yices_yices_mk_and"

external mk_eq : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_eq"

external mk_diseq : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_diseq"

external mk_ite : context -> expr -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_ite"

external mk_not : context -> expr -> expr
	= "camlidl_yices_yices_mk_not"

external create_var_decl_iterator : context -> var_decl_iterator
	= "camlidl_yices_yices_create_var_decl_iterator"

external iterator_has_next : var_decl_iterator -> bool
	= "camlidl_yices_yices_iterator_has_next"

external iterator_next : var_decl_iterator -> var_decl
	= "camlidl_yices_yices_iterator_next"

external iterator_reset : var_decl_iterator -> unit
	= "camlidl_yices_yices_iterator_reset"

external del_iterator : var_decl_iterator -> unit
	= "camlidl_yices_yices_del_iterator"

let iter_bool_var_decl f ctx = 
  let it = create_var_decl_iterator ctx in
    while iterator_has_next it do
      f (iterator_next it);
    done;
    del_iterator it;;

external mk_var_decl : context -> string -> typ -> var_decl
	= "camlidl_yices_yices_mk_var_decl"

external get_var_decl_from_name : context -> string -> var_decl
	= "camlidl_yices_yices_get_var_decl_from_name"

external mk_var_from_decl : context -> var_decl -> expr
	= "camlidl_yices_yices_mk_var_from_decl"

external mk_app : context -> expr -> expr array -> expr
	= "camlidl_yices_yices_mk_app"

external mk_num : context -> int -> expr
	= "camlidl_yices_yices_mk_num"

external mk_num_from_string : context -> string -> expr
	= "camlidl_yices_yices_mk_num_from_string"

external mk_sum : context -> expr array -> expr
	= "camlidl_yices_yices_mk_sum"

external mk_sub : context -> expr array -> expr
	= "camlidl_yices_yices_mk_sub"

external mk_mul : context -> expr array -> expr
	= "camlidl_yices_yices_mk_mul"

external mk_lt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_lt"

external mk_le : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_le"

external mk_gt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_gt"

external mk_ge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_ge"

external mk_bv_constant : context -> int -> int32 -> expr
	= "camlidl_yices_yices_mk_bv_constant"

external mk_bv_constant_from_array : context -> bool array -> expr
	= "camlidl_yices_yices_mk_bv_constant_from_array"

external mk_bv_add : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_add"

external mk_bv_sub : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sub"

external mk_bv_mul : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_mul"

external mk_bv_minus : context -> expr -> expr
	= "camlidl_yices_yices_mk_bv_minus"

external mk_bv_concat : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_concat"

external mk_bv_and : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_and"

external mk_bv_or : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_or"

external mk_bv_xor : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_xor"

external mk_bv_not : context -> expr -> expr
	= "camlidl_yices_yices_mk_bv_not"

external mk_bv_extract : context -> int -> int -> expr -> expr
	= "camlidl_yices_yices_mk_bv_extract"

external mk_bv_sign_extend : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_sign_extend"

external mk_bv_shift_left0 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_left0"

external mk_bv_shift_left1 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_left1"

external mk_bv_shift_right0 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_right0"

external mk_bv_shift_right1 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_right1"

external mk_bv_lt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_lt"

external mk_bv_le : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_le"

external mk_bv_gt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_gt"

external mk_bv_ge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_ge"

external mk_bv_slt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_slt"

external mk_bv_sle : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sle"

external mk_bv_sgt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sgt"

external mk_bv_sge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sge"

external pp_expr : expr -> unit
	= "camlidl_yices_yices_pp_expr"

module Future = struct

external interrupt : context -> unit
	= "camlidl_yices_yices_interrupt"

external get_lite_context : context -> Yicesl.context
	= "camlidl_yices_yices_get_lite_context"

external mk_function_update : context -> expr -> expr array -> expr -> expr
	= "camlidl_yices_yices_mk_function_update"

external mk_tuple_literal : context -> expr array -> expr
	= "camlidl_yices_yices_mk_tuple_literal"

end

