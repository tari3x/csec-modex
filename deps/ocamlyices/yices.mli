(* File generated from yices.idl *)
(**
  Yices binding for Ocaml

  See the official {{:http://yices.csl.sri.com/capi.shtml} C API documentation}
*)

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
and unsat_core = assertion_id array

(**
  [context] A context sotres a collection of declarations and asserations.

  [expr] Expressions (abstract syntax tree)

  [typ] Types (abstract syntax tree)

  [var_decl] Variable declaration.
  A declaration consists of a name a type (such as [x::bool]). An
  instance of the declaration represents the term [x]. Instances are also
  called name expressions. Instances can be created using 
  {!mk_bool_var_from_decl} or {!mk_var_from_decl}.

  [model] Model. A model assigns constant values to variables defined in a context.
  The context must be known to be consistent for a model to be available.
  The model is constructed by calling {!check} (or its relatives) then
  {!get_model}.

  [assertion_id] Assertion index, to identify retractable assertions.

  [lbool] Extended booleans: to represent the value of literals in the context
*)
(**
   Return the Yices version number.
*)
external version : unit -> string
	= "camlidl_yices_yices_version"

(** {2 Parameters} *)
(**
   Set the verbosity level.
*)
external set_verbosity : int -> unit
	= "camlidl_yices_yices_set_verbosity"

(**

   Set the maximum number of conflicts that are allowed in a maxsat iteration.

   If the maximum is reached, then "unknown" (i.e., [Undef]) is returned by maxsat.
*)
external set_max_num_conflicts_in_maxsat_iteration : int -> unit
	= "camlidl_yices_yices_set_max_num_conflicts_in_maxsat_iteration"

(**
   Force Yices to type check expressions when they are asserted (default = false).
*)
external enable_type_checker : bool -> unit
	= "camlidl_yices_yices_enable_type_checker"

(**
   Set the maximum number of iterations in the MaxSAT algorithm.

   If the maximum is reached, then "unknown" (i.e., [Undef]) is returned by maxsat.
*)
external set_max_num_iterations_in_maxsat : int -> unit
	= "camlidl_yices_yices_set_max_num_iterations_in_maxsat"

(**
   Set the initial cost for a maxsat problem.
*)
external set_maxsat_initial_cost : int64 -> unit
	= "camlidl_yices_yices_set_maxsat_initial_cost"

(**
   Inform yices that only arithmetic theory is going to be used.

   This flag usually improves performance (default = false).
*)
external set_arith_only : bool -> unit
	= "camlidl_yices_yices_set_arith_only"

(**
   Enable a log file that will store the assertions, checks, decls, etc.

   If the log file is already open, then nothing happens.
*)
external enable_log_file : string -> unit
	= "camlidl_yices_yices_enable_log_file"

(** {2 Context management} *)
(**
   Create a logical context.
*)
external mk_context : unit -> context
	= "camlidl_yices_yices_mk_context"

(**
   Delete the given logical context.

   See {!mk_context}.
*)
external del_context : context -> unit
	= "camlidl_yices_yices_del_context"

(**
   Reset the given logical context.
*)
external reset : context -> unit
	= "camlidl_yices_yices_reset"

(**
   Display the internal representation of the given logical context on [stderr]. 

   This function is mostly for debugging.
*)
external dump_context : context -> unit
	= "camlidl_yices_yices_dump_context"

(**
   Create a backtracking point in the given logical context.

   The logical context can be viewed as a stack of contexts.
   The scope level is the number of elements on this stack. The stack
   of contexts is simulated using trail (undo) stacks.
*)
external push : context -> unit
	= "camlidl_yices_yices_push"

(**
   Backtrack.

   Restores the context from the top of the stack, and pops it off the
   stack.  Any changes to the logical context (by {!assert_simple} or
   other functions) between the matching {!push} and [pop]
   operators are flushed, and the context is completely restored to
   what it was right before the {!push}.

   See {!push}.
*)
external pop : context -> unit
	= "camlidl_yices_yices_pop"

(** {3 Assertions} *)
(**
   Assert a constraint in the logical context.

   After one assertion, the logical context may become inconsistent.
   The method {!inconsistent} may be used to check that.
*)
external assert_simple : context -> expr -> unit
	= "camlidl_yices_yices_assert"

(**
   Assert a constraint in the logical context with weight [w].

   @return An id that can be used to retract the constraint.

   See {!retract}.
*)
external assert_weighted : context -> expr -> int64 -> assertion_id
	= "camlidl_yices_yices_assert_weighted"

(**
   Assert a constraint that can be later retracted.

   @return An id that can be used to retract the constraint.

   This is similar to {!assert_weighted}, but the weight is considered to be infinite.

   See {!retract}.
*)
external assert_retractable : context -> expr -> assertion_id
	= "camlidl_yices_yices_assert_retractable"

(**
   Retract a retractable or weighted constraint.

   See {!assert_weighted} and {!assert_retractable}.
*)
external retract : context -> assertion_id -> unit
	= "camlidl_yices_yices_retract"

(** {3 Checking} *)
(**
   Return 1 if the logical context is known to be inconsistent.
*)
external inconsistent : context -> int
	= "camlidl_yices_yices_inconsistent"

(**
   Check if the logical context is satisfiable.

   - [True] means the context is satisfiable
   - [False] means it is unsatisfiable
   - [Undef] means it was not possible to decide due to an incompleteness.

   If the context is satisfiable, then {!get_model} can be used to obtain a model.

   {i Warning!} This method ignore the weights associated with the constraints.
*)
external check : context -> lbool
	= "camlidl_yices_yices_check"

(**
  [find_weighted_model ctx random] searches for a model of the constraints
  asserted in [ctx] and compute its cost.

  If [random] is true, then random search is used,
  otherwise, the default decision heuristic is used.

  If there are no weighted constaints in [ctx], then this function is the same as {!check}.

  Otherwise, it searches for a model that satisfies all the
  non-weighted constraints but not necessarily the weighted
  constraints. The function returns [True] if such a model is
  found, and the model can be obtained using {!get_model}.  The
  cost of this model is the sum of the weights of the unsatisfied
  weighted constraints.

  The function returns [False] if it cannot find such a model.

  The function may also return [Undef], if the context contains
  formulas for which yices is incomplete (e.g., quantifiers). Do not
  use the model in this case.
*)
external find_weighted_model : context -> bool -> lbool
	= "camlidl_yices_yices_find_weighted_model"

(**
   Compute the maximal satisfying assignment for the asserted
   weighted constraints.

   - [True] means the maximal satisfying assignment was found
   - [False] means it is unsatisfiable (this may happen if the context has 
     unweighted constraints)
   - [Undef] means it was not possible to decide due to an incompleteness.
     If the result is [True], then {!get_model} can be used to obtain a model.

   See {!assert_weighted}
*)
external max_sat : context -> lbool
	= "camlidl_yices_yices_max_sat"

(**
   Similar to {!max_sat}, but start looking for models with cost
   less than of equal to [max_cost].

   @return [False] if such a model doesn't exist.
*)
external max_sat_cost_leq : context -> int64 -> lbool
	= "camlidl_yices_yices_max_sat_cost_leq"

(** {2 Unsatisifiable core} *)
(** {i (OCaml-specific)} Get the unsat core. Each element is the id of a retractable assertion. *)
external get_unsat_core : context -> unsat_core
	= "camlidl_yices_get_unsat_core"

(** {2 Model} *)
(**
   Return a model for a satisfiable logical context.

   {i Warning!} The should be only called if {!check} or {!max_sat} 
   returned [True] or [Undef].
   Calls to functions which modify the context invalidate the model.

   @raise Failure if the model is not available
*)
external get_model : context -> model
	= "camlidl_yices_yices_get_model"

(**
   Evaluate a formula in a model.

   Model can be obtained via {!get_model}, after a call to {!check},
   {!max_sat}, or {!find_weighted_model}

   - [True] means the formula is true in the model
   - [False] means the formula is false in the model
   - [Undef] means the model does not have enough information.
     typically this is due to a function application, e.g., 
     the model defines (f 1) and (f 2), but the formula references (f 3)
*)
external evaluate_in_model : model -> expr -> lbool
	= "camlidl_yices_yices_evaluate_in_model"

(**
   [get_value m v] returns the assignment for the variable [v].

   The result is [Undef] if the value of [v] is a "don't care".

   {i Warning!} [v] must be the declaration of a boolean variable.

   See {!get_int_value}, {!get_arith_value} and {!get_double_value}.
*)
external get_value : model -> var_decl -> lbool
	= "camlidl_yices_yices_get_value"

(**
   [get_int_value m v] returns the integer value assigned to variable [v] in model [m]

   @raise Failure if one of the following errors occurs:
   - [v] is not a proper declaration or not the declaration of a numerical variable
   - [v] has no value assigned in model m (typically, this means that [v] does not 
   occur in the asserted constraints)
   - [v] has a value that cannot be converted to [long], because
   it is rational or too big

   See {!get_value}, {!get_arith_value} and {!get_double_value}.
*)
external get_int_value : model -> var_decl -> int32
	= "camlidl_yices_yices_get_int_value"

(**
   [get_arith_value m v] returns the rational value as a pair (numerator, denominator)

   @raise Failure if one of the following errors occurs:
   - [v] is not a proper declaration or not the declaration of a numerical variable
   - [v] has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)
   - [v] has a value that cannot be converted to [long/long], 
   because the numerator or the denominator is too big

   See {!get_value}, {!get_int_value} and {!get_double_value}.
*)
external get_arith_value : model -> var_decl -> int32 * int32
	= "camlidl_yices_yices_get_arith_value"

(**
   [get_double_value m v] converts the value assigned to variable [v]
   in model [m] to a floating point number and returns it. 

   @raise Failure if one of the following errors occurs:
   - [v] is not a proper declaration or not the declaration of a numerical variable
   - [v] has no value assigned in model [m] (typically, this means that [v] does not 
   occur in the asserted constraints)

   See {!get_value}, {!get_int_value} and {!get_arith_value}.
*)
external get_double_value : model -> var_decl -> float
	= "camlidl_yices_yices_get_double_value"

(**
   [get_bitvector_value m v n] gets the bitvector constant assigned to a
   variable [v] in model [m].

   It returns an array of [n] booleans: [bv.(0)] is the low-order
   bit and [bv.(n - 1)] is the high-order bit.

   [n] should be the size of the bitvector variable [v]. Otherwise:
   - If [n] is smaller than [v]'s size, the [n] lower-order bits of [v] are returned.
   - If [n] is larger than [v]'s size, then the extra high-order bits are set to 0.

   @raise Failure if one of the following errors occurs:
   - [v] is not a proper declaration or not the declaration of a bitvector variable
   - [v] has no value assigned in model [m] (typically, this means that [v] does not 
   occur in the asserted constraints)
*)
external get_bitvector_value : model -> var_decl -> int -> bool array
	= "camlidl_yices_yices_get_bitvector_value"

(** Alias of {!get_bitvector_value}. *)
val get_bv_value : model -> var_decl -> int -> bool array

external get_rational_value_as_string : model -> var_decl -> string
	= "camlidl_yices_get_rational_value_as_string"

external get_integer_value_as_string : model -> var_decl -> string
	= "camlidl_yices_get_integer_value_as_string"

val get_ratio_value : model -> var_decl -> Ratio.ratio

val get_big_int_value : model -> var_decl -> Big_int.big_int

(**
   Return true (false) if the assertion of the given assertion id is satisfied (not
   satisfied) in the model.

   This function is only useful for assertion ids obtained using {!assert_weighted},
   and if {!max_sat} was used to build the model. That is the only scenario where an
   assertion may not be satisfied in a model produced by yices.
*)
external get_assertion_value : model -> assertion_id -> bool
	= "camlidl_yices_yices_get_assertion_value"

(**
   Display the given model in the standard output.
*)
external display_model : model -> unit
	= "camlidl_yices_yices_display_model"

(**
   Return the cost of model [m].

   The cost is the sum of the weights of unsatisfied constraints.

   {i Warning!} The model cost is computed automatically by {!max_sat} but 
   not by {!check}. If {!check} returns [True] (or [Undef]),
   you can to call [compute_model_cost] to compute the cost explicitly.
   {b But this function does not seem to exist yet... MD}
*)
external get_cost : model -> int64
	= "camlidl_yices_yices_get_cost"

(**
   Return the cost of the model m, converted to a double-precision 
   floating point number.
*)
external get_cost_as_double : model -> float
	= "camlidl_yices_yices_get_cost_as_double"

(** {2 Types} *)
(**
   Return the type associated with the given name. If the type
   does not exist, a new uninterpreted type is created.

   {i Remark:} number, real, int, nat, bool, any are builtin types.
*)
external mk_type : context -> string -> typ
	= "camlidl_yices_yices_mk_type"

val number_type_name : string
val real_type_name : string
val int_type_name : string
val nat_type_name : string
val bool_type_name : string
val any_type_name : string

(**
   [mk_function_type ctx d r] returns a function type [(-> d1 ... dn r)].
*)
external mk_function_type : context -> typ array -> typ -> typ
	= "camlidl_yices_yices_mk_function_type"

(**
   Returns the bitvector type of the given size [(bv size)].
   
   The size must be positive.
*)
external mk_bitvector_type : context -> int -> typ
	= "camlidl_yices_yices_mk_bitvector_type"

(** Alias of {!mk_bv_type}*)
val mk_bv_type : context -> int -> typ

(**
   Constructs the tuple type [(a0, ..., an)].
*)
external mk_tuple_type : context -> typ array -> typ
	= "camlidl_yices_yices_mk_tuple_type"

(** {2 Expressions}*)
(**
   Return an expression representing \c true.
 *)
external mk_true : context -> expr
	= "camlidl_yices_yices_mk_true"

(**
   Return an expression representing \c false.
 *)
external mk_false : context -> expr
	= "camlidl_yices_yices_mk_false"

(**
   Return a name expression for the given variable name. 

   [mk_bool_var c n1 = mk_bool_var c n2] when [n1 = n2].

   See {!mk_bool_var_decl}, {!mk_fresh_bool_var}, {!mk_bool_var_from_decl}.
*)
external mk_bool_var : context -> string -> expr
	= "camlidl_yices_yices_mk_bool_var"

(**
   Return a fresh boolean variable.
 *)
external mk_fresh_bool_var : context -> expr
	= "camlidl_yices_yices_mk_fresh_bool_var"

(**
   [get_var_decl e] returns the variable declaration object associated with
   the given name expression.

   {i Warning!} [e] must be a name expression created using methods such
   as: {!mk_bool_var}, {!mk_fresh_bool_var}, or {!mk_bool_var_from_decl}.
 *)
external get_var_decl : expr -> var_decl
	= "camlidl_yices_yices_get_var_decl"

(**
   Return a new boolean variable declaration. 
   
   It is an error to create two variables with the same name.
 *)
external mk_bool_var_decl : context -> string -> var_decl
	= "camlidl_yices_yices_mk_bool_var_decl"

(**
   Return a name of a variable declaration.
 *)
external get_var_decl_name : var_decl -> string
	= "camlidl_yices_yices_get_var_decl_name"

(**
   Return a name expression (instance) using the given variable declaration.
 *)
external mk_bool_var_from_decl : context -> var_decl -> expr
	= "camlidl_yices_yices_mk_bool_var_from_decl"

(**
   Return an expression representing the disjunction [or] of the given arguments.

   {i Warning!} the length of the array must be greater than 0.
*)
external mk_or : context -> expr array -> expr
	= "camlidl_yices_yices_mk_or"

(**
   Return an expression representing the conjunction [and] of the given arguments.

   {i Warning!} the length of the array must be greater than 0.
*)
external mk_and : context -> expr array -> expr
	= "camlidl_yices_yices_mk_and"

(**
   [mk_eq ctx a1 a2] returns an expression representing [a1 = a2].
*)
external mk_eq : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_eq"

(**
   [mk_eq ctx a1 a2] returns an expression representing [a1 /= a2].
*)
external mk_diseq : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_diseq"

(**
   [mk_ite ctx c t e] returns an expression representing [(if c t e)] (if {i condition} then {i then-value} else {i else-value}).
*)
external mk_ite : context -> expr -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_ite"

(**
   [mk_not ctx a] returns an expression representing [(not a)].
 *)
external mk_not : context -> expr -> expr
	= "camlidl_yices_yices_mk_not"

(*
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

*)

(** {i (OCaml-specific)} Applies a function to each boolean variable declarations of a given context. *)
val iter_bool_var_decl: (var_decl -> unit) -> context -> unit;;

(**
   Return a new (global) variable declaration. It is an error to create two variables
   with the same name.
*)
external mk_var_decl : context -> string -> typ -> var_decl
	= "camlidl_yices_yices_mk_var_decl"

(**
   Return a variable declaration associated with the given name.

   Return 0 if there is no variable declaration associated with the given name.
*)
external get_var_decl_from_name : context -> string -> var_decl
	= "camlidl_yices_yices_get_var_decl_from_name"

(**
   Return a name expression (instance) using the given variable declaration.
*)
external mk_var_from_decl : context -> var_decl -> expr
	= "camlidl_yices_yices_mk_var_from_decl"

(**
   Return a function application term [(f t1 ... tn)].

   The type of [f] must be a function type, and its arity must
   be equal to the number of arguments.
*)
external mk_app : context -> expr -> expr array -> expr
	= "camlidl_yices_yices_mk_app"

(** {3 Numeric expressions} *)
(**
   Return an expression representing the given integer.
*)
external mk_num : context -> int -> expr
	= "camlidl_yices_yices_mk_num"

(**
   Return an expression representing the number provided in ASCII format.
*)
external mk_num_from_string : context -> string -> expr
	= "camlidl_yices_yices_mk_num_from_string"

(**
   [mk_sum ctx arr] returns an expression representing [arr.(0) + ... + arr.(n)].

   {i Warning!} [Array.length arr] must be greater than zero.
*)
external mk_sum : context -> expr array -> expr
	= "camlidl_yices_yices_mk_sum"

(**
   [mk_sub ctx arr] returns an expression representing [arr.(0) - ... - arr.(n)].

   {i Warning!} [Array.length arr] must be greater than zero.
 *)
external mk_sub : context -> expr array -> expr
	= "camlidl_yices_yices_mk_sub"

(**
   [mk_mul ctx arr] returns an expression representing [arr.(0) * ... * arr.(n)].

   {i Warning!} [Array.length arr] must be greater than zero.
*)
external mk_mul : context -> expr array -> expr
	= "camlidl_yices_yices_mk_mul"

(**
   [mk_lt ctx a1 a2] returns an expression representing [a1 < a2].
*)
external mk_lt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_lt"

(**
   [mk_le ctx a1 a2] returns an expression representing [a1 <= a2].
*)
external mk_le : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_le"

(**
   [mk_gt ctx a1 a2] returns an expression representing [a1 > a2].
*)
external mk_gt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_gt"

(**
   [mk_ge ctx a1 a2] returns an expression representing [a1 >= a2].
*)
external mk_ge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_ge"

(** {3 Bitvector expressions} *)
(**
   Create a bit vector constant of [size] bits and from the given [value].

   [size] must be positive.
*)
external mk_bv_constant : context -> int -> int32 -> expr
	= "camlidl_yices_yices_mk_bv_constant"

(**
   Create a bit vector constant from an array of booleans [bv].

   Bit [i] of the bitvector is set to 0 if [bv.(i)] is [true] and to 1 and to 1 if [bv.(i)] is [false].
*)
external mk_bv_constant_from_array : context -> bool array -> expr
	= "camlidl_yices_yices_mk_bv_constant_from_array"

(**
   [mk_bv_add ctx a1 a2] Bitvector addition

   [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_add : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_add"

(**
   [mk_bv_sub ctx a1 a2] Bitvector subtraction

   [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_sub : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sub"

(**
   [mk_bv_mul ctx a1 a2] Bitvector multiplication

   [a1] and [a2] must be bitvector expression of same size. The result is
   truncated to that size too, e.g., multiplication of two 8-bit vectors
   gives an 8-bit result.
*)
external mk_bv_mul : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_mul"

(**
   [mk_bv_minus ctx a1] Bitvector opposite

   [a1] must be bitvector expression. The result is [(- a1)].
*)
external mk_bv_minus : context -> expr -> expr
	= "camlidl_yices_yices_mk_bv_minus"

(**
  [mk_bv_concat ctx a1 a2] Bitvector concatenation

  [a1] and [a2] must be two bitvector expressions. [a1] is the left
  part of the result and [a2] the right part.

  Assuming [a1] and [a2] have [n1] and [n2] bits, respectively,
  then the result is a bitvector [concat] of size [n1 + n2].  Bit
  0 of [concat] is bit 0 of [a2] and bit [n2] of [concat] is bit 0
  of [a1].
*)
external mk_bv_concat : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_concat"

(**
  [mk_bv_and ctx a1 a2] Bitwise and

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_and : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_and"

(**
  [mk_bv_or ctx a1 a2] Bitwise or

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_or : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_or"

(**
  [mk_bv_xor ctx a1 a2] Bitwise exclusive or

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_xor : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_xor"

(**
  [mk_bv_not ctx a] Bitwise negation
*)
external mk_bv_not : context -> expr -> expr
	= "camlidl_yices_yices_mk_bv_not"

(**
  [mk_bv_extract ctx end begin a] extracts a subvector from the bitvector [a].

  [a] must a bitvector expression of size [n] with [begin < end < n].
  The result is the subvector from [a[begin]] to [a[end]].
*)
external mk_bv_extract : context -> int -> int -> expr -> expr
	= "camlidl_yices_yices_mk_bv_extract"

(**
  [mk_bv_sign_extend ctx a n] returns the sign extension of the bitvector [a] to [n] bits.

  Append [n] times the most-significant bit of [a] to the left of [a].
*)
external mk_bv_sign_extend : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_sign_extend"

(**
  [mk_bv_shift_left0 ctx a n] Left shift by [n] bits, padding with zeros.
*)
external mk_bv_shift_left0 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_left0"

(**
  [mk_bv_shift_left1 ctx a n] Left shift by [n] bits, padding with ones.
*)
external mk_bv_shift_left1 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_left1"

(**
  [mk_bv_shift_right0 ctx a n] Right shift by [n] bits, padding with zeros.
*)
external mk_bv_shift_right0 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_right0"

(**
  [mk_bv_shift_right1 ctx a n] Right shift by [n] bits, padding with ones.
*)
external mk_bv_shift_right1 : context -> expr -> int -> expr
	= "camlidl_yices_yices_mk_bv_shift_right1"

(** {4 Unsigned comparison} *)
(**
  [mk_bv_lt ctx a1 a2] Unsigned comparison: [(a1 < a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_lt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_lt"

(**
  [mk_bv_le ctx a1 a2] Unsigned comparison: [(a1 <= a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_le : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_le"

(**
  [mk_bv_gt ctx a1 a2] Unsigned comparison: [(a1 > a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_gt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_gt"

(**
  [mk_bv_ge ctx a1 a2] Unsigned comparison: [(a1 >= a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_ge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_ge"

(** {4 Signed comparison} *)
(**
  [mk_bv_slt ctx a1 a2] Signed comparison: [(a1 < a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_slt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_slt"

(**
  [mk_bv_sle ctx a1 a2] Signed comparison: [(a1 <= a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_sle : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sle"

(**
  [mk_bv_sgt ctx a1 a2] Signed comparison: [(a1 > a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_sgt : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sgt"

(**
  [mk_bv_sge ctx a1 a2] Signed comparison: [(a1 >= a2)]

  [a1] and [a2] must be bitvector expression of same size.
*)
external mk_bv_sge : context -> expr -> expr -> expr
	= "camlidl_yices_yices_mk_bv_sge"

(** {3 Pretty print expressions} *)
(**
   Pretty print the given expression in the standard output.
*)
external pp_expr : expr -> unit
	= "camlidl_yices_yices_pp_expr"

(** {2 Future} *)
(** Untested and potentially harmful features *)
module Future : sig

(** Given on yices-help by Bruno Dutertre (2009-12-16) *)
external interrupt : context -> unit
	= "camlidl_yices_yices_interrupt"

(** Get the Lite context out of a Full context.
  Be aware to close only the full context!

  Given on yices-help by Bruno Dutertre (2010-06-01)
*)
external get_lite_context : context -> Yicesl.context
	= "camlidl_yices_yices_get_lite_context"

(** Make a function update.

  Found with 'nm': seems to work pretty well
*)
external mk_function_update : context -> expr -> expr array -> expr -> expr
	= "camlidl_yices_yices_mk_function_update"

(** Make a tuple.

  Found with 'nm': seems to work but no really useful without 'select' *)
external mk_tuple_literal : context -> expr array -> expr
	= "camlidl_yices_yices_mk_tuple_literal"

end

