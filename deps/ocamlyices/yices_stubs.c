/* File generated from yices.idl */

#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>


#include "yices.h"

extern void camlidl_ml2c_yicesl_yicesl_context(value, yicesl_context *, camlidl_ctx _ctx);
extern value camlidl_c2ml_yicesl_yicesl_context(yicesl_context *, camlidl_ctx _ctx);

extern void camlidl_ml2c_yicesl_yicesl_error(value, yicesl_error *, camlidl_ctx _ctx);
extern value camlidl_c2ml_yicesl_yicesl_error(yicesl_error *, camlidl_ctx _ctx);

void camlidl_ml2c_yices_yices_context(value _v1, yices_context * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_context *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_context(yices_context * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_context) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_context *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yices_yices_type(value _v1, yices_type * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_type *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_type(yices_type * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_type) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_type *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yices_yices_type_ptr(value _v1, yices_type_ptr * _c2, camlidl_ctx _ctx)
{
  (*_c2) = (yices_type  *) camlidl_malloc(sizeof(yices_type ), _ctx);
  camlidl_ml2c_yices_yices_type(_v1, &*(*_c2), _ctx);
}

value camlidl_c2ml_yices_yices_type_ptr(yices_type_ptr * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_c2ml_yices_yices_type(&*(*_c2), _ctx);
  return _v1;
}

void camlidl_ml2c_yices_yices_expr(value _v1, yices_expr * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_expr *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_expr(yices_expr * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_expr) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_expr *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yices_yices_var_decl(value _v1, yices_var_decl * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_var_decl *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_var_decl(yices_var_decl * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_var_decl) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_var_decl *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yices_yices_model(value _v1, yices_model * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_model *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_model(yices_model * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_model) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_model *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yices_assertion_id(value _v1, assertion_id * _c2, camlidl_ctx _ctx)
{
  (*_c2) = Int_val(_v1);
}

value camlidl_c2ml_yices_assertion_id(assertion_id * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = Val_int((*_c2));
  return _v1;
}

void camlidl_ml2c_yices_yices_error(value _v1, yices_error * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_error *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_error(yices_error * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_error) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_error *) Bp_val(_v1)) = *_c2;
  return _v1;
}

int camlidl_transl_table_yices_enum_1[3] = {
  False,
  Undef,
  True,
};

int camlidl_ml2c_yices_enum_lbool(value _v1)
{
  int _c2;
  _c2 = camlidl_transl_table_yices_enum_1[Int_val(_v1)];
  return _c2;
}

value camlidl_c2ml_yices_enum_lbool(int _c1)
{
  value _v2;
  switch(_c1) {
  case False: _v2 = Val_int(0); break;
  case Undef: _v2 = Val_int(1); break;
  case True: _v2 = Val_int(2); break;
  default: invalid_argument("enum lbool: bad enum lbool value");
  }
  return _v2;
}

void camlidl_ml2c_yices_yices_var_decl_iterator(value _v1, yices_var_decl_iterator * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yices_var_decl_iterator *) Bp_val(_v1));
}

value camlidl_c2ml_yices_yices_var_decl_iterator(yices_var_decl_iterator * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yices_var_decl_iterator) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yices_var_decl_iterator *) Bp_val(_v1)) = *_c2;
  return _v1;
}

value camlidl_yices_yices_version(value _unit)
{
  char *_res;
  value _vres;

  _res = yices_version();
  _vres = copy_string(_res);
  return _vres;
}

value camlidl_yices_yices_set_verbosity(
	value _v_l)
{
  int l; /*in*/
  l = Int_val(_v_l);
  yices_set_verbosity(l);
  return Val_unit;
}

value camlidl_yices_yices_set_max_num_conflicts_in_maxsat_iteration(
	value _v_n)
{
  unsigned int n; /*in*/
  n = Int_val(_v_n);
  yices_set_max_num_conflicts_in_maxsat_iteration(n);
  return Val_unit;
}

value camlidl_yices_yices_enable_type_checker(
	value _v_flag)
{
  int flag; /*in*/
  flag = Int_val(_v_flag);
  yices_enable_type_checker(flag);
  return Val_unit;
}

value camlidl_yices_yices_set_max_num_iterations_in_maxsat(
	value _v_n)
{
  unsigned int n; /*in*/
  n = Int_val(_v_n);
  yices_set_max_num_iterations_in_maxsat(n);
  return Val_unit;
}

value camlidl_yices_yices_set_maxsat_initial_cost(
	value _v_c)
{
  long long c; /*in*/
  c = Int64_val(_v_c);
  yices_set_maxsat_initial_cost(c);
  return Val_unit;
}

value camlidl_yices_yices_set_arith_only(
	value _v_flag)
{
  int flag; /*in*/
  flag = Int_val(_v_flag);
  yices_set_arith_only(flag);
  return Val_unit;
}

value camlidl_yices_yices_enable_log_file(
	value _v_file_name)
{
  char *file_name; /*in*/
  file_name = String_val(_v_file_name);
  yices_enable_log_file(file_name);
  return Val_unit;
}

value camlidl_yices_yices_mk_context(value _unit)
{
  yices_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = yices_mk_context();
  check_context(_res);
  _vres = camlidl_c2ml_yices_yices_context(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_del_context(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_del_context(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_reset(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_reset(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_dump_context(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_dump_context(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_push(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_push(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_pop(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_pop(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_assert(
	value _v_ctx,
	value _v_expr)
{
  yices_context ctx; /*in*/
  yices_expr expr; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_expr, &expr, _ctx);
  yices_assert(ctx, expr);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_assert_weighted(
	value _v_ctx,
	value _v_expr,
	value _v_w)
{
  yices_context ctx; /*in*/
  yices_expr expr; /*in*/
  long long w; /*in*/
  assertion_id _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_expr, &expr, _ctx);
  w = Int64_val(_v_w);
  _res = yices_assert_weighted(ctx, expr, w);
  _vres = camlidl_c2ml_yices_assertion_id(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_assert_retractable(
	value _v_ctx,
	value _v_expr)
{
  yices_context ctx; /*in*/
  yices_expr expr; /*in*/
  assertion_id _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_expr, &expr, _ctx);
  _res = yices_assert_retractable(ctx, expr);
  _vres = camlidl_c2ml_yices_assertion_id(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_retract(
	value _v_ctx,
	value _v_id)
{
  yices_context ctx; /*in*/
  assertion_id id; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_assertion_id(_v_id, &id, _ctx);
  yices_retract(ctx, id);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_inconsistent(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_inconsistent(ctx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_check(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  enter_blocking_section();
  _res = yices_check(ctx);
  leave_blocking_section();
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_find_weighted_model(
	value _v_ctx,
	value _v_random)
{
  yices_context ctx; /*in*/
  int random; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  random = Int_val(_v_random);
  enter_blocking_section();
  _res = yices_find_weighted_model(ctx, random);
  leave_blocking_section();
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_max_sat(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  enter_blocking_section();
  _res = yices_max_sat(ctx);
  leave_blocking_section();
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_max_sat_cost_leq(
	value _v_c,
	value _v_max_cost)
{
  yices_context c; /*in*/
  long long max_cost; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_c, &c, _ctx);
  max_cost = Int64_val(_v_max_cost);
  enter_blocking_section();
  _res = yices_max_sat_cost_leq(c, max_cost);
  leave_blocking_section();
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_yices_struct_unsat_core(value _v1, struct unsat_core * _c2, camlidl_ctx _ctx)
{
  mlsize_t _c3;
  mlsize_t _c4;
  value _v5;
  _c3 = Wosize_val(_v1);
  (*_c2).array = camlidl_malloc(_c3 * sizeof(assertion_id ), _ctx);
  for (_c4 = 0; _c4 < _c3; _c4++) {
    _v5 = Field(_v1, _c4);
    camlidl_ml2c_yices_assertion_id(_v5, &(*_c2).array[_c4], _ctx);
  }
  (*_c2).length = _c3;
}

value camlidl_c2ml_yices_struct_unsat_core(struct unsat_core * _c1, camlidl_ctx _ctx)
{
  value _v2;
  mlsize_t _c3;
  value _v4;
  _v2 = camlidl_alloc((*_c1).length, 0);
  Begin_root(_v2)
    for (_c3 = 0; _c3 < (*_c1).length; _c3++) {
      _v4 = camlidl_c2ml_yices_assertion_id(&(*_c1).array[_c3], _ctx);
      modify(&Field(_v2, _c3), _v4);
    }
  End_roots()
  return _v2;
}

value camlidl_yices_get_unsat_core(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct unsat_core _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = get_unsat_core(ctx);
  _vres = camlidl_c2ml_yices_struct_unsat_core(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
free(_res.array);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_yices_yices_get_model(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  yices_model _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_get_model(ctx);
  check_model(_res);
  _vres = camlidl_c2ml_yices_yices_model(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_evaluate_in_model(
	value _v_m,
	value _v_e)
{
  yices_model m; /*in*/
  yices_expr e; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_e, &e, _ctx);
  _res = yices_evaluate_in_model(m, e);
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_value(
	value _v_m,
	value _v_v)
{
  yices_model m; /*in*/
  yices_var_decl v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_v, &v, _ctx);
  _res = yices_get_value(m, v);
  _vres = camlidl_c2ml_yices_enum_lbool(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_int_value(
	value _v_m,
	value _v_d)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  long *v; /*out*/
  yices_error _res;
  long _c1;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  v = &_c1;
  _res = yices_get_int_value(m, d, v);
  check_yices_error(_res);
  _vres = copy_int32(*v);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_arith_value(
	value _v_m,
	value _v_d)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  long *num; /*out*/
  long *den; /*out*/
  yices_error _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  long _c1;
  long _c2;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  num = &_c1;
  den = &_c2;
  _res = yices_get_arith_value(m, d, num, den);
  check_yices_error(_res);
  Begin_roots_block(_vres, 2)
    _vres[0] = copy_int32(*num);
    _vres[1] = copy_int32(*den);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_yices_yices_get_double_value(
	value _v_m,
	value _v_d)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  double *v; /*out*/
  yices_error _res;
  double _c1;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  v = &_c1;
  _res = yices_get_double_value(m, d, v);
  check_yices_error(_res);
  _vres = copy_double(*v);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_bitvector_value(
	value _v_m,
	value _v_d,
	value _v_n)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  unsigned int n; /*in*/
  int *bv; /*out*/
  yices_error _res;
  mlsize_t _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  n = Int_val(_v_n);
  bv = camlidl_malloc(n * sizeof(int ), _ctx);
  _res = yices_get_bitvector_value(m, d, n, bv);
  check_yices_error(_res);
  _vres = camlidl_alloc(n, 0);
  for (_c1 = 0; _c1 < n; _c1++) {
    _v2 = Val_int(bv[_c1]);
    modify(&Field(_vres, _c1), _v2);
  }
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_get_rational_value_as_string(
	value _v_m,
	value _v_d)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  char *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  _res = get_rational_value_as_string(m, d);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
if (_res) free(_res);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_yices_get_integer_value_as_string(
	value _v_m,
	value _v_d)
{
  yices_model m; /*in*/
  yices_var_decl d; /*in*/
  char *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  _res = get_integer_value_as_string(m, d);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
if (_res) free(_res);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_yices_yices_get_assertion_value(
	value _v_m,
	value _v_id)
{
  yices_model m; /*in*/
  assertion_id id; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  camlidl_ml2c_yices_assertion_id(_v_id, &id, _ctx);
  _res = yices_get_assertion_value(m, id);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_display_model(
	value _v_m)
{
  yices_model m; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  yices_display_model(m);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_get_cost(
	value _v_m)
{
  yices_model m; /*in*/
  long long _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  _res = yices_get_cost(m);
  _vres = copy_int64(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_cost_as_double(
	value _v_m)
{
  yices_model m; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_model(_v_m, &m, _ctx);
  _res = yices_get_cost_as_double(m);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_type(
	value _v_ctx,
	value _v_name)
{
  yices_context ctx; /*in*/
  char *name; /*in*/
  yices_type _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  name = String_val(_v_name);
  _res = yices_mk_type(ctx, name);
  check_type(_res);
  _vres = camlidl_c2ml_yices_yices_type(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_function_type(
	value _v_ctx,
	value _v_domain,
	value _v_range)
{
  yices_context ctx; /*in*/
  yices_type *domain; /*in*/
  unsigned int domain_size; /*in*/
  yices_type range; /*in*/
  yices_type _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(yices_type ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_yices_yices_type(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_yices_yices_type(_v_range, &range, _ctx);
  _res = yices_mk_function_type(ctx, domain, domain_size, range);
  check_type(_res);
  _vres = camlidl_c2ml_yices_yices_type(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bitvector_type(
	value _v_ctx,
	value _v_size)
{
  yices_context ctx; /*in*/
  unsigned int size; /*in*/
  yices_type _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  size = Int_val(_v_size);
  _res = yices_mk_bitvector_type(ctx, size);
  check_type(_res);
  _vres = camlidl_c2ml_yices_yices_type(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_tuple_type(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_type_ptr *args; /*in*/
  unsigned int size; /*in*/
  yices_type _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_type_ptr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_type_ptr(_v3, &args[_c2], _ctx);
  }
  size = _c1;
  _res = yices_mk_tuple_type(ctx, args, size);
  check_type(_res);
  _vres = camlidl_c2ml_yices_yices_type(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_true(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_mk_true(ctx);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_false(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_mk_false(ctx);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bool_var(
	value _v_ctx,
	value _v_name)
{
  yices_context ctx; /*in*/
  char *name; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  name = String_val(_v_name);
  _res = yices_mk_bool_var(ctx, name);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_fresh_bool_var(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_mk_fresh_bool_var(ctx);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_var_decl(
	value _v_e)
{
  yices_expr e; /*in*/
  yices_var_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_expr(_v_e, &e, _ctx);
  _res = yices_get_var_decl(e);
  check_var_decl(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bool_var_decl(
	value _v_ctx,
	value _v_name)
{
  yices_context ctx; /*in*/
  char *name; /*in*/
  yices_var_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  name = String_val(_v_name);
  _res = yices_mk_bool_var_decl(ctx, name);
  check_var_decl(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_var_decl_name(
	value _v_d)
{
  yices_var_decl d; /*in*/
  char *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  _res = yices_get_var_decl_name(d);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bool_var_from_decl(
	value _v_ctx,
	value _v_d)
{
  yices_context ctx; /*in*/
  yices_var_decl d; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  _res = yices_mk_bool_var_from_decl(ctx, d);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_or(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_or(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_and(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_and(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_eq(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_eq(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_diseq(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_diseq(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_ite(
	value _v_ctx,
	value _v_c,
	value _v_t,
	value _v_e)
{
  yices_context ctx; /*in*/
  yices_expr c; /*in*/
  yices_expr t; /*in*/
  yices_expr e; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_c, &c, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_t, &t, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_e, &e, _ctx);
  _res = yices_mk_ite(ctx, c, t, e);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_not(
	value _v_ctx,
	value _v_a)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  _res = yices_mk_not(ctx, a);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_create_var_decl_iterator(
	value _v_c)
{
  yices_context c; /*in*/
  yices_var_decl_iterator _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_c, &c, _ctx);
  _res = yices_create_var_decl_iterator(c);
  check_var_decl_iterator(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl_iterator(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_iterator_has_next(
	value _v_it)
{
  yices_var_decl_iterator it; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_var_decl_iterator(_v_it, &it, _ctx);
  _res = yices_iterator_has_next(it);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_iterator_next(
	value _v_it)
{
  yices_var_decl_iterator it; /*in*/
  yices_var_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_var_decl_iterator(_v_it, &it, _ctx);
  _res = yices_iterator_next(it);
  check_var_decl(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_iterator_reset(
	value _v_it)
{
  yices_var_decl_iterator it; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_var_decl_iterator(_v_it, &it, _ctx);
  yices_iterator_reset(it);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_del_iterator(
	value _v_it)
{
  yices_var_decl_iterator it; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_var_decl_iterator(_v_it, &it, _ctx);
  yices_del_iterator(it);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_mk_var_decl(
	value _v_ctx,
	value _v_name,
	value _v_ty)
{
  yices_context ctx; /*in*/
  char *name; /*in*/
  yices_type ty; /*in*/
  yices_var_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  name = String_val(_v_name);
  camlidl_ml2c_yices_yices_type(_v_ty, &ty, _ctx);
  _res = yices_mk_var_decl(ctx, name, ty);
  check_var_decl(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_get_var_decl_from_name(
	value _v_ctx,
	value _v_name)
{
  yices_context ctx; /*in*/
  char *name; /*in*/
  yices_var_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  name = String_val(_v_name);
  _res = yices_get_var_decl_from_name(ctx, name);
  check_var_decl(_res);
  _vres = camlidl_c2ml_yices_yices_var_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_var_from_decl(
	value _v_ctx,
	value _v_d)
{
  yices_context ctx; /*in*/
  yices_var_decl d; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_var_decl(_v_d, &d, _ctx);
  _res = yices_mk_var_from_decl(ctx, d);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_app(
	value _v_ctx,
	value _v_f,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr f; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_app(ctx, f, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_num(
	value _v_ctx,
	value _v_n)
{
  yices_context ctx; /*in*/
  int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_num(ctx, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_num_from_string(
	value _v_ctx,
	value _v_n)
{
  yices_context ctx; /*in*/
  char *n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  n = String_val(_v_n);
  _res = yices_mk_num_from_string(ctx, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_sum(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_sum(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_sub(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_sub(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_mul(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_mul(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_lt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_lt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_le(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_le(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_gt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_gt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_ge(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_ge(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_constant(
	value _v_ctx,
	value _v_size,
	value _v_val)
{
  yices_context ctx; /*in*/
  unsigned int size; /*in*/
  long val; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  size = Int_val(_v_size);
  val = Int32_val(_v_val);
  _res = yices_mk_bv_constant(ctx, size, val);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_constant_from_array(
	value _v_ctx,
	value _v_bv)
{
  yices_context ctx; /*in*/
  unsigned int size; /*in*/
  int *bv; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_bv);
  bv = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bv, _c2);
    bv[_c2] = Int_val(_v3);
  }
  size = _c1;
  _res = yices_mk_bv_constant_from_array(ctx, size, bv);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_add(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_add(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_sub(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_sub(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_mul(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_mul(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_minus(
	value _v_ctx,
	value _v_a1)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  _res = yices_mk_bv_minus(ctx, a1);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_concat(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_concat(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_and(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_and(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_or(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_or(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_xor(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_xor(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_not(
	value _v_ctx,
	value _v_a1)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  _res = yices_mk_bv_not(ctx, a1);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_extract(
	value _v_ctx,
	value _v_end,
	value _v_begin,
	value _v_a)
{
  yices_context ctx; /*in*/
  unsigned int end; /*in*/
  unsigned int begin; /*in*/
  yices_expr a; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  end = Int_val(_v_end);
  begin = Int_val(_v_begin);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  _res = yices_mk_bv_extract(ctx, end, begin, a);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_sign_extend(
	value _v_ctx,
	value _v_a,
	value _v_n)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_bv_sign_extend(ctx, a, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_shift_left0(
	value _v_ctx,
	value _v_a,
	value _v_n)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_bv_shift_left0(ctx, a, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_shift_left1(
	value _v_ctx,
	value _v_a,
	value _v_n)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_bv_shift_left1(ctx, a, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_shift_right0(
	value _v_ctx,
	value _v_a,
	value _v_n)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_bv_shift_right0(ctx, a, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_shift_right1(
	value _v_ctx,
	value _v_a,
	value _v_n)
{
  yices_context ctx; /*in*/
  yices_expr a; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a, &a, _ctx);
  n = Int_val(_v_n);
  _res = yices_mk_bv_shift_right1(ctx, a, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_lt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_lt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_le(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_le(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_gt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_gt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_ge(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_ge(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_slt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_slt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_sle(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_sle(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_sgt(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_sgt(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_bv_sge(
	value _v_ctx,
	value _v_a1,
	value _v_a2)
{
  yices_context ctx; /*in*/
  yices_expr a1; /*in*/
  yices_expr a2; /*in*/
  yices_expr _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a1, &a1, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_a2, &a2, _ctx);
  _res = yices_mk_bv_sge(ctx, a1, a2);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_pp_expr(
	value _v_e)
{
  yices_expr e; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_expr(_v_e, &e, _ctx);
  yices_pp_expr(e);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_interrupt(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  yices_interrupt(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yices_yices_get_lite_context(
	value _v_ctx)
{
  yices_context ctx; /*in*/
  yicesl_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _res = yices_get_lite_context(ctx);
  check_yicesl_context(_res);
  _vres = camlidl_c2ml_yicesl_yicesl_context(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_function_update(
	value _v_ctx,
	value _v_f,
	value _v_args,
	value _v_val)
{
  yices_context ctx; /*in*/
  yices_expr f; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr val; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  camlidl_ml2c_yices_yices_expr(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  camlidl_ml2c_yices_yices_expr(_v_val, &val, _ctx);
  _res = yices_mk_function_update(ctx, f, args, n, val);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yices_yices_mk_tuple_literal(
	value _v_ctx,
	value _v_args)
{
  yices_context ctx; /*in*/
  yices_expr *args; /*in*/
  unsigned int n; /*in*/
  yices_expr _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yices_yices_context(_v_ctx, &ctx, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(yices_expr ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_yices_yices_expr(_v3, &args[_c2], _ctx);
  }
  n = _c1;
  _res = yices_mk_tuple_literal(ctx, args, n);
  check_expr(_res);
  _vres = camlidl_c2ml_yices_yices_expr(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

