/* File generated from yicesl.idl */

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


#include "yicesl.h"

void camlidl_ml2c_yicesl_yicesl_context(value _v1, yicesl_context * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yicesl_context *) Bp_val(_v1));
}

value camlidl_c2ml_yicesl_yicesl_context(yicesl_context * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yicesl_context) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yicesl_context *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_yicesl_yicesl_error(value _v1, yicesl_error * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((yicesl_error *) Bp_val(_v1));
}

value camlidl_c2ml_yicesl_yicesl_error(yicesl_error * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(yicesl_error) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((yicesl_error *) Bp_val(_v1)) = *_c2;
  return _v1;
}

value camlidl_yicesl_yicesl_set_verbosity(
	value _v_l)
{
  int l; /*in*/
  l = Int_val(_v_l);
  yicesl_set_verbosity(l);
  return Val_unit;
}

value camlidl_yicesl_yicesl_version(value _unit)
{
  char *_res;
  value _vres;

  _res = yicesl_version();
  _vres = copy_string(_res);
  return _vres;
}

value camlidl_yicesl_yicesl_enable_type_checker(
	value _v_flag)
{
  int flag; /*in*/
  flag = Int_val(_v_flag);
  yicesl_enable_type_checker(flag);
  return Val_unit;
}

value camlidl_yicesl_yicesl_enable_log_file(
	value _v_file_name)
{
  char *file_name; /*in*/
  file_name = String_val(_v_file_name);
  yicesl_enable_log_file(file_name);
  return Val_unit;
}

value camlidl_yicesl_yicesl_mk_context(value _unit)
{
  yicesl_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = yicesl_mk_context();
  check_yicesl_context(_res);
  _vres = camlidl_c2ml_yicesl_yicesl_context(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yicesl_yicesl_del_context(
	value _v_ctx)
{
  yicesl_context ctx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yicesl_yicesl_context(_v_ctx, &ctx, _ctx);
  yicesl_del_context(ctx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yicesl_yicesl_read(
	value _v_ctx,
	value _v_cmd)
{
  yicesl_context ctx; /*in*/
  char const *cmd; /*in*/
  yicesl_error _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yicesl_yicesl_context(_v_ctx, &ctx, _ctx);
  cmd = String_val(_v_cmd);
  enter_blocking_section();
  _res = yicesl_read(ctx, cmd);
  leave_blocking_section();
  check_yicesl_error(_res);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_yicesl_yicesl_inconsistent(
	value _v_ctx)
{
  yicesl_context ctx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_yicesl_yicesl_context(_v_ctx, &ctx, _ctx);
  _res = yicesl_inconsistent(ctx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_yicesl_yicesl_set_output_file(
	value _v_file_name)
{
  char *file_name; /*in*/
  file_name = String_val(_v_file_name);
  yicesl_set_output_file(file_name);
  return Val_unit;
}

