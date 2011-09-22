// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "interface.h"

#include "crest.h"

// Things implemented in crestify.cpp:
// mute, unmute

void load_buf(const unsigned char * buf, size_t len, const char * hint)
{
  LoadBuf(buf, len);
  Hint(hint);
}

void load_all(const char * buf, const char * hint)
{
  LoadAll(buf);
  Hint(hint);
}

void load_ctx(const void * ctx, const char * attr, const char * hint)
{
  LoadAttr(ctx, attr);
  Hint(hint);
}

void load_int(int n, const char * hint)
{
  LoadInt(n);
  Hint(hint);
}

void symL(const char * sym, const char * hint, size_t len, int deterministic)
{
  Sym(sym);
  SetLen(len);
  if(!deterministic) Nondet();
  Done();
  if(hint != NULL) Hint(hint);
}

void symNE(const char * sym, const char * hint, unsigned char * len, size_t lenlen, int deterministic)
{
  Sym(sym);
  if(!deterministic) Nondet();
  Done();
  if(hint != NULL) Hint(hint);

  if(len != NULL)
  {
    Dup();
    SymN("len", 1);
    SetLen(lenlen);
    Done();
    Hint("len");
    StoreBuf(len);
  }
}

void symN(const char * sym, const char * hint, size_t * len, int deterministic)
{
  symNE(sym, hint, len, sizeof(*len), deterministic);
}

void var(const char * name, const unsigned char * buf, const unsigned char * len, size_t lenlen)
{
  LoadStr(name);
  Sym("var");
  Done();
  Hint(name);

  Dup();
  SymN("len", 1);
  SetLen(lenlen);
  Done();
  Hint("len");

  StoreBuf(len);
  StoreBuf(buf);
}

void store_buf(const unsigned char * buf)
{
  StoreBuf(buf);
}

void store_all(const char * buf)
{
  StoreAll(buf);
}

void store_ctx(const void * ctx, const char * attr)
{
  StoreAttr(ctx, attr);
}

/*long int lhs_int(long int n, const char * hint)
{
  Hint(hint);
  CustomReturn();
  return n;
}*/

void event()
{
  Event();
}

void add_to_attr(const void * ctx, const char * attr, const unsigned char * buf, size_t len)
{
  LoadAttr(ctx, attr);
  LoadBuf(buf, len);
  Append();
  StoreAttr(ctx, attr);
}

/*
 * FIXME: potential unsoundness because of bypassing buffer2string()
 */
void set_attr_str(const void * ctx, const char * attr, const char * str)
{
  LoadStr(str);
  StoreAttr(ctx, attr);
}

void set_attr_buf(const void * ctx, const char * attr, const unsigned char * buf, size_t len)
{
  LoadBuf(buf, len);
  StoreAttr(ctx, attr);
}

void set_attr_int(const void * ctx, const char * attr, int n)
{
  LoadInt(n);
  StoreAttr(ctx, attr);

  StoreRuntimeInt(ctx, attr, n);
}

int get_attr_int(const void * ctx, const char * attr)
{
  LoadAttr(ctx, attr);
  CustomReturn();
  return LoadRuntimeInt(ctx, attr);
}

void clear_attr(const void * ctx, const char * attr)
{
  set_attr_str(ctx, attr, "");
}

void copy_ctx(const void * to, const void * from)
{
  CopyCtx(to, from);
}

void copy_attr_ex(const void * to, const char * attr_to, const void * from, const char * attr_from)
{
  LoadAttr(from, attr_from);
  StoreAttr(to, attr_to);
}

void copy_attr(const void * to, const void * from, const char * attr)
{
  copy_attr_ex(to, attr, from, attr);
}

long int concrete_val(long int n)
{
  __CrestLoadInt(n);
  CustomReturn();
  return n;
}

//void * fresh_ptr(void * p, int size)
//{
//  NewHeapPtr(size);
//  CustomReturn();
//  return p;
//}

void fresh_ptr(int size)
{
  NewHeapPtr(size);
}


void sym_return()
{
  CustomReturn();
}
