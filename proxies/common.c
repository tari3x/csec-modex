
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "common.h"

#include "interface.h"
#include "crest.h"

#include <stdio.h>

// void var(const char * name, const unsigned char * buf, const unsigned char * len, size_t lenlen)

void readenvE(const unsigned char * buf, const unsigned char * len, size_t lenlen, const char * name)
{
  if(lenlen == 0)
  {
    proxy_fail("readenvE: you certainly don't want lenlen = 0\n");
  }

  Env(name);
  assume_intype("bitstring");

  Dup();
  Len();
  BS(FALSE, lenlen);
  Done();
  // Assume that variable length fits in its bitstring representation.
  assume_intype("bitstring");

  if(len != NULL)
    StoreBuf(len);
  else
    Clear(1);

  // len will most probably be incomparable with the length of the buffer contents,
  // so we use StoreAll.
  StoreAll(buf);
}

void readenv(const unsigned char * buf, const size_t * len, const char * name)
{
  readenvE(buf, len, sizeof(*len), name);
}


void readenvL(const unsigned char * buf, size_t len, const char * name)
{
  Env(name);
  assume_intype("bitstring");
  assume_len(&len, FALSE, sizeof(len));

  // See readenv for why we use StoreAll
  StoreAll(buf);
}

void make_sym(const unsigned char * buf, size_t len, const char * s)
{
  SymN(s, 0);
  assume_len(&len, FALSE, sizeof(len));
  Hint(s);
  Nondet();
  store_buf(buf);
}

void event0(const char * s)
{
  event(s, 0);
}

void event1(const char * s, const unsigned char * buf, size_t len)
{
  load_buf(buf, len, "");
  event(s, 1);
}

void event2(const char * s, const unsigned char * buf1, size_t len1, const unsigned char * buf2, size_t len2)
{
  load_buf(buf1, len1, "");
  load_buf(buf2, len2, "");
  event(s, 2);
}

void event3(const char * s, const unsigned char * buf1, size_t len1,
                            const unsigned char * buf2, size_t len2,
                            const unsigned char * buf3, size_t len3)
{
  load_buf(buf1, len1, "");
  load_buf(buf2, len2, "");
  load_buf(buf3, len3, "");
  event(s, 3);
}

void event4(const char * s, const unsigned char * buf1, size_t len1,
                            const unsigned char * buf2, size_t len2,
                            const unsigned char * buf3, size_t len3,
                            const unsigned char * buf4, size_t len4)
{
  load_buf(buf1, len1, "");
  load_buf(buf2, len2, "");
  load_buf(buf3, len3, "");
  load_buf(buf4, len4, "");
  event(s, 4);
}

void typehint(const unsigned char * buf, size_t len, const char * type)
{
  load_buf(buf, len, "");
  TypeHint(type);
  store_buf(buf);
}

void append_zero(const unsigned char * buf)
{
  load_all(buf, "");
  SymN("ztpSafe", 1);
  load_all(buf, "");
  SymN("=", 2);
  Assume();

  load_all(buf, "");
  load_int(0, TRUE, sizeof(char), "");
  // load_str("00");
  Append();
  store_all(buf);
}
