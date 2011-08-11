
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "common.h"

#include "interface.h"

#include <stdio.h>

void readenv(const unsigned char * buf, size_t * len, const char * s)
{
//  char s_len[100] = "test";
//  mute();
//  if(snprintf(s_len, 100, "%s_len", s) == 100) proxy_fail("make_sym: symbol too long: %s", s);
//  unmute();
//
//  sym("user_len", s_len, TRUE, sizeof(*len), FALSE);
//  store_buf((void*) len);
  //*len = lhs_int(*len, s_len);

  //if(*len < 0) proxy_fail("make_sym: len is negative: %s", s);
  // if((int) *len != *len) error("make_sym: len doesn't fit into int: %s", s);

  var(s, buf, len, sizeof(*len));
}

void make_sym(const unsigned char * buf, size_t len, const char * s)
{
  symL(s, s, len, FALSE);
  store_buf(buf);
}

void make_str_sym(const char * str, const char * s)
{
  // Length value not really used so far, but might be if someone calls strlen for instance.
  // But then need a non-zero assumption anyway, so will wait what becomes necessary
  symN(s, s, NULL, FALSE);
  store_all(str);
}

void event0(const char * s)
{
  symL(s, s, 0, FALSE);
  symL("event", "event", 0, FALSE);
  event();
}

void event1(const char * s, const unsigned char * buf, size_t len)
{
  load_buf(buf, len, "");
  symL(s, s, 0, FALSE);
  symL("event", "event", 0, FALSE);
  event();
}

void event2(const char * s, const unsigned char * buf1, size_t len1, const unsigned char * buf2, size_t len2)
{
  load_buf(buf1, len1, "");
  load_buf(buf2, len2, "");
  symL(s, s, 0, FALSE);
  symL("event", "event", 0, FALSE);
  event();
}
