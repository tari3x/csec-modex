// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <proxies/common.h>
#include <proxies/interface.h>
#include <proxies/system-proxies.h>

#include <string.h>

unsigned char * otp_proxy(size_t len)
{
  char * ret = otp(len);

  readenvL(ret, len, "pad");

  return ret;
}

extern void xor_proxy(unsigned char * buf, unsigned char * pad, size_t len)
{
  xor(buf, pad, len);

  load_buf(buf, len, NULL);
  load_buf(pad, len, NULL);
  symL("XOR", "xor", len, TRUE);
  store_buf(buf);
}
