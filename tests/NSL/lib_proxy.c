// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <proxies/common.h>
#include <proxies/interface.h>

extern void nonce_proxy(unsigned char * N)
{
  nonce(N);

  symL("nonce", "nonce", SIZE_NONCE, FALSE);
  store_buf(N);
}

extern size_t encrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  size_t ret = encrypt_len(key, keylen, in, inlen);

  symL("encrypt_len", "len", sizeof(ret), FALSE);
  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern size_t encrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  size_t ret = encrypt(key, keylen, in, inlen, out);

  unsigned char nonce[SIZE_NONCE];

  nonce_proxy(nonce);

  load_buf(key, keylen, "key");
  // hm, it would be sensible to set length to keylen here, but right now I don't allow len() inside lens
  symN("isek", "key", NULL, TRUE);
  load_buf(in, inlen, "msg");
  load_buf(nonce, SIZE_NONCE, "nonce");
  symN("E", "cipher", &ret, TRUE);
  store_buf(out);

  if(ret > encrypt_len_proxy(key, keylen, in, inlen))
    fail("encrypt_proxy: bad length");

  return ret;
}

extern size_t decrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  size_t ret = decrypt_len(key, keylen, in, inlen);

  symL("decrypt_len", "len", sizeof(ret), FALSE);
  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern size_t decrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  size_t ret = decrypt(key, keylen, in, inlen, out);

  load_buf(key, keylen, "key");
  load_buf(in, inlen, "cipher");
  symN("D", "msg", &ret, TRUE);
  store_buf(out);

  if(ret > decrypt_len_proxy(key, keylen, in, inlen))
    fail("decrypt_proxy: bad length");

  return ret;
}

unsigned char * get_pkey_proxy(size_t * len, char side)
{
  unsigned char * ret = get_pkey(len, side);

  char name[] = "pkX";
  name[2] = side;

  readenv(ret, len, name);

//  make_sym(len, sizeof(*len), "user_len");
//  make_sym(ret, *len, name);

  return ret;
}


unsigned char * get_skey_proxy(size_t * len, char side)
{
  unsigned char * ret = get_skey(len, side);

  char name[] = "skX";
  name[2] = side;

  readenv(ret, len, name);

//  make_sym(len, sizeof(*len), "user_len");
//  make_sym(ret, *len, name);

  return ret;
}

unsigned char * get_xkey_proxy(size_t * len, char side)
{
  unsigned char * ret = get_xkey(len, side);

  char name[] = "pkX";

  readenv(ret, len, name);

//  make_sym(len, sizeof(*len), "user_len");
//  make_sym(ret, *len, name);

  return ret;
}

