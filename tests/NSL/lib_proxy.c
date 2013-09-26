// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <proxies/common.h>
#include <proxies/interface.h>
// Temporary
#include <crest.h>

extern void nonce_proxy(unsigned char * N)
{
  nonce(N);

  newTL(SIZE_NONCE, "nonce", "nonce");
  store_buf(N);
}

extern size_t encrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  size_t ret = encrypt_len(key, keylen, in, inlen);

  // No hint, to avoid term duplication.
  load_buf(in, inlen, "");
  symL("encrypt_len", "", sizeof(ret), TRUE);

  duplicate();
  assume_intype("bitstring");

  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern size_t encrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  size_t ret = encrypt(key, keylen, in, inlen, out);

    load_buf(in, inlen, "msg");
      load_buf(key, keylen, "key");
      // hm, it would be sensible to set length to keylen here, but right now I don't allow len() inside lens
    symNE("isek", "key", NULL, 0, TRUE, 1);
    // FIXME: what's the actual seed length?
    newTL(256, "seed_T", "nonce");
  symN("E", "cipher", &ret, TRUE);
  store_buf(out);

  if(ret > encrypt_len_proxy(key, keylen, in, inlen))
    fail("encrypt_proxy: bad length");

  return ret;
}

extern size_t decrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  size_t ret = decrypt_len(key, keylen, in, inlen);

  // No hint, to avoid term duplication.
  load_buf(in, inlen, "");
  //  symL("decrypt_len", "", sizeof(ret), TRUE);
  SymN("decrypt_len", 1);

  duplicate();
  test_intype("bitstring");

  SetLen(sizeof(ret));
  Done();

  store_buf(&ret);

  // Assume that the length of the decryption is at most the length of the ciphertext.
  if(ret < 0 || ret > inlen) exit(1);

  return ret;
}

extern size_t decrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  size_t ret = decrypt(key, keylen, in, inlen, out);

  load_buf(in, inlen, "cipher");
  load_buf(key, keylen, "key");
  symN("D", "msg", NULL, TRUE);
  symN("inverse_injbot", "msg", &ret, TRUE);
  store_buf(out);

  if(ret > decrypt_len_proxy(key, keylen, in, inlen))
    fail("decrypt_proxy: bad length");

  return ret;
}

unsigned char * get_sigkey_proxy(size_t * len)
{
  unsigned char * ret = get_sigkey(len);
  readenv(ret, len, "pkS");
  return ret;
}

unsigned char * get_pkey_proxy(size_t * len, char side)
{
  unsigned char * ret = get_pkey(len, side);

  char name[] = "pkX";
  name[2] = side;

  readenv(ret, len, name);

  if(*len > 100)
    fail("pkey too long");

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

  if(*len > 100)
    fail("pkey too long");

//  make_sym(len, sizeof(*len), "user_len");
//  make_sym(ret, *len, name);

  return ret;
}

unsigned char * get_xkey_proxy(size_t * len, const unsigned char * host, size_t host_len)
{
  unsigned char * ret = get_xkey(len, host, host_len);

  char name[] = "pkX";

  readenv(ret, len, name);

  if(*len > 100)
    fail("pkey too long");

//  make_sym(len, sizeof(*len), "user_len");
//  make_sym(ret, *len, name);

  return ret;
}

unsigned char * get_xsig_proxy(size_t * len, const unsigned char * host, size_t host_len)
{
  unsigned char * ret = get_xsig(len, host, host_len);
  char name[] = "sigX";
  readenv(ret, len, name);
  return ret;
}

unsigned char * get_host_proxy(size_t * len, char side)
{
  unsigned char * ret = get_host(len, side);
  char name[] = "hostX";
  name[4] = side;
  readenv(ret, len, name);

  if(*len > 40)
    fail("host name too long");

  return ret;
}

unsigned char * get_xhost_proxy(size_t * len, char side)
{
  unsigned char * ret = get_xhost(len, side);
  char name[] = "hostX";
  readenv(ret, len, name);

  if(*len > 40)
    fail("host name too long");

  return ret;
}

bool check_key_proxy(const unsigned char * host, size_t host_len,
               const unsigned char * key, size_t key_len,
               const unsigned char * sig, size_t sig_len,
               const unsigned char * sigkey, size_t sigkey_len)
{
  bool ret = check_key(host, host_len, key, key_len, sig, sig_len, sigkey, sigkey_len);

  load_buf(host, host_len, "host");
  load_buf(key, key_len, "key");
  load_buf(sig, sig_len, "sig");
  load_buf(sigkey, sigkey_len, "sigkey");

  symL("check_key", NULL, sizeof(ret), TRUE);

  store_buf(&ret);

  return ret;
}
