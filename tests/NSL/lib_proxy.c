// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"
#include "net.h"

#include <proxies/common.h>
#include <proxies/interface.h>
// Temporary
#include <crest.h>

extern void nonce_proxy(unsigned char * N)
{
  mute();
  nonce(N);
  unmute();

  newTL(SIZE_NONCE, "nonce", "nonce");
  store_buf(N);
}

extern size_t encrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  mute();
  size_t ret = encrypt_len(key, keylen, in, inlen);
  unmute();

  // No hint here because encrypt_len will be opaque for the solver,
  // so we should keep its contents in.
  load_buf(in, inlen, "");
  SymN("encrypt_len", 1);
  assume_intype("bitstring");
  assume_len(sizeof(ret));
  // Give a hint to make sure the function application is exposed to CV,
  // so that we can communicate length-regularity properties.
  Hint("len");

  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern size_t encrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  mute();
  size_t ret = encrypt(key, keylen, in, inlen, out);
  unmute();

  load_buf(in, inlen, "msg");
  load_buf(key, keylen, "key");
  // hm, it would be sensible to set length to keylen here, but right now I don't allow len() inside lens
  SymN("isek", 1);
  Hint("key");
  // FIXME: what's the actual seed length?
  newTL(256, "seed_T", "nonce");
  SymN("E", 3);
  Hint("cipher");
  store_len(&ret, sizeof(ret), FALSE);
  store_buf(out);

  if(ret > encrypt_len_proxy(key, keylen, in, inlen))
    fail("encrypt_proxy: bad length");

  return ret;
}

extern size_t decrypt_len_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  mute();
  size_t ret = decrypt_len(key, keylen, in, inlen);
  unmute();

  // No hint, to avoid term duplication.
  load_buf(in, inlen, "");
  //  symL("decrypt_len", "", sizeof(ret), TRUE);
  SymN("decrypt_len", 1);

  test_intype("bitstring");

  assume_len(sizeof(ret));
  Done();

  store_buf(&ret);

  // Assume that the length of the decryption is at most the length of the ciphertext.
  if(ret < 0 || ret > inlen) exit(1);

  return ret;
}

extern size_t decrypt_proxy(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  mute();
  size_t ret = decrypt(key, keylen, in, inlen, out);
  unmute();

  load_buf(in, inlen, "cipher");
  load_buf(key, keylen, "key");
  SymN("D", 2);
  Hint("msg");
  SymN("inverse_injbot", 1);
  Hint("msg");
  store_len(&ret, sizeof(ret), FALSE);
  store_buf(out);

  if(ret > decrypt_len_proxy(key, keylen, in, inlen))
    fail("decrypt_proxy: bad length");

  return ret;
}

unsigned char * get_sigkey_proxy(size_t * len)
{
  mute();
  unsigned char * ret = get_sigkey(len);
  unmute();

  stack_ptr("get_sigkey_ret");
  StoreBuf(&ret);

  readenv(ret, len, "pkS");
  return ret;
}

unsigned char * get_pkey_proxy(size_t * len, char side)
{
  mute();
  unsigned char * ret = get_pkey(len, side);
  unmute();

  stack_ptr("get_pkey_ret");
  StoreBuf(&ret);

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
  mute();
  unsigned char * ret = get_skey(len, side);
  unmute();

  stack_ptr("get_skey_ret");
  StoreBuf(&ret);

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
  mute();
  unsigned char * ret = get_xkey(len, host, host_len);
  unmute();

  stack_ptr("get_xkey_ret");
  StoreBuf(&ret);

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
  mute();
  unsigned char * ret = get_xsig(len, host, host_len);
  unmute();

  stack_ptr("get_xsig_ret");
  StoreBuf(&ret);

  char name[] = "sigX";
  readenv(ret, len, name);
  return ret;
}

unsigned char * get_host_proxy(size_t * len, char side)
{
  mute();
  unsigned char * ret = get_host(len, side);
  unmute();

  stack_ptr("get_host_ret");
  StoreBuf(&ret);

  char name[] = "hostX";
  name[4] = side;
  readenv(ret, len, name);

  if(*len > 40)
    fail("host name too long");

  return ret;
}

unsigned char * get_xhost_proxy(size_t * len, char side)
{
  mute();
  unsigned char * ret = get_xhost(len, side);
  unmute();

  stack_ptr("get_xhost_ret");
  StoreBuf(&ret);

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
  mute();
  bool ret = check_key(host, host_len, key, key_len, sig, sig_len, sigkey, sigkey_len);
  unmute();

  load_buf(host, host_len, "host");
  load_buf(key, key_len, "key");
  load_buf(sig, sig_len, "sig");
  load_buf(sigkey, sigkey_len, "sigkey");

  SymT("(check_key : bitstring * bitstring * bitstring * bitstring -> bool)");
  SymN("bs_of_truth[1]", 1);
  assume_len(sizeof(ret));

  store_buf(&ret);

  return ret;
}

void print_buffer_proxy(const unsigned char * buf, int len)
{
  mute();
  print_buffer(buf, len);
  unmute();
}

extern void wait_close_proxy(BIO *c )
{
  mute();
  wait_close(c);
  unmute();
}

