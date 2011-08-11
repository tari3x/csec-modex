// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <lib.h>

#include <string.h>
#include <stdio.h>
#include <stdarg.h>

#include <openssl/rand.h>

/*
  These functions are now stubs, real ones will be using something along the lines of

  #include <openssl/evp.h>
  EVP_PKEY_CTX *EVP_PKEY_CTX_new(EVP_PKEY *pkey, ENGINE *e);
  EVP_PKEY *EVP_PKEY_new(void);
  int EVP_PKEY_set1_RSA(EVP_PKEY *pkey,RSA *key);

  For now it doesn't really matter what's in here because the verification doesn't look into these functions.
*/

extern void nonce(unsigned char * N)
{
  memcpy(N, "nonce", 5);
  RAND_bytes(N + 5, SIZE_NONCE - 5);
}

extern size_t encrypt_len(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  return 7 + sizeof(keylen) + keylen - 2 + inlen;
}

extern size_t encrypt(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  if(keylen < 3)
  {
    fprintf(stderr, "encrypt: key too short\n");
    exit(1);
  }
  if(memcmp(key, "pk", 2))
  {
    fprintf(stderr, "encrypt: wrong key type\n");
    exit(1);
  }

  memcpy(out, "encrypt", 7);
  * (size_t *) (out + 7) = keylen - 2;
  memcpy(out + 7 + sizeof(keylen), key + 2, keylen - 2);
  memcpy(out + 7 + sizeof(keylen) + keylen - 2, in, inlen);

  return 7 + sizeof(keylen) + keylen - 2 + inlen;
}

extern size_t decrypt_len(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen)
{
  if(keylen < 3)
  {
    fprintf(stderr, "decrypt: key too short\n");
    exit(1);
  }
  if(memcmp(key, "sk", 2))
  {
    fprintf(stderr, "decrypt: wrong key type\n");
    exit(1);
  }

  if(inlen < 7 + sizeof(keylen) + 1)
  {
    fprintf(stderr, "decrypt: message too short\n");
    exit(1);
  }
  if(memcmp(in, "encrypt", 7))
  {
    fprintf(stderr, "decrypt: wrong message type\n");
    exit(1);
  }

  size_t keyname_len = * (size_t *) (in + 7);

  if(keyname_len != keylen - 2)
  {
    fprintf(stderr, "decrypt: wrong key(1)\n");
    exit(1);
  }

  if(memcmp(key + 2, in + 7 + sizeof(keyname_len), keyname_len))
  {
    fprintf(stderr, "decrypt: wrong key(2)\n");
    exit(1);
  }

  return inlen - 7 - sizeof(keyname_len) - keyname_len;
}

extern size_t decrypt(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{
  size_t outlen = decrypt_len(key, keylen, in, inlen);

  memcpy(out, in + inlen - outlen, outlen);

  return outlen;
}

unsigned char * get_pkey(size_t * len, char side)
{
  *len = 3;

  char * ret;

  if(side == 'A') ret = "pkA";
  if(side == 'B') ret = "pkB";

  return (unsigned char *) ret;
}

unsigned char * get_skey(size_t * len, char side)
{
  *len = 3;

  char * ret;

  if(side == 'A') ret = "skA";
  if(side == 'B') ret = "skB";

  return (unsigned char *) ret;
}

unsigned char * get_xkey(size_t * len, char side)
{
  *len = 3;

  char * ret;

  if(side == 'A') ret = "pkB";
  if(side == 'B') ret = "pkA";

  return (unsigned char *) ret;
}

void fail(const char * fmt, ...)
{
  va_list argp;
  va_start(argp, fmt);
  vfprintf(stderr, fmt, argp);
  va_end(argp);
  printf("\n");

  // if(c != NULL) wait_close(c);

  exit(1);
}
