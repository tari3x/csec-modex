// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#ifndef LIB_H_
#define LIB_H_

#include <stdlib.h>

#define SIZE_NONCE 20

extern void nonce(unsigned char * N);

extern size_t encrypt_len(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen);
/**
 * Returns actual outlen
*/
extern size_t encrypt(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out);

extern size_t decrypt_len(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen);
/**
 * Returns actual outlen
*/
extern size_t decrypt(unsigned char * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out);

unsigned char * get_pkey(size_t * len, char side);
unsigned char * get_skey(size_t * len, char side);
unsigned char * get_xkey(size_t * len, char side);

extern void fail(const char * fmt, ...);

#endif /* LIB_H_ */
