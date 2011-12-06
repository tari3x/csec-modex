// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// Modified by Marcin Szymczak
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#ifndef LIB_H_
#define LIB_H_

#include <stdlib.h>

#include <openssl/evp.h>
#include <openssl/rsa.h>

#define SIZE_NONCE 20

#define KEY_LENGTH 16

#define AES_BLOCK_SIZE 128

extern void nonce(unsigned char * N);

extern void get_key(unsigned char * ptr);

extern void get_iv(unsigned char * ptr);

extern size_t encrypt_len(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * symkey, unsigned char * iv);
/**
 * Returns actual outlen
*/
extern size_t encrypt(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * symkey, unsigned char * iv, unsigned char * out);

extern size_t decrypt_len(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen);
/**
 * Returns actual outlen
*/
extern size_t decrypt(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out);

EVP_PKEY * get_pkey(size_t * len, char side);
EVP_PKEY * get_skey(size_t * len, char side);
EVP_PKEY * get_xkey(size_t * len, char side);

extern void fail(const char * fmt, ...);

extern void print_buffer(const unsigned char * buf, int len);

#endif /* LIB_H_ */
