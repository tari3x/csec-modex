
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

/**
 * These are utility functions used by the (annotated) protocol code.
 */

#ifndef PROXY_COMMON
#define PROXY_COMMON

// This should be included by all files that call crest functions explicitly
// #include <crest.h>

#include <stdlib.h>

#include <openssl/bn.h>

#ifdef __cplusplus
	#define EXTERN extern "C"
#else
	#define EXTERN extern
#endif

EXTERN void proxy_fail(const char * fmt, ...);

void readenv(const unsigned char * buf, size_t * len, const char * s);
// shouldn't use this at all?
void make_sym(const unsigned char * buf, size_t len, const char * s);
// void make_simple_sym(const unsigned char * buf, size_t len, const char * s);
void make_str_sym(const char * str, const char * sym);
void event0(const char * s);
void event1(const char * s, const unsigned char * buf, size_t len);
void event2(const char * s, const unsigned char * buf1, size_t len1, const unsigned char * buf2, size_t len2);

// TODO: remove later when using the patcher
#ifdef CSEC_VERIFY
  #undef BN_num_bytes
  extern int BN_num_bytes(BIGNUM const *a);
#endif

#define FALSE 0
#define TRUE  1


#endif /* PROXY_COMMON */
