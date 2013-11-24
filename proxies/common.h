
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
#include <stdint.h>

#include <openssl/bn.h>

#ifdef __cplusplus
	#define EXTERN extern "C"
#else
	#define EXTERN extern
#endif

EXTERN void proxy_fail(const char * fmt, ...);

void readenv(const unsigned char * buf, const size_t * len, const char * s);
/**
 * A version that does not assume a particular length size.
 * lenlen should be an appropriate value even if len is NULL.
 */
void readenvE(const unsigned char * buf, const unsigned char * len, size_t lenlen, const char * s);
/**
 * A fixed-length version. In terms of paper CVM this corresponds to reading from
 * the environment and then checking that the length is indeed of the requested size.
 */
void readenvL(const unsigned char * buf, size_t len, const char * s);
// shouldn't use this at all?
void make_sym(const unsigned char * buf, size_t len, const char * s);
// void make_simple_sym(const unsigned char * buf, size_t len, const char * s);
void make_str_sym(const char * str, const char * sym);
void event0(const char * s);
void event1(const char * s, const unsigned char * buf, size_t len);
void event2(const char * s, const unsigned char * buf1, size_t len1,
                            const unsigned char * buf2, size_t len2);
void event3(const char * s, const unsigned char * buf1, size_t len1,
                            const unsigned char * buf2, size_t len2,
                            const unsigned char * buf3, size_t len3);
void event4(const char * s, const unsigned char * buf1, size_t len1,
                            const unsigned char * buf2, size_t len2,
                            const unsigned char * buf3, size_t len3,
                            const unsigned char * buf4, size_t len4);

void typehint(const unsigned char * buf, size_t len, const char * type);

/**
 * Adds an assumption that buf does not contain zero and appends zero to buf.
 */
void append_zero(const unsigned char * buf);

#define FALSE 0
#define TRUE  1


#endif /* PROXY_COMMON */
