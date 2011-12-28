// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#ifndef LIB_H_
#define LIB_H_

#ifdef VERIFY
#include <vcc.h>
#include "table.h"
#else
#define _(...)
#endif

#include <stdlib.h>
#include <stdint.h>

extern _(pure) uint32_t encrypt_len(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
  _(reads \array_range(key,keylen))
  _(reads \array_range(in,inlen))
  _(returns inlen + 32);
/**
 * Returns actual outbuflen
*/
extern uint32_t encrypt(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * outbuf _(ghost \claim c))
  _(always c, (&table)->\consistent)
  _(writes c)
  _(requires \thread_local_array(key,keylen))
  _(requires \thread_local_array(in,inlen))
  _(writes \array_range(outbuf, encrypt_len(key,keylen,in,inlen)))
  _(ensures \result <= encrypt_len(key,keylen,in,inlen))
  _(requires table.DefinedB[from_array(key,keylen)] && table.DefinedB[from_array(in,inlen)])
  _(ensures table.DefinedB[from_array(outbuf,\result)])
  _(ensures \result != 0 ==> getTerm(outbuf,\result) == SEnc(getTerm(key,keylen),getTerm(in,inlen)));

extern _(pure) uint32_t decrypt_len(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
  _(reads \array_range(key,keylen))
  _(reads \array_range(in,inlen))
  _(returns inlen - 32);
/**
 * Returns actual outbuflen
*/
extern uint32_t decrypt(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * outbuf _(ghost \claim c))
  _(always c, (&table)->\consistent)
  _(requires \thread_local_array(key,keylen))
  _(requires \thread_local_array(in,inlen))
  _(requires table.DefinedB[from_array(key,keylen)] && table.DefinedB[from_array(in,inlen)])
  _(writes \array_range(outbuf,decrypt_len(key,keylen,in,inlen)))
  _(ensures \result == decrypt_len(key,keylen,in,inlen))
  _(ensures table.DefinedB[from_array(outbuf,\result)])
  _(ensures \result != 0 ==> getTerm(in,inlen) == SEnc(getTerm(key,keylen),getTerm(outbuf,\result)));

unsigned char * get_shared_key(unsigned char* client, uint32_t client_len, unsigned char* server, uint32_t server_len, uint32_t * len _(ghost \claim c))
  _(always c, (&table)->\consistent)
  _(writes (&table), len)
  _(requires \thread_local_array(client,client_len))
  _(requires \thread_local_array(server,server_len))
  _(ensures table_stable()) // This is probably not needed in general. Check for performance impact?
  _(ensures \wrapped((unsigned char[*len]) \result) && \malloc_root((unsigned char[*len]) \result) && \fresh((unsigned char[*len]) \result) && \result != NULL)
  _(ensures log.New[getTerm(\result,*len)][SEncKey(U_RPCKeyAB(getTerm(client,client_len),getTerm(server,server_len)))]);

unsigned char * mk_session_key(uint32_t * len /*_(ghost Bytes client) _(ghost Bytes server) _(ghost Bytes request)*/)
  _(ensures \wrapped((unsigned char[*len]) \result))
  /*_(ensures Logged(New(from_bytes(\result,*len),SessionKey(client,server,request))))*/;
unsigned char * get_response(uint32_t * len /*_(ghost Bytes client) _(ghost Bytes server) _(ghost Bytes request)*/)
  _(writes len)
  _(ensures \wrapped((unsigned char[*len]) \result) && \malloc_root((unsigned char[*len]) \result) && \fresh((unsigned char[*len]) \result) && \result != NULL)
  /*_(ensures Logged(New(from_bytes(\result,*len),RPCResponse(client,server,request))))*/;

extern void print_buffer(const unsigned char * buf, int len);

extern void print_text_buffer(const unsigned char * buf, int len);

extern void fail(const char * fmt, ...);

#endif /* LIB_H_ */
