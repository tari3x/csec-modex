// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#ifdef VERIFY
#include <vcc.h>
#include <stdlib.h>
#include "table.h"
#else
#define _(...)
#endif

#ifndef VERIFY
#define SPEC_CAST(_TYPE_,_EXPR_) _EXPR_
#define NOSPEC_CAST(_TYPE_,_EXPR_) (_TYPE_) _EXPR_

#define recv_uint32(...)  recv(__VA_ARGS__)
#define send_uint32(...)  send(__VA_ARGS__)

#define parse_uint32(_PTR_)        *((uint32_t *) (_PTR_))
#define write_uint32(_PTR_,_VAL_)  *((uint32_t *) (_PTR_)) = _VAL_
#else
#include <limits.h>
#include <stdint.h>
#define SPEC_CAST(_TYPE_,_EXPR_)   (_TYPE_) _EXPR_
#define NOSPEC_CAST(_TYPE_,_EXPR_) _EXPR_

_(ghost _(pure) uint32_t bytesToU32(ByteString b)
    _(requires b.length == 4);)
_(ghost _(pure) ByteString u32ToBytes(uint32_t i)
    _(ensures \result.length == 4);)

int recv_uint32(int* fd, uint32_t* buf, unsigned long len)
  _(out_param buf);
void send_uint32(int* fd, uint32_t* buf, unsigned long len);
	
uint32_t _(pure) parse_uint32(unsigned char* buf)
  _(reads \array_range(buf,sizeof(uint32_t)))
  _(requires \is_array(buf,sizeof(uint32_t)))
  _(ensures \result == bytesToU32(from_array(buf,sizeof(uint32_t))));
void write_uint32(unsigned char* buf, uint32_t value)
  _(writes \array_range(buf,sizeof(uint32_t)))
  _(ensures bytesToU32(from_array(buf,sizeof(uint32_t))) == value);

_(abstract \integer pwr10(\integer x)
    _(requires x >= 0)
    _(ensures x == 0 ==> \result == 1)
    _(ensures x > 0 ==> \result == 10 * pwr10(x - 1))
  {
    if (x == 0)
	  return 1;
	else
      return 10 * pwr10(x - 1);
  })

_(ghost _(pure) bool trigNTstring(char* s)
  _(returns \true);)

_(logic bool isNTstring(char * s, uint32_t l) =
    \mutable_array(s,l+1) && s[l] == '\0' && \forall uint32_t i; s[i] == '\0' ==> i >= l)

_(logic bool isMutableNTstring(char * s, uint32_t l) =
    \mutable_array(s,l+1) && s[l] == '\0' && \forall uint32_t i; s[i] == '\0' ==> i >= l)

_(logic bool isNTstring(char * s) =
   (trigNTstring(s) &&
    \exists uint32_t l;
       isNTstring(s,l)))

_(logic bool isMutableNTstring(char * s) =
   (trigNTstring(s) &&
    \exists uint32_t l;
       isMutableNTstring(s,l)))

_(logic bool isWrappedNTstring(char *s, uint32_t l) =
    \wrapped((unsigned char[l + 1]) s) && s[l] == '\0' && \forall uint32_t i; s[i] == '\0' ==> i >= l)

#ifndef STROPS
#define STROPS
// Ad hoc polymorphism through overloading
_(pure) uint32_t strlen(const char* s _(ghost uint32_t len))
  _(reads \universe())
  _(requires isNTstring(s,len))
  _(ensures \result == len);

_(pure) int memcmp_u_u ( unsigned char * ptr1, unsigned char * ptr2, uint32_t num )
  _(reads \universe())
  _(requires \thread_local_array(ptr1,num))
  _(requires \thread_local_array(ptr2,num))
  _(ensures \result == (\forall uint32_t i; i < num ==> ptr1[i] == ptr2[i]));

_(pure) int memcmp_s_u ( const char * ptr1, const unsigned char * ptr2, uint32_t num )
  _(reads \universe())
  _(requires \thread_local_array(ptr1,num))
  _(requires \thread_local_array(ptr2,num))
  _(ensures \result == (\forall uint32_t i; i < num ==> (unsigned char) ptr1[i] == ptr2[i]));

_(pure) int memcmp_u_s ( const unsigned char * ptr1, const char * ptr2, uint32_t num )
  _(reads \universe())
  _(requires \thread_local_array(ptr1,num))
  _(requires \thread_local_array(ptr2,num))
  _(ensures \result == (\forall uint32_t i; i < num ==> ptr1[i] == (unsigned char) ptr2[i]));

void * memcpy_u_u ( unsigned char * destination, const unsigned char * source, uint32_t num )
  _(writes \array_range(destination,num))
  _(requires \disjoint(\array_range(destination,num),\array_range(source,num)))
  _(maintains \thread_local_array(destination,num))
  _(maintains \thread_local_array(source,num))
  _(ensures \forall uint32_t i; i < num ==> destination[i] == \old(source[i]))
  _(ensures (unsigned char*) \result == destination);

void * memcpy_u_s ( unsigned char * destination, const char * source, uint32_t num )
  _(writes \array_range(destination,num))
  _(requires \disjoint(\array_range(destination,num),\array_range(source,num)))
  _(maintains \thread_local_array(destination,num))
  _(maintains \thread_local_array(source,num))
  _(ensures \forall uint32_t i; i < num ==> destination[i] == \old(source[i]))
  _(ensures (unsigned char*) \result == destination);
#endif
#endif

enum protEnd {CLIENT, SERVER};

_(logic term getTerm(unsigned char* ptr, uint32_t len) =
    table.B2T[from_array(ptr,len)])
	
typedef _(dynamic_owns) struct RPCstate_s
{
  enum protEnd end;
  int port;
  _(invariant 0 <= port && port < 65535)

  _(ghost \claim c;)
  _(invariant \mine(c))
  _(invariant \claims(c, (&table)->\consistent))

  unsigned char * self;
  uint32_t self_len;
  _(invariant self != NULL ==>
      \mine((unsigned char[self_len]) self))

  unsigned char * other;
  uint32_t other_len;
  _(invariant other != NULL ==>
      \mine((unsigned char[other_len]) other))

  // Long-Term Key
  unsigned char * k_ab;
  uint32_t k_ab_len;
  _(invariant k_ab != NULL ==>
      \mine((unsigned char[k_ab_len]) k_ab) &&
	  self != NULL && other != NULL)

  // Request
  unsigned char * request;
  uint32_t request_len;
  _(invariant request != NULL ==>
      \mine((unsigned char[request_len]) request) &&
      k_ab != NULL)
  
  // Session Key
  unsigned char * k;
  uint32_t k_len;
  _(invariant k != NULL ==>
      \mine((unsigned char[k_len]) k) &&
      request != NULL)

  // Response
  unsigned char * response;
  uint32_t response_len;
  _(invariant response != NULL ==>
      \mine((unsigned char[response_len]) response) &&
      k != NULL)

  // Channel/Socket
  int bio;
} RPCstate;

_(logic bool Good_Client(RPCstate s) =
    s.end == CLIENT &&
	0 < s.port && s.port < 65536 &&
    (s.self != NULL ==> s.self_len > 0 && table.DefinedB[from_array(s.self,s.self_len)] && Level(Low,getTerm(s.self,s.self_len))) &&
	(s.other != NULL ==> s.other_len > 0 && table.DefinedB[from_array(s.other,s.other_len)] && Level(Low,getTerm(s.other,s.other_len))) &&
	(s.k_ab != NULL ==> s.k_ab_len > 0 && table.DefinedB[from_array(s.k_ab,s.k_ab_len)] && log.New[getTerm(s.k_ab,s.k_ab_len)][SEncKey(U_RPCKeyAB(getTerm(s.self,s.self_len),getTerm(s.other,s.other_len)))]) &&
	(s.request != NULL ==> s.request_len > 0 && table.DefinedB[from_array(s.request,s.request_len)] && log.New[getTerm(s.request,s.request_len)][Nonce(U_Request(getTerm(s.self,s.self_len),getTerm(s.other,s.other_len)))]) &&
	(s.k != NULL ==> s.k_len > 0 && table.DefinedB[from_array(s.k,s.k_len)] && log.New[getTerm(s.k,s.k_len)][SEncKey(U_RPCSessionKey(getTerm(s.self,s.self_len),getTerm(s.other,s.other_len),getTerm(s.request,s.request_len)))]) &&
	(s.response != NULL ==> s.response_len > 0 && table.DefinedB[from_array(s.response,s.response_len)] && log.New[getTerm(s.response,s.response_len)][Nonce(U_Response(getTerm(s.self,s.self_len),getTerm(s.other,s.other_len),getTerm(s.request,s.request_len)))]))

_(logic bool Good_Server(RPCstate s) =
    s.end == SERVER &&
	0 < s.port && s.port < 65536 &&
    (s.self != NULL ==> s.self_len > 0 && table.DefinedB[from_array(s.self,s.self_len)] && Level(Low,getTerm(s.self,s.self_len))) &&
	(s.other != NULL ==> s.other_len > 0 && table.DefinedB[from_array(s.other,s.other_len)] && Level(Low,getTerm(s.other,s.other_len))) &&
	(s.k_ab != NULL ==> s.k_ab_len > 0 && table.DefinedB[from_array(s.k_ab,s.k_ab_len)] && log.New[getTerm(s.k_ab,s.k_ab_len)][SEncKey(U_RPCKeyAB(getTerm(s.other,s.other_len),getTerm(s.self,s.self_len)))]) &&
	(s.request != NULL ==> s.request_len > 0 && table.DefinedB[from_array(s.request,s.request_len)] && log.New[getTerm(s.request,s.request_len)][Nonce(U_Request(getTerm(s.other,s.other_len),getTerm(s.self,s.self_len)))]) &&
	(s.k != NULL ==> s.k_len > 0 && table.DefinedB[from_array(s.k,s.k_len)] && log.New[getTerm(s.k,s.k_len)][SEncKey(U_RPCSessionKey(getTerm(s.other,s.other_len),getTerm(s.self,s.self_len),getTerm(s.request,s.request_len)))]) &&
	(s.response != NULL ==> s.response_len > 0 && table.DefinedB[from_array(s.response,s.response_len)] && log.New[getTerm(s.response,s.response_len)][Nonce(U_Response(getTerm(s.other,s.other_len),getTerm(s.self,s.self_len),getTerm(s.request,s.request_len)))]))
