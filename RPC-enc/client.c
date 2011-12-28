// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

// Defining out VCC annotations when not verifying
// (useful when running on a non-windows machine without vcc installed)
#ifdef VERIFY
#include <vcc.h>
#else
#define _(...)
#endif

#include "lib.h"
#include "net.h"
#include "rpc-enc.h"

#ifdef CSEC_VERIFY
  #include <proxies/common.h>
#endif

#include <string.h>
#include <stdio.h>
#include <stdint.h>

#ifndef STROPS
#define STROPS
#include <string.h>
#define memcmp_s_u(...)  memcmp(__VA_ARGS__)
#define memcmp_u_u(...)  memcmp(__VA_ARGS__)
#define memcpy_u_u(...)  memcpy(__VA_ARGS__)
#define memcpy_u_s(...)  memcpy(__VA_ARGS__)
#endif

int send_request(RPCstate * ctx)
  _(maintains \wrapped(ctx))
  _(writes &table)
  _(requires Good_Client(*ctx))
  _(ensures \result == 0 ==> Good_Client(*ctx))
  _(requires ctx->k_ab != NULL && ctx->k != NULL && ctx->request != NULL)
{
  uint32_t m1_len, m1_e_len, full_len;
  unsigned char * m1, * p, * m1_e;
  _(ghost uint32_t m1_len_init, m1_e_len_init;)
  _(ghost \claim c;)
  _(ghost bool collision;)

#ifdef VERBOSE
  printf("Client: Preparing to send request: ");
  print_text_buffer(ctx->request,ctx->request_len);
  printf("\nand session key: ");
  print_buffer(ctx->k,ctx->k_len);
  fflush(stdout);
#endif
  _(assume 1 + ctx->k_len + sizeof(ctx->request_len) + ctx->request_len < ULONG_MAX)
  m1_len = 1 + ctx->k_len + sizeof(ctx->request_len) + ctx->request_len;
  p = m1 = malloc(m1_len);
  if (m1 == NULL) return -1;
  _(ghost m1_len_init = m1_len)

  _(assert \active_claim(ctx->c))
  _(ghost c = \make_claim({&table}, table_claim_stable());)
  memcpy_u_s(p, _(precise) ("p"), 1);
  p += 1;
  write_uint32(p,ctx->request_len);
  p += sizeof(ctx->request_len);
  memcpy_u_u(p, ctx->request, ctx->request_len);
  p += ctx->request_len;
  memcpy_u_u(p, ctx->k, ctx->k_len);
  _(ghost _(atomic (&table)) {
    term req, k, tPair;
    req = getTerm(ctx->request,ctx->request_len);
    k   = getTerm(ctx->k,ctx->k_len);
	tPair = Pair(req,k);
	
	if ((table.DefinedB[from_array(m1,m1_len)] && table.B2T[from_array(m1,m1_len)] != tPair) ||
        (table.DefinedT[tPair] && table.T2B[tPair] != from_array(m1,m1_len)))
      collision = \true;
    else
    {
       table.DefinedB[from_array(m1,m1_len)] = \true;
       table.B2T[from_array(m1,m1_len)] = tPair;
	   table.DefinedT[tPair] = \true;
	   table.T2B[tPair] = from_array(m1,m1_len);
    }})
    _(assume !collision)
	_(assert \active_claim(c))
	_(assert getTerm(m1,m1_len) == Pair(getTerm(ctx->request,ctx->request_len),getTerm(ctx->k,ctx->k_len)))
	_(assert Good_Client(*ctx))

  _(ghost c = \upgrade_claim({c}, table_claim_stable());)
  _(assume 1 + sizeof(ctx->self_len) + ctx->self_len + encrypt_len(ctx->k_ab, ctx->k_ab_len, m1, m1_len) < ULONG_MAX)
  full_len = 1 + sizeof(ctx->self_len) + ctx->self_len + encrypt_len(ctx->k_ab, ctx->k_ab_len, m1, m1_len);
  p = m1_e = malloc(full_len);
  if (m1_e == NULL)
  {
    free(SPEC_CAST(unsigned char[m1_len_init],m1));
    return -1;
  }
  memcpy_u_s(p, _(precise)("p"), 1);
  p += 1;
  write_uint32(p,ctx->self_len);
  p += sizeof(ctx->self_len);
  memcpy_u_u(p, ctx->self, ctx->self_len);
  p += ctx->self_len;
  _(assert \active_claim(c))
  _(ghost c = \upgrade_claim({c}, table_claim_stable());)
  m1_e_len = encrypt(ctx->k_ab, ctx->k_ab_len, m1, m1_len, p _(ghost c));
  full_len = 1 + sizeof(ctx->self_len) + ctx->self_len + m1_e_len;
  _(assert \active_claim(c))
  _(ghost _(atomic (&table)) {
    term clientID, ctxt, tPair;
    clientID = getTerm(ctx->self,ctx->self_len);
    ctxt   = getTerm(m1,m1_len);
	_(assert ctxt == Pair(getTerm(ctx->request,ctx->request_len),getTerm(ctx->k,ctx->k_len)))
	tPair = Pair(clientID,ctxt);
	
	if ((table.DefinedB[from_array(m1_e,full_len)] && table.B2T[from_array(m1_e,full_len)] != tPair) ||
        (table.DefinedT[tPair] && table.T2B[tPair] != from_array(m1_e,full_len)))
      collision = \true;
    else
    {
       table.DefinedB[from_array(m1_e,full_len)] = \true;
       table.B2T[from_array(m1_e,full_len)] = tPair;
	   table.DefinedT[tPair] = \true;
	   table.T2B[tPair] = from_array(m1_e,full_len);
    }})
  _(assert \active_claim(c))
  _(assert Good_Client(*ctx))

#ifdef VERBOSE
  printf("Client: Sending message: %.1s | %u | ", m1_e, *((uint32_t*) (m1_e + 1)));
  print_text_buffer(m1_e + 1 + sizeof(uint32_t),ctx->self_len);
  printf(" | ");
  print_buffer(p,m1_e_len);
  fflush(stdout);
#endif

  send_uint32(&(ctx->bio), NOSPEC_CAST(unsigned char *,&full_len), sizeof(full_len));
  send(&(ctx->bio), m1_e, full_len);

  free(SPEC_CAST(unsigned char[m1_len_init],m1));
  free(SPEC_CAST(unsigned char[m1_e_len_init],m1_e));

  return 0;
}

int recv_response(RPCstate * ctx)
  _(updates ctx)
  _(writes &table)
  _(requires Good_Client(*ctx))
  _(maintains ctx->k_ab != NULL && ctx->k != NULL && ctx->request != NULL)
  _(ensures \result == 0 ==> ctx->response != NULL)
  _(ensures \result == 0 ==> Good_Client(*ctx))
{
  unsigned char * m2_e;
  uint32_t m2_e_len;
  _(ghost uint32_t m2_e_len_init, response_len_init)
  _(ghost \claim c)

  _(assert \active_claim(ctx->c))
  _(ghost c = \make_claim({&table}, table_claim_stable()))
  recv_uint32(&(ctx->bio), NOSPEC_CAST(unsigned char*,&m2_e_len), sizeof(m2_e_len));
  m2_e = malloc(m2_e_len);
  if (m2_e == NULL) return -1;
  _(ghost m2_e_len_init = m2_e_len)
  recv(&(ctx->bio), m2_e, m2_e_len);
  _(assert \active_claim(c))
  _(ghost c = \upgrade_claim({c}, table_claim_stable()))

#ifdef VERBOSE
  printf("Client: Received encrypted message: ");
  print_buffer(m2_e,m2_e_len);
  fflush(stdout);
#endif

  _(unwrap(ctx))
  ctx->response_len = decrypt_len(ctx->k, ctx->k_len, m2_e, m2_e_len);
  _(ghost response_len_init = ctx->response_len)
  ctx->response = malloc(ctx->response_len);
  if (ctx->response == NULL)
  {
    free(SPEC_CAST(unsigned char[m2_e_len_init],m2_e));
	_(wrap(ctx))
    return -1;
  }
  // this call returns 0 if not encrypted with the right key
  ctx->response_len = decrypt(ctx->k, ctx->k_len, m2_e, m2_e_len, ctx->response _(ghost ctx->c));
  _(wrap((unsigned char[response_len_init]) ctx->response))
  _(ghost ctx->\owns += (unsigned char[response_len_init]) ctx->response)
  if (ctx->response_len == 0)
  {
    free(SPEC_CAST(unsigned char[m2_e_len_init],m2_e));
    _(wrap(ctx))
    return -1;
  }
  _(assert \active_claim(c))
  _(wrap(ctx))

#ifdef VERBOSE
    printf("Client: Received and authenticated response: ");
    print_text_buffer(ctx->response,ctx->response_len);
    printf("\n");
    fflush(stdout);
#endif

  return 0;
}

int parseargs(int argc, char ** argv, RPCstate * ctx)
{
  int port_len, pwr = 1;

  if (argc != 4 && argc != 5)
    return -1;

  ctx->self_len = strlen(argv[1]);
  if (ctx->self_len == 0)
  {
    _(assert \is_array(DEFAULTHOST,9))
    ctx->self_len = strlen(DEFAULTHOST);
    ctx->self = malloc(ctx->self_len);
    if (ctx->self == NULL)
      return -1;
    memcpy(ctx->self,DEFAULTHOST,ctx->self_len);
  }
  else
  {
    ctx->self = malloc(ctx->self_len);
    if (ctx->self == NULL)
      return -1;
    memcpy((char*) ctx->self,argv[1],ctx->self_len);
  }

  ctx->other_len = strlen(argv[2]);
  if (ctx->other_len == 0)
  {
    _(assert \is_array(DEFAULTHOST,9))
    ctx->other_len = strlen(DEFAULTHOST);
    ctx->other = malloc(ctx->other_len);
    if (ctx->other == NULL)
      return -1;
    memcpy(ctx->other,DEFAULTHOST,ctx->other_len);
  }
  else
  {
    ctx->other = malloc(ctx->self_len);
    if (ctx->other == NULL)
      return -1;
    memcpy((char*) ctx->other,argv[2],ctx->other_len);
  }

#ifdef CSEC_VERIFY
  // Assumption that the corresponding argv fields indeed contains the correct ids:
  readenvE(ctx->self, &(ctx->self_len), sizeof(ctx->self_len), "clientID");
  readenvE(ctx->other, &(ctx->other_len), sizeof(ctx->other_len), "serverID");
#endif

  ctx->port = 0;
  if (argc == 5)
  {
    port_len = (int) strlen(argv[3]);
    if (port_len > 5)
      return -1;
    for (; port_len > 0; port_len--)
    {
      if (argv[3][port_len - 1] < '0' || argv[3][port_len - 1] > '9')
        return -1;
      ctx->port += (argv[3][port_len - 1] - 48) * pwr;
      pwr *= 10;
    }
  }
  if (ctx->port <= 0 || ctx->port >= 65536)
  {
    ctx->port = DEFAULTPORT;
  }

  // This chunk could be defined as being "get_request()"
  ctx->request_len = strlen(argv[argc - 1]);
  if (ctx->request_len == 0)
    ctx->request = NULL;
  else
  {
    ctx->request = malloc(ctx->request_len);
    if (ctx->request == NULL)
      return -1;
    memcpy((char*) ctx->request,argv[argc - 1],ctx->request_len);
  }

#ifdef CSEC_VERIFY
  // Assumption that the argv field indeed contains the request from the environment:
  readenvE(ctx->request, &(ctx->request_len), sizeof(ctx->request_len), "request");
#endif

  return 0;
}

//Begin ClientCode
int main(int argc, char ** argv)
  _(requires \program_entry_point())
{
  RPCstate clState;

  clState.end = CLIENT;

  if (parseargs(argc,argv,&clState) < 0)
  {
#ifdef VERBOSE
    fprintf(stdout, "Usage: client clientAddress serverAddress [port] request\n");
#endif
    exit(-1);
  }

#ifdef VERBOSE
  printf("Client: Now connecting to %s, port %d.\n", clState.other, clState.port);
  fflush(stdout);
#endif
  // Getting arguments
  if (socket_connect(&(clState.bio),(char*) clState.other, clState.other_len, clState.port))
    return -1;
  clState.k_ab = get_shared_key(clState.self, clState.self_len, clState.other, clState.other_len, &(clState.k_ab_len) _(ghost clState.c));
  clState.k = mk_session_key(&(clState.k_len));
  clState.response = NULL;

#ifdef CSEC_VERIFY
  event3("client_begin", clState.self, clState.self_len, clState.other, clState.other_len, clState.request, clState.request_len);
#endif

  /* Send request */
  if (send_request(&clState) < 0) return -1;

  /* Receive response */
  if (recv_response(&clState) < 0) return -1;

  _(ghost \unwrap(&clState);)
#ifdef CSEC_VERIFY
  event4("client_accept", clState.self, clState.self_len, clState.other, clState.other_len,
                          clState.request, clState.request_len, clState.response, clState.response_len);
#endif

  return 0;
}
//End ClientCode
