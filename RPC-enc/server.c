// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <stdio.h>
#include <stdint.h>

#include "lib.h"
#include "net.h"
#include "rpc-enc.h"

#ifdef CSEC_VERIFY
  #include <proxies/common.h>
#endif

#ifndef STROPS
#define STROPS
#include <string.h>
#define memcmp_s_u(...)  memcmp(__VA_ARGS__)
#define memcmp_u_u(...)  memcmp(__VA_ARGS__)
#define memcpy_u_u(...)  memcpy(__VA_ARGS__)
#define memcpy_u_s(...)  memcpy(__VA_ARGS__)
#endif

int recv_request(RPCstate * ctx)
  _(updates ctx)
  _(writes &table)
  _(requires ctx->self != NULL)
  _(requires ctx->other == NULL)
  _(requires (unsigned char[ctx->self_len]) ctx->self \in ctx->\owns)
  _(requires Good_Server(*ctx))
  _(ensures \result == 0 ==> Good_Server(*ctx))
  _(ensures \unchanged(ctx->bio))
  _(ensures \unchanged(ctx->self))
  _(ensures \result == 0 ==> \subset({(unsigned char[ctx->other_len]) ctx->other,(unsigned char[ctx->request_len]) ctx->request,(unsigned char[ctx->k_ab_len]) ctx->k_ab,(unsigned char[ctx->k_len]) ctx->k}, ctx->\owns))
  _(ensures \result == 0 ==> ctx->k != NULL)
{
  unsigned char * m1_e, * m1, * p;
  uint32_t m1_e_len, m1_len;
  _(ghost uint32_t m1_e_len_init, m1_len_init) // Save actual allocated lengths for calls to free()
  _(ghost \claim c;)
  _(ghost bool collision;)
  _(ghost \state s;)

  _(unwrap(ctx))
  _(assert \active_claim(ctx->c))
  _(ghost c = \make_claim({ctx->c,&table},
                table_claim_stable() &&
                log_claim_stable()))
  recv_uint32(&(ctx->bio), NOSPEC_CAST(unsigned char*,&m1_e_len), sizeof(m1_e_len));
  _(assert \active_claim(c))
  if (m1_e_len < 1 + sizeof(uint32_t))
  {
    _(wrap(ctx))
    return -1;
  }
  _(ghost m1_e_len_init = m1_e_len)
  
  p = m1_e = malloc(m1_e_len);
  if (m1_e == NULL)
  {
    _(wrap(ctx))
    return -1;
  }
  recv(&(ctx->bio), m1_e, m1_e_len);

  if (memcmp_s_u(_(precise)("p"), p, 1))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message not properly tagged as a pair, aborting.\n");
#endif
    exit(-1);
    _(assume \false)
  }
  p += 1;

  ctx->other_len = parse_uint32(p);
  _(assume 1 + sizeof(uint32_t) + ctx->other_len < ULONG_MAX)
  if (m1_e_len <= 1 + sizeof(uint32_t) + ctx->other_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message has wrong length.\n");
#endif
    exit(-1);
    _(assume \false)
  }
  p += sizeof(uint32_t);

  ctx->other = malloc(ctx->other_len);
  if (ctx->other == NULL)
  {
    _(wrap(ctx))
    return -1;
  }
  _(ghost c = \upgrade_claim({c},table_claim_stable())) // We refine VCC's knowledge by upgrading the claim (we are simply updating the reference state)
  memcpy_u_u(ctx->other,p,ctx->other_len);
  _(assert \active_claim(c))
  _(wrap((unsigned char[ctx->other_len]) ctx->other))
  _(ghost ctx->\owns += (unsigned char[ctx->other_len]) ctx->other)
  p += ctx->other_len;
  _(ghost _(atomic (&table)) {
      term clientID, ctxt;
      term tpair = getTerm(m1_e,m1_e_len);
	  if (!table.DefinedB[from_array(ctx->other,ctx->other_len)] ||
	      !table.DefinedB[from_array(p,m1_e_len - 1 - sizeof(uint32_t) - ctx->other_len)])
        collision = \true;
      else
      {
        clientID = getTerm(ctx->other,ctx->other_len);
        ctxt = getTerm(p,m1_e_len - 1 - sizeof(uint32_t) - ctx->other_len);
      }
	  if (tpair != Pair(clientID,ctxt))
        collision = \true;
      })
  _(assume !collision)
  _(assert \active_claim(c))
  _(assert Good_Server(*ctx))
  
  if (m1_e_len < 1 + sizeof(uint32_t) + ctx->other_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message has wrong length.\n");
#endif
    exit(-1);
    _(assume \false)
  }
  m1_e_len -= (1 + sizeof(ctx->other_len) + ctx->other_len);

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Received message: %.1s | %u | ", m1_e, *((uint32_t*) (m1_e + 1)));
  print_text_buffer(m1_e + 1 + sizeof(uint32_t),ctx->other_len);
  printf(" | ");
  print_buffer(p, m1_e_len);
  fflush(stdout);
#endif
#endif

  _(ghost c = \upgrade_claim({c}, table_claim_stable()))
  ctx->k_ab = get_shared_key(ctx->other, ctx->other_len, ctx->self, ctx->self_len, &(ctx->k_ab_len) _(ghost ctx->c));
  _(ghost ctx->\owns += (unsigned char[ctx->k_ab_len]) ctx->k_ab)
  _(assert \active_claim(c))
  _(assert Good_Server(*ctx))

  _(assert \mutable((unsigned char[m1_e_len_init]) m1_e))
  _(ghost c = \upgrade_claim({c}, table_claim_stable()))
  m1_len = decrypt_len(ctx->k_ab, ctx->k_ab_len, p, m1_e_len);
  m1 = malloc(m1_len);
  _(ghost m1_len_init = m1_len)
  if (m1 == NULL)
  {
    _(wrap(ctx))
    free(SPEC_CAST(unsigned char[m1_e_len_init],m1_e));
    return -1;
  }
  _(assert Good_Server(*ctx))
  m1_len = decrypt(ctx->k_ab, ctx->k_ab_len, p, m1_e_len, m1 _(ghost ctx->c));

  _(assert getTerm(m1_e,m1_e_len_init) == Pair(getTerm(ctx->other,ctx->other_len),SEnc(getTerm(ctx->k_ab,ctx->k_ab_len),getTerm(m1,m1_len))))
  _(assert Level(Low,getTerm(m1_e,m1_e_len_init)))
  
  if(m1_len < 1 + sizeof(ctx->request_len))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext has wrong length.\n");
#endif
    exit(1);
    _(assume \false)
  }

  ctx->request_len = parse_uint32(m1 + 1);

  // TODO: Remove these assumptions
  _(assume 1 + sizeof(ctx->request_len) + ctx->request_len <= ULONG_MAX)
  if(m1_len <= 1 + sizeof(ctx->request_len) + ctx->request_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext has wrong length (2).\n");
#endif
    exit(1);
    _(assume \false)
  }

  if(memcmp_s_u(_(precise)("p"), m1, 1))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext not properly tagged as a pair, aborting\n");
#endif
    exit(1);
    _(assume \false)
  }

  ctx->request = malloc(ctx->request_len);
  if (ctx->request == NULL)
  {
    _(wrap(ctx))
    free(SPEC_CAST(unsigned char[m1_e_len_init],m1_e));
    free(SPEC_CAST(unsigned char[m1_len_init],m1));
    return -1;
  }
  memcpy_u_u(ctx->request, m1 + 1 + sizeof(ctx->request_len), ctx->request_len);
  _(ghost ctx->\owns += (unsigned char[ctx->request_len]) ctx->request)
  _(wrap((unsigned char[ctx->request_len]) ctx->request))

  ctx->k_len = m1_len - (1 + sizeof(ctx->request_len) + ctx->request_len);
  ctx->k = malloc(ctx->k_len);
  if (ctx->k == NULL)
  {
    free(SPEC_CAST(unsigned char[m1_e_len_init],m1_e));
    free(SPEC_CAST(unsigned char[m1_len_init],m1));
    _(wrap(ctx))
    return -1;
  }
  memcpy_u_u(ctx->k, m1 + 1 + sizeof(ctx->request_len) + ctx->request_len, ctx->k_len);
  _(ghost ctx->\owns += (unsigned char[ctx->k_len]) ctx->k)
  _(wrap((unsigned char[ctx->k_len]) ctx->k))
  _(wrap(ctx))
    _(ghost _(atomic (&table)) {
      term req, seskey;
      term tpair = getTerm(m1,m1_len);
	  if (!table.DefinedB[from_array(ctx->request,ctx->request_len)] ||
	      !table.DefinedB[from_array(ctx->k,ctx->k_len)])
        collision = \true;
      else
      {
        req = getTerm(ctx->request,ctx->request_len);
        seskey = getTerm(ctx->k,ctx->k_len);
      }
	  if (tpair != Pair(req,seskey))
        collision = \true;
      })
  _(assume !collision)
  _(assert \active_claim(c))
  _(assert Good_Server(*ctx))

  _(assert log.Request[table.B2T[from_array(ctx->other,ctx->other_len)]][table.B2T[from_array(ctx->self,ctx->self_len)]][table.B2T[from_array(ctx->request,ctx->request_len)]])

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Authenticated request: ");
  print_text_buffer(ctx->request,ctx->request_len);
  printf("\nServer: Authenticated session key: ");
  print_buffer(ctx->k,ctx->k_len);
  fflush(stdout);
#endif
#endif

  free(SPEC_CAST(unsigned char[m1_e_len_init],m1_e));
  free(SPEC_CAST(unsigned char[m1_len_init],m1));
  return 0;
}

int send_response(RPCstate * ctx _(ghost \claim c))
  _(always c, table_valid())
  _(ensures table_stable())
  _(writes c)
  _(requires ctx->self != NULL && ctx->other != NULL && ctx->k_ab != NULL && ctx->k != NULL && ctx->request != NULL && ctx->response != NULL)
  _(updates ctx)
{
  unsigned char * m2_e;
  uint32_t m2_e_len;
  _(ghost uint32_t m2_e_len_init)

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Preparing response: ");
  print_text_buffer(ctx->response,ctx->response_len);
  printf("\n");
  fflush(stdout);
#endif
#endif

  _(unwrap(ctx))
  m2_e_len = encrypt_len(ctx->k, ctx->k_len, ctx->response, ctx->response_len);
  _(ghost m2_e_len_init = m2_e_len)

  m2_e = malloc(m2_e_len);
  if (m2_e == NULL)
  {
    _(wrap(ctx))
    return -1;
  }
  m2_e_len = encrypt(ctx->k, ctx->k_len, ctx->response, ctx->response_len, m2_e _(ghost c));

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Sending encrypted message: ");
  print_buffer(m2_e, m2_e_len);
  fflush(stdout);
#endif
#endif

  send_uint32(&(ctx->bio),  NOSPEC_CAST(unsigned char*,&m2_e_len), sizeof(m2_e_len));
  send(&(ctx->bio), m2_e, m2_e_len _(ghost c));

  _(wrap(ctx))
  free(SPEC_CAST(unsigned char[m2_e_len_init],m2_e));
  return 0;
}

int parseargs(int argc, char ** argv, RPCstate * ctx _(ghost uint32_t argl[\integer]))
  _(requires \wrapped(&table))
  _(requires \mutable_array(argv,(uint32_t) argc))
  _(requires \forall uint32_t i; 0 <= i && i < (uint32_t) argc ==> isMutableNTstring(argv[i],argl[i]))
  _(writes \extent(ctx))
  _(ensures \result == 0 ==> \wrapped(ctx))
  _(ensures \result == 0 ==> ctx->self != NULL)
{
  uint32_t port_len, pwr = 1;
  _(ghost uint32_t port_len_init;)
  _(ghost uint32_t l;)

  if (argc != 2 && argc != 3)
    return -1;

  // Initialize the whole structure to 0
  ctx->self = NULL;
  ctx->other = NULL;
  ctx->k = NULL;
  ctx->k_ab = NULL;
  ctx->request = NULL;
  ctx->response = NULL;
  ctx->port = 0;
  _(ghost ctx->\owns = {})

  // Get the principal name from the first command-line parameter
  ctx->self_len = strlen(argv[1] _(ghost argl[1]));
  if (ctx->self_len >= 256)
    return -1;
  if (ctx->self_len == 0)
  {
    ctx->self_len = DEFAULTHOST_LEN;
    ctx->self = malloc(ctx->self_len);
    if (ctx->self == NULL)
      return -1;

    memcpy_u_s(ctx->self,DEFAULTHOST,ctx->self_len); // VCC models string literals using unsigned char
  }
  else
  {
    ctx->self = malloc(ctx->self_len);
    if (ctx->self == NULL)
      return -1;

    memcpy_u_s(ctx->self,argv[1],ctx->self_len);
  }
  _(ghost ctx->\owns += (unsigned char[ctx->self_len]) ctx->self)
  _(wrap((unsigned char[ctx->self_len]) ctx->self))

#ifdef CSEC_VERIFY
  readenvE(ctx->self, &(ctx->self_len), sizeof(ctx->self_len), "serverID");
#endif

  ctx->port = 0;
  if (argc == 3)
  {
    port_len = strlen(argv[2] _(ghost argl[2]));
    if (port_len > 5)
      return -1;
    _(ghost port_len_init = port_len;)

    while (port_len > 0)
    _(invariant port_len >= 0 && port_len <= 5 && port_len <= strlen(argv[2] _(ghost argl[2])))
    _(invariant isNTstring(argv[2],(uint32_t) port_len_init))
    _(invariant pwr == pwr10(port_len_init - port_len))
    _(invariant ctx->port <= pwr10(port_len_init - port_len + 1))
    _(invariant \unchanged(ctx->\owns))
    _(invariant \unchanged(ctx->self) && \unchanged(ctx->self_len) && \unchanged(ctx->other) && \unchanged(ctx->k) && \unchanged(ctx->k_ab) && \unchanged(ctx->request) && \unchanged(ctx->response))
    {
	  if (argv[2][port_len - 1] < '0' || argv[2][port_len - 1] > '9')
        return -1;
      _(assert argv[2][port_len - 1] >= 48 && argv[2][port_len - 1] <= 57)
      ctx->port += (int) (((uint32_t) argv[2][port_len - 1] - 48) * pwr);
      pwr *= 10;
      port_len--;
    }
  }
  if (ctx->port <= 0 || ctx->port >= 65535)
  {
    ctx->port = DEFAULTPORT;
  }
  _(wrap(ctx))
  return 0;
}

int main(int argc, char ** argv _(ghost uint32_t argl[\integer]))
  _(requires \program_entry_point())
  _(requires argc >= 0)
  _(requires \mutable_array(argv,(uint32_t) argc))
  _(requires \forall uint32_t i; i < (uint32_t) argc ==> isMutableNTstring(argv[i],argl[i]))
{
  RPCstate seState;
  _(ghost \claim c)
  
  if (parseargs(argc,argv, &seState _(ghost argl)))
  {
#ifndef VERIFY
    fprintf(stdout, "Usage: server serverAddress [port]\n");
#endif
    exit(-1);
    _(assume \false)
  }

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Now listening on %s, port %d.\n", seState.self, seState.port);
#endif
#endif
  _(unwrapping(&seState)) {
  if (socket_listen(&(seState.bio),&(seState.bio), seState.self, seState.self_len, seState.port,NULL))
    return -1;
  }
#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Accepted client connection.\n");
#endif
#endif

  /* Receive request */
  if (recv_request(&seState) != 0)
  {
    _(unwrap &seState)
    return -1;
  }

  /* Send response */
  _(unwrapping &seState) {
  seState.response = get_response(&(seState.response_len));
  _(ghost (&seState)->\owns += (unsigned char[seState.response_len]) seState.response)}

#ifdef CSEC_VERIFY
  event4("server_reply", seState.other, seState.other_len, seState.self, seState.self_len,
                         seState.request, seState.request_len, seState.response, seState.response_len);
#endif

  if (send_response(&seState _(ghost c)) != 0)
  {
    _(unwrap &seState)
    return -1;
  }

  // wait for the client to close, to avoid "Address already in use" errors
  wait_close(&(seState.bio));

  _(unwrap &seState)
  return 0;
}
