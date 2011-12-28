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

#include <string.h>

int recv_request(RPCstate * ctx)
{
  unsigned char * m1_e, * m1, * p;
  uint32_t m1_e_len, m1_len;

  recv(&(ctx->bio), (unsigned char*) &m1_e_len, sizeof(m1_e_len));
  if (m1_e_len < MAX_MESSAGE_OVERHEAD || m1_e_len > MAX_PAYLOAD_LENGTH + MAX_MESSAGE_OVERHEAD)
  {
    return -1;
  }
  
  p = m1_e = malloc(m1_e_len);
  if (m1_e == NULL)
  {
    return -1;
  }
  recv(&(ctx->bio), m1_e, m1_e_len);

  if (memcmp("p", p, 1))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message not properly tagged as a pair, aborting.\n");
#endif
    exit(-1);
  }
  p += 1;

  ctx->other_len = *((uint32_t *) p);
  if (ctx->other_len > MAX_PRINCIPAL_LENGTH)
    return -1;
  if (m1_e_len <= 1 + sizeof(uint32_t) + ctx->other_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message has wrong length.\n");
#endif
    exit(-1);
  }
  p += sizeof(uint32_t);

  ctx->other = malloc(ctx->other_len);
  if (ctx->other == NULL)
    return -1;
  memcpy(ctx->other,p,ctx->other_len);
  p += ctx->other_len;
  
  if (m1_e_len < 1 + sizeof(uint32_t) + ctx->other_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Message has wrong length.\n");
#endif
    exit(-1);
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

  ctx->k_ab = get_shared_key(ctx->other, ctx->other_len, ctx->self, ctx->self_len, &(ctx->k_ab_len));

  m1_len = decrypt_len(ctx->k_ab, ctx->k_ab_len, p, m1_e_len);
  if (m1_len > MAX_PAYLOAD_LENGTH)
    return -1;
  m1 = malloc(m1_len);
  if (m1 == NULL)
  {
    free(m1_e);
    return -1;
  }
  m1_len = decrypt(ctx->k_ab, ctx->k_ab_len, p, m1_e_len, m1);
  
  if(m1_len < 1 + sizeof(ctx->request_len))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext has wrong length.\n");
#endif
    exit(1);
  }

  ctx->request_len = *((uint32_t *) (m1 + 1));

  if(m1_len <= 1 + sizeof(ctx->request_len) + ctx->request_len)
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext has wrong length.\n");
#endif
    exit(1);
  }

  if(memcmp("p", m1, 1))
  {
#ifndef VERIFY
    fprintf(stderr, "Server: Plaintext not properly tagged as a pair, aborting\n");
#endif
    exit(1);
  }

  ctx->request = malloc(ctx->request_len);
  if (ctx->request == NULL)
  {
    free(m1_e);
    free(m1);
    return -1;
  }
  memcpy(ctx->request, m1 + 1 + sizeof(ctx->request_len), ctx->request_len);

  ctx->k_len = m1_len - (1 + sizeof(ctx->request_len) + ctx->request_len);
  ctx->k = malloc(ctx->k_len);
  if (ctx->k == NULL)
  {
    free(m1_e);
    free(m1);
    return -1;
  }
  memcpy(ctx->k, m1 + 1 + sizeof(ctx->request_len) + ctx->request_len, ctx->k_len);

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Authenticated request: ");
  print_text_buffer(ctx->request,ctx->request_len);
  printf("\nServer: Authenticated session key: ");
  print_buffer(ctx->k,ctx->k_len);
  fflush(stdout);
#endif
#endif

  free(m1_e);
  free(m1);
  return 0;
}

int send_response(RPCstate * ctx)
{
  unsigned char * m2_e;
  uint32_t m2_e_len;

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Preparing response: ");
  print_text_buffer(ctx->response,ctx->response_len);
  printf("\n");
  fflush(stdout);
#endif
#endif

  m2_e_len = encrypt_len(ctx->k, ctx->k_len, ctx->response, ctx->response_len);

  m2_e = malloc(m2_e_len);
  if (m2_e == NULL)
  {
    return -1;
  }
  m2_e_len = encrypt(ctx->k, ctx->k_len, ctx->response, ctx->response_len, m2_e);
  if (m2_e_len == 0)
  {
    return -1;
  }

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Sending encrypted message: ");
  print_buffer(m2_e, m2_e_len);
  fflush(stdout);
#endif
#endif

  send(&(ctx->bio), (unsigned char*) &m2_e_len, sizeof(m2_e_len));
  send(&(ctx->bio), m2_e, m2_e_len);

  free(m2_e);
  return 0;
}

int parseargs(int argc, char ** argv, RPCstate * ctx)
{
  uint32_t port_len, pwr = 1;

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

  // Get the principal name from the first command-line parameter
  ctx->self_len = strlen(argv[1] );
  if (ctx->self_len >= 256)
    return -1;
  if (ctx->self_len == 0)
  {
    ctx->self_len = DEFAULTHOST_LEN;
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

    memcpy(ctx->self,argv[1],ctx->self_len);
  }

#ifdef CSEC_VERIFY
  readenvE(ctx->self, &(ctx->self_len), sizeof(ctx->self_len), "serverID");
#endif

  ctx->port = 0;
  if (argc == 3)
  {
    port_len = strlen(argv[2]);
    if (port_len > 5)
      return -1;

    while (port_len > 0)
    {
	  if (argv[2][port_len - 1] < '0' || argv[2][port_len - 1] > '9')
        return -1;
      ctx->port += (int) (((uint32_t) argv[2][port_len - 1] - 48) * pwr);
      pwr *= 10;
      port_len--;
    }
  }
  if (ctx->port <= 0 || ctx->port >= 65535)
  {
    ctx->port = DEFAULTPORT;
  }
  return 0;
}

int main(int argc, char ** argv)
{
  RPCstate seState;
  if (parseargs(argc,argv, &seState))
  {
#ifndef VERIFY
    fprintf(stdout, "Usage: server serverAddress [port]\n");
#endif
    exit(-1);
  }

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Now listening on ");
  print_text_buffer(seState.self, seState.self_len);
  printf(", port %d.\n", seState.port);
#endif
#endif

  if (socket_listen(&(seState.bio),&(seState.bio), seState.self, seState.self_len, seState.port,NULL))
    return -1;

#ifdef VERBOSE
#ifndef VERIFY
  printf("Server: Accepted client connection.\n");
#endif
#endif

  /* Receive request */
  if (recv_request(&seState) != 0)
  {
    return -1;
  }

  /* Send response */
  seState.response = get_response(&(seState.response_len));

#ifdef CSEC_VERIFY
  event4("server_reply", seState.other, seState.other_len, seState.self, seState.self_len,
                         seState.request, seState.request_len, seState.response, seState.response_len);
#endif

  if (send_response(&seState) != 0)
  {
    return -1;
  }

  // wait for the client to close, to avoid "Address already in use" errors
  wait_close(&(seState.bio));

  return 0;
}
