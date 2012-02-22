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

int send_request(RPCstate * ctx)
{
  uint32_t m1_len, m1_e_len, full_len;
  unsigned char * m1, * p, * m1_e;

#ifdef VERBOSE
  printf("Client: Preparing to send request: ");
  print_text_buffer(ctx->request,ctx->request_len);
  printf("\nand session key: ");
  print_buffer(ctx->k,ctx->k_len);
  fflush(stdout);
#endif

  m1_len = 1 + ctx->k_len + sizeof(ctx->request_len) + ctx->request_len;
  p = m1 = malloc(m1_len);
  if (m1 == NULL) return -1;

  memcpy(p, "p", 1);
  p += 1;
  *((uint32_t *) p) = ctx->request_len;
  p += sizeof(ctx->request_len);
  memcpy(p, ctx->request, ctx->request_len);
  p += ctx->request_len;
  memcpy(p, ctx->k, ctx->k_len);

  full_len = 1 + sizeof(ctx->self_len) + ctx->self_len + encrypt_len(ctx->k_ab, ctx->k_ab_len, m1, m1_len);
  p = m1_e = malloc(full_len);
  if (m1_e == NULL)
  {
    free(m1);
    return -1;
  }
  memcpy(p, "p", 1);
  p += 1;
  *((uint32_t *) p) = ctx->self_len;
  p += sizeof(ctx->self_len);
  memcpy(p, ctx->self, ctx->self_len);
  p += ctx->self_len;
  m1_e_len = encrypt(ctx->k_ab, ctx->k_ab_len, m1, m1_len, p);
  if (m1_e_len == 0)
  {
    free(m1);
    return -1;
  }
  full_len = 1 + sizeof(ctx->self_len) + ctx->self_len + m1_e_len;

#ifdef VERBOSE
  printf("Client: Sending message: %.1s | %u | ", m1_e, *((uint32_t*) (m1_e + 1)));
  print_text_buffer(m1_e + 1 + sizeof(uint32_t),ctx->self_len);
  printf(" | ");
  print_buffer(p,m1_e_len);
  fflush(stdout);
#endif

  send(&(ctx->bio), (unsigned char *) &full_len, sizeof(full_len));
  send(&(ctx->bio), m1_e, full_len);

  free(m1);
  free(m1_e);

  return 0;
}

int recv_response(RPCstate * ctx)
{
  unsigned char * m2_e;
  uint32_t m2_e_len;

  recv(&(ctx->bio), (unsigned char*) &m2_e_len, sizeof(m2_e_len));
  // Check if the read length is within bounds
  if (m2_e_len < MAX_MESSAGE_OVERHEAD || m2_e_len > MAX_PAYLOAD_LENGTH + MAX_MESSAGE_OVERHEAD)
    return -1;

  m2_e = malloc(m2_e_len);
  if (m2_e == NULL)
    return -1;
  recv(&(ctx->bio), m2_e, m2_e_len);

#ifdef VERBOSE
  printf("Client: Received encrypted message: ");
  print_buffer(m2_e,m2_e_len);
  fflush(stdout);
#endif

  ctx->response_len = decrypt_len(ctx->k, ctx->k_len, m2_e, m2_e_len);
  if (ctx->response_len > MAX_PAYLOAD_LENGTH)
  {
    free(m2_e);
    return -1;
  }

  ctx->response = malloc(ctx->response_len);
  if (ctx->response == NULL)
  {
    free(m2_e);
    return -1;
  }
  // this call returns 0 if not encrypted with the right key
  ctx->response_len = decrypt(ctx->k, ctx->k_len, m2_e, m2_e_len, ctx->response);
  if (ctx->response_len == 0)
  {
    free(m2_e);
    return -1;
  }

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

    memcpy((char*) ctx->self,argv[1],ctx->self_len);
  }

  ctx->other_len = strlen(argv[2]);
  if (ctx->other_len == 0)
  {
    ctx->other_len = DEFAULTHOST_LEN;
    ctx->other = malloc(ctx->other_len);
    if (ctx->other == NULL)
      return -1;

    memcpy(ctx->other,DEFAULTHOST,ctx->other_len);
  }
  else
  {
    ctx->other = malloc(ctx->other_len);
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
  // TOOD: replace by random for the purpose of secrecy
  readenvE(ctx->request, &(ctx->request_len), sizeof(ctx->request_len), "request");
#endif

  return 0;
}

//Begin ClientCode
int main(int argc, char ** argv)
{
  RPCstate clState;

  clState.end = CLIENT;

  if (parseargs(argc,argv,&clState))
  {
#ifdef VERBOSE
    fprintf(stdout, "Usage: client clientAddress serverAddress [port] request\n");
#endif
    exit(-1);
  }

#ifdef VERBOSE
  printf("Client: Now connecting to ");
  print_text_buffer(clState.other,clState.other_len);
  printf(", port %d.\n", clState.port);
  fflush(stdout);
#endif
  // Getting arguments
  if (socket_connect(&(clState.bio),(char*) clState.other, clState.other_len, clState.port))
    return -1;
  clState.k_ab = get_shared_key(clState.self, clState.self_len, clState.other, clState.other_len, &(clState.k_ab_len));
  clState.k = mk_session_key(&(clState.k_len));
  clState.response = NULL;

#ifdef CSEC_VERIFY
  event3("client_begin", clState.self, clState.self_len, clState.other, clState.other_len, clState.request, clState.request_len);
#endif

  /* Send request */
  if (send_request(&clState) < 0) return -1;

  /* Receive response */
  if (recv_response(&clState) < 0) return -1;

#ifdef CSEC_VERIFY
  event4("client_accept", clState.self, clState.self_len, clState.other, clState.other_len,
                          clState.request, clState.request_len, clState.response, clState.response_len);
#endif

  return 0;
}
//End ClientCode
