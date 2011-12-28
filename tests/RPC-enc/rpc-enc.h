// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <limits.h>
#include <stdint.h>



#define MAX_MESSAGE_OVERHEAD 38 // This is AUTH_LENGTH + IV_LENGTH + LENGTH_LENGTH + 2
#define MAX_PAYLOAD_LENGTH 1024
#define MAX_PRINCIPAL_LENGTH 1024

enum protEnd {CLIENT, SERVER};

typedef struct RPCstate_s
{
  enum protEnd end;
  int port;


  unsigned char * self;
  uint32_t self_len;

  unsigned char * other;
  uint32_t other_len;

  // Long-Term Key
  unsigned char * k_ab;
  uint32_t k_ab_len;

  // Request
  unsigned char * request;
  uint32_t request_len;
  
  // Session Key
  unsigned char * k;
  uint32_t k_len;

  // Response
  unsigned char * response;
  uint32_t response_len;

  // Channel/Socket
  int bio;
} RPCstate;