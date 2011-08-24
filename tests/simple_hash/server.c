// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <openssl/hmac.h>

#include <net.h>

#include <proxies/common.h>

#include <string.h>

#include "lib.h"

#define SHA1_LEN 20

void server(unsigned char * key, ulong key_len)
{
  ulong payload_len;

  BIO * b = socket_listen();

  // receive the payload length and compute message length
  recv(b, (unsigned char*) &payload_len, sizeof(payload_len));
  if(payload_len < 0) fail ("payload_len < 0");

  ulong body_len = sizeof(payload_len) + 1 + payload_len;
  ulong msg_len = body_len + SHA1_LEN;

  // allocate the message and the hash buffers
  unsigned char * buf = malloc(msg_len);
  unsigned char * hmac = malloc(SHA1_LEN);

  // store payload length in the received message buffer
  unsigned char * p = buf;
  * (ulong *) p = payload_len;
  p += sizeof(payload_len);

  // receive the tag, the payload and the hash into message buffer
  //recv(b, p, 1 + payload_len + SHA1_LEN);
  recv(b, p, 1);
  unsigned char * tag = p;
  *(p++) = 1; // overwrite the tag

  recv(b, p, payload_len);
  //unsigned char * payload = p + 1;
  //unsigned char * msg_hmac = p + 1 + payload_len;

  unsigned char * payload = p;
  p += payload_len;

  recv(b, p, SHA1_LEN);

  unsigned char * msg_hmac = p;
  p += SHA1_LEN;

  unsigned int md_len;
  *tag = 2;
  HMAC(EVP_sha1(), key, key_len, buf, body_len, hmac, &md_len);
  *tag = 1;

  if(!memcmp(hmac, msg_hmac, SHA1_LEN))
  {
    #ifdef VERBOSE
        printf("received and verified ");
        fwrite(payload, payload_len, sizeof(char), stdout);
        printf("\n");
        fflush(stdout);
    #endif
    #ifdef CSEC_VERIFY
      event1("server_recv", payload, payload_len);
    #endif
  }
  else
  {
#ifdef VERBOSE
    printf("verification failed\n");
#endif
  }

  // wait for the client to close, to avoid "Address already in use" errors
  wait_close(b);
}

int main(int argc, char ** argv)
{
  char * key = "Secret key";
  ulong key_len = 11;

#ifdef CSEC_VERIFY
  readenv(key, &key_len, "key");
  //make_sym(&key_len, sizeof(key_len), "user_len");
  //make_sym(key, key_len, "key");
#endif

  server( (unsigned char*) key, key_len);

  return 0;
}
 
