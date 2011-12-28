// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <openssl/hmac.h>

#include "net.h"

#include <string.h>

#include "lib.h"

#ifdef CSEC_VERIFY
  #include <proxies/common.h>
#endif

#define SHA1_LEN 20

void server(unsigned char * key, ulong key_len)
{
  ulong msg_len;

  BIO * b = socket_listen();

  // receive the message length
  recv(b, (unsigned char*) &msg_len, sizeof(msg_len));
  if(msg_len < 0) fail ("payload_len < 0");

  // allocate the message and the hash buffers
  unsigned char * buf = malloc(msg_len);
  unsigned char * hmac = malloc(SHA1_LEN);

  unsigned char * p = buf;

  // receive the message
  recv(b, buf, msg_len);

  // extract the payload length
  ulong payload_len = * (ulong *) p;
  p += sizeof(payload_len);

  // check the payload length
  if(sizeof(payload_len) + 1 + payload_len + SHA1_LEN != msg_len)
    fail("payload_len wrong");

  // check the tag
  if (*p != 1)
    fail("tag check failed");

  unsigned char * payload = p + 1;
  unsigned char * msg_hmac = p + 1 + payload_len;

  // reconstruct the hashed buffer
  ulong body_len = sizeof(payload_len) + 1 + payload_len;
  unsigned char * body = malloc(body_len);
  *(ulong *) body = payload_len;
  *(body + sizeof(payload_len)) = 2;
  memcpy(body + sizeof(payload_len) + 1, payload, payload_len);

  unsigned int md_len;
  HMAC(EVP_sha1(), key, key_len, body, body_len, hmac, &md_len);

  if(!memcmp(hmac, msg_hmac, SHA1_LEN))
  // if(1)
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
    fail("MAC check failed");

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
 
