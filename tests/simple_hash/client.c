// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <openssl/hmac.h>

#include <net.h>

#include <proxies/common.h>

#include <string.h>
#include <stdio.h>

#define SHA1_LEN 20

void client(unsigned char * payload, ulong payload_len, unsigned char * key, ulong key_len)
{
  ulong body_len = sizeof(payload_len) + 1 + payload_len;
  ulong msg_len = body_len + SHA1_LEN;
  unsigned char * msg = malloc(msg_len);

  unsigned char * p = msg;
  * (ulong *)p = payload_len; p += sizeof(payload_len);     // add length
  unsigned char * tag = p;
  *(p++) = 1;                                               // add the tag
  memcpy(p, payload, payload_len);                          // add the payload

  p += payload_len;

  unsigned int md_len;
  *tag = 2;
  HMAC(EVP_sha1(), key, key_len, msg, body_len, p, &md_len); // add hash
  *tag = 1;

  BIO * b = socket_connect();
  send(b, msg, msg_len);
}

int main(int argc, char ** argv)
{
  char * msg = "Hello world";
  ulong msg_len = 12;
  char * key = "Secret key";
  ulong key_len = 11;

#ifdef CSEC_VERIFY
  readenv(msg, &msg_len, "payload");
  readenv(key, &key_len, "key");
//  make_sym(&msg_len, sizeof(msg_len), "user_len");
//  make_sym(msg, msg_len, "payload");
//  make_sym(&key_len, sizeof(key_len), "user_len");
//  make_sym(key, key_len, "key");
  event1("client_send", msg, msg_len);
#endif

  client((unsigned char*) msg, msg_len, (unsigned char *) key, key_len);

  return 0;
}
