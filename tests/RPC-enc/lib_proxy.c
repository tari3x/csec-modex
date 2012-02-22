// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <proxies/common.h>
#include <proxies/interface.h>
#include <proxies/system-proxies.h>

#include <string.h>

extern uint32_t encrypt_len_proxy(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
{
  uint32_t ret = encrypt_len(key, keylen, in, inlen);

  symL("encrypt_len", "len", sizeof(ret), FALSE);
  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern uint32_t encrypt_proxy(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * out)
{
  uint32_t ret = encrypt(key, keylen, in, inlen, out);

  load_buf(in, inlen, "msg");
  load_buf(key, keylen, "key");
  newTN("seed", "nonce", NULL);
  symNE("E", "cipher", &ret, sizeof(ret), TRUE, -1);
  store_buf(out);

  if(ret > encrypt_len_proxy(key, keylen, in, inlen))
    fail("encrypt_proxy: bad length");

  return ret;
}

extern uint32_t decrypt_len_proxy(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
{
  uint32_t ret = decrypt_len(key, keylen, in, inlen);

  symL("decrypt_len", "len", sizeof(ret), FALSE);
  store_buf(&ret);

  if(ret < 0) exit(1);

  return ret;
}

extern uint32_t decrypt_proxy(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * out)
{
  uint32_t ret = decrypt(key, keylen, in, inlen, out);

  load_buf(in, inlen, "cipher");
  load_buf(key, keylen, "key");
  symN("D", "msg", NULL, TRUE);
  symNE("inverse_injbot", "msg", &ret, sizeof(ret), TRUE, -1);
  store_buf(out);

  if(ret > decrypt_len_proxy(key, keylen, in, inlen))
    fail("decrypt_proxy: bad length");

  return ret;
}

unsigned char * get_shared_key_proxy(unsigned char* client, uint32_t client_len, unsigned char* server, uint32_t server_len, uint32_t * len)
{
  unsigned char * ret = get_shared_key(client, client_len, server, server_len, len);

  // We only provide the service for one identity of attacker's choice (xClient).
  // This can be improved with multipath, because then we can just inline the case split
  // bad client / good client.
  size_t xclient_len = client_len;
  unsigned char * xclient = malloc(xclient_len);
  memcpy(xclient, client, xclient_len);
  readenv(xclient, &xclient_len, "xClient");

  if((client_len != xclient_len) || memcmp_proxy(client, xclient, xclient_len))
    fail("trying to look up key for unknown host");

  load_buf(client, client_len, "client");
  load_buf(server, server_len, "server");
  varsym("db");
  symNE("lookup", "kAB", len, sizeof(*len), TRUE, -1);
  store_buf(ret);
  //readenv(ret, len, "kAB");

  return ret;
}

unsigned char * mk_session_key_proxy(uint32_t * len)
{
  unsigned char * ret = mk_session_key(len);

  newTN("keyseed", "kS_seed", NULL);
  symN("kgen", "kS", len, FALSE);
  store_buf(ret);

  return ret;
}

/*
unsigned char * get_request_proxy(uint32_t * len)
{
  unsigned char * ret = get_request(len);

  symNE("nonce", "request", len, sizeof(*len), FALSE);
  store_buf(ret);

  return ret;
}
*/

unsigned char * get_response_proxy(uint32_t * len)
{
  unsigned char * ret = get_response(len);

  // symNE("new", "response", len, sizeof(*len), FALSE, -1);
  // store_buf(ret);

  // newTN("mstring_payload", "response", len);
  // store_buf(ret);

  readenv(ret, len, "response");

  return ret;
}

