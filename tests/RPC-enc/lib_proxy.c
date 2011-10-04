// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <proxies/common.h>
#include <proxies/interface.h>

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

  load_buf(key, keylen, "key");
  load_buf(in, inlen, "msg");
  symNE("E", "cipher", &ret, sizeof(ret), TRUE);
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

  load_buf(key, keylen, "key");
  load_buf(in, inlen, "cipher");
  symNE("D", "msg", &ret, sizeof(ret), TRUE);
  store_buf(out);

  if(ret > decrypt_len_proxy(key, keylen, in, inlen))
    fail("decrypt_proxy: bad length");

  return ret;
}

unsigned char * get_shared_key_proxy(unsigned char* client, uint32_t client_len, unsigned char* server, uint32_t server_len, uint32_t * len)
{
  unsigned char * ret = get_shared_key(client, client_len, server, server_len, len);

  load_buf(client, client_len, "client");
  load_buf(server, server_len, "server");
  symNE("key", "kAB", len, sizeof(*len), TRUE);
  store_buf(ret);
  //readenv(ret, len, "kAB");

  return ret;
}

unsigned char * mk_session_key_proxy(uint32_t * len)
{
  unsigned char * ret = mk_session_key(len);

  // typically one would use a keygen function seeded with a nonce,
  // but in a symbolic model this does not make a difference
  // and so we use the nonce itself as a key

  symNE("nonce", "kS", len, sizeof(*len), FALSE);
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

  symNE("nonce", "response", len, sizeof(*len), FALSE);
  store_buf(ret);

  return ret;
}

