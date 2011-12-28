// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <gcm.h>
#include <polarssl/havege.h>

#include <string.h>
#include <stdio.h>
#include <stdarg.h>

/*
  These functions are now calling out to zork.org's implementation of GCM mode for AES.
  http://www.zork.org/gcm
*/

// Not thread-safe
static havege_state HS;
static int HSinitted = 0;

extern uint32_t encrypt_len(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
{
  return 32 + inlen;
}

extern uint32_t encrypt(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * out)
{
  gcm_ctx_256b ctx;
  int i;

  if (!HSinitted)
  {
    havege_init(&HS);
    HSinitted++;
  }

  for (i = 0; i < 4; i++)
  {
    ((int*) (out + inlen + 16))[i] = havege_rand(&HS);
  }

  gcm_init_256b(&ctx,key,keylen * 8);
  gcm_encrypt_256b(&ctx, out + inlen + 16,16,in,inlen,NULL,0,out,out + inlen);
  gcm_destroy_256b(&ctx);

  return 32 + inlen;
}

extern uint32_t decrypt_len(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen)
{
  return inlen - 32;
}

void fail(const char * fmt, ...)
{
  va_list argp;
  va_start(argp, fmt);
  vfprintf(stderr, fmt, argp);
  va_end(argp);
  fprintf(stderr, "\n");

  // if(c != NULL) wait_close(c);

  exit(1);
}

extern uint32_t decrypt(unsigned char * key, uint32_t keylen, unsigned char * in, uint32_t inlen, unsigned char * out)
{
  gcm_ctx_256b ctx;

  gcm_init_256b(&ctx,key,keylen * 8);
  if (gcm_decrypt_256b(&ctx,in + inlen - 16,16,in,inlen - 32,in + inlen - 32,16,NULL,0,out) == 0)
    fail("Decryption/Authentication check failed.\n");
  gcm_destroy_256b(&ctx);

  return inlen - 32;
}

// FIXME: implement this properly
unsigned char * get_shared_key(unsigned char* client, uint32_t client_len, unsigned char* server, uint32_t server_len, uint32_t * len)
{
  *len = 16;
  return (unsigned char *) "abcdefghijklmnop";
}

unsigned char * mk_session_key(uint32_t * len)
{
  // We will generate it completely at random,
  // which may not be the best idea (see weak keys
  // for GCM mode).
  int i;
  unsigned char * key;

  if (!HSinitted)
  {
    havege_init(&HS);
    HSinitted++;
  }

  key = malloc(4 * sizeof(int));
  if (key == NULL)
    return NULL;

  for (i = 0; i < 4; i++)
  {
    ((int*) key)[i] = havege_rand(&HS);
  }

  *len = 4 * sizeof(uint32_t);
  return key;
}

unsigned char * get_response(uint32_t * len)
{
  *len = 20;
  return (unsigned char*) "Look out the window.";
}


void print_buffer(const unsigned char * buf, int len)
{
  uint32_t sblen;
  char * sbuf;
  int i;

  if(!buf)
  {
    printf("NULL");
    return;
  }

  sblen = len * 2 + 1;
  sbuf = (char *) malloc(sblen);

  for(i = 0; i < len; i++)
    sprintf(sbuf + 2 * i, "%02x", buf[i]);
    /* if(isprint(buf[i]))
      putchar(buf[i]);
    else
      printf("\\%.2x", buf[i]); */

  // hm, all of this is still interleaving!
  // write(2, sbuf, sblen);
  // write(2, "\n", 1);
  printf("%s\n",  sbuf);
  // fflush(stdout);
  // FD: You may want to free all this eventually
}

void print_text_buffer(const unsigned char * buf, int len)
{
  int i;
  char * sbuf;

  if(!buf)
  {
    printf("NULL");
    return;
  }

  sbuf = (char *) malloc(len + 1);

  for(i = 0; i < len; i ++)
    sprintf(sbuf + i,"%c", buf[i]);
  sbuf[len] = '\0';

  printf("%s", sbuf);
  return;
}
