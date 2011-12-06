// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// Modified by Marcin Szymczak
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "lib.h"

#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>

#include <openssl/rand.h>
#include <openssl/pem.h>

/*
  These functions are now stubs, real ones will be using something along the lines of

  #include <openssl/evp.h>
  EVP_PKEY_CTX *EVP_PKEY_CTX_new(EVP_PKEY *pkey, ENGINE *e);
  EVP_PKEY *EVP_PKEY_new(void);
  int EVP_PKEY_set1_RSA(EVP_PKEY *pkey,RSA *key);

  For now it doesn't really matter what's in here because the verification doesn't look into these functions.
*/

extern void nonce(unsigned char * N)
{
  memcpy(N, "nonce", 5);
  RAND_bytes(N + 5, SIZE_NONCE - 5);
}

extern void get_key(unsigned char * ptr)
{
  memcpy(ptr, "key", 3);
  RAND_bytes(ptr + 3, KEY_LENGTH - 3);
}

extern void get_iv(unsigned char * ptr)
{
  memcpy(ptr, "iv", 2);
  RAND_bytes(ptr + 2, KEY_LENGTH - 2);
}


extern size_t encrypt_len(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * symkey, unsigned char * iv)
{
  
  
  ENGINE *e;
  EVP_PKEY_CTX *ctx;
  size_t enc_key_len = 0;
  size_t msg_len = 0;
  size_t rem_len = 0;
  size_t outlen = 0;

  size_t symkey_len = KEY_LENGTH;
  size_t iv_len = KEY_LENGTH;

  e = ENGINE_get_default_RSA();
  ctx = EVP_PKEY_CTX_new(key, e);
  
  unsigned char * dummy = OPENSSL_malloc(inlen + AES_BLOCK_SIZE - 1);

  size_t keyiv_len;
  keyiv_len = sizeof(size_t) + symkey_len + iv_len;
  unsigned char * keyiv;
  keyiv = OPENSSL_malloc(keyiv_len);
  

  * (size_t *) keyiv = symkey_len;

  memcpy(keyiv + sizeof(size_t), symkey, symkey_len);
  memcpy(keyiv + sizeof(size_t) + symkey_len, iv, iv_len);

  //ENCRYPT KEY

  if(!ctx)
    printf("Null contrext\n");

  if(EVP_PKEY_encrypt_init(ctx) <= 0)
    printf("Context initialization failed\n");

  if(EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING) <= 0)
    printf("Couldn't set padding\n");


  //get encrypted sym key length
  if(EVP_PKEY_encrypt(ctx, NULL, &enc_key_len, keyiv, keyiv_len)<=0)
    printf("Couldn't determine length\n");

  

  //ENCRYPT MESSAGE ITSELF

  EVP_CIPHER_CTX sym_ctx;
  EVP_CIPHER_CTX_init(&sym_ctx);
  
  //AES
  EVP_EncryptInit_ex(&sym_ctx, EVP_aes_128_cbc() , NULL, symkey, iv);
  //ecncrypt
  if(!EVP_EncryptUpdate(&sym_ctx, dummy, &msg_len, in, inlen))
    printf("Symmetric encryption error\n");

  if(!EVP_EncryptFinal_ex(&sym_ctx, dummy+msg_len, &rem_len))
    printf("Symmetric encryption error- remainder\n");

  msg_len += rem_len;
  outlen = sizeof(size_t) + enc_key_len + msg_len;

  EVP_CIPHER_CTX_cleanup(&sym_ctx);

  OPENSSL_free(dummy);
  OPENSSL_free(keyiv);

  return outlen;
}

extern size_t encrypt(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * symkey, unsigned char * iv, unsigned char * out)
{
  
  ENGINE *e;
  EVP_PKEY_CTX *ctx;
  size_t enc_key_len;
  size_t msg_len;
  size_t rem_len;
  size_t outlen;

  size_t symkey_len = KEY_LENGTH;
  size_t iv_len = KEY_LENGTH;

  e = ENGINE_get_default_RSA();
  ctx = EVP_PKEY_CTX_new(key, e);

  size_t keyiv_len;
  keyiv_len = sizeof(size_t) + symkey_len + iv_len;
  unsigned char * keyiv;
  keyiv = OPENSSL_malloc(keyiv_len);
  

  * (size_t *) keyiv = symkey_len;

  memcpy(keyiv + sizeof(size_t), symkey, symkey_len);
  memcpy(keyiv + sizeof(size_t) + symkey_len, iv, iv_len);

  //ENCRYPT KEY

  if(!ctx)
    printf("Null contrext\n");

  if(EVP_PKEY_encrypt_init(ctx) <= 0)
    printf("Context initialization failed\n");

  if(EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING) <= 0)
    printf("Couldn't set padding\n");


  //get encrypted sym key length
  if(EVP_PKEY_encrypt(ctx, NULL, &enc_key_len, keyiv, keyiv_len)<=0)
    printf("Couldn't determine length\n");


  * (size_t *) out = enc_key_len;
  

  if(EVP_PKEY_encrypt(ctx, out + sizeof(size_t), &enc_key_len, keyiv, keyiv_len)<=0)
    printf("Encryption failed\n");

  //ENCRYPT MESSAGE ITSELF

  EVP_CIPHER_CTX sym_ctx;
  EVP_CIPHER_CTX_init(&sym_ctx);

  //AES
  EVP_EncryptInit_ex(&sym_ctx, EVP_aes_128_cbc() , NULL, symkey, iv);

  //ecncrypt
  if(!EVP_EncryptUpdate(&sym_ctx, out + sizeof(size_t) + enc_key_len, &msg_len, in, inlen))
    printf("Symmetric encryption error\n");
  
  if(!EVP_EncryptFinal_ex(&sym_ctx, out + sizeof(size_t) + enc_key_len + msg_len, &rem_len))
    printf("Symmetric encryption error- remainder\n");
  
  msg_len += rem_len;
  outlen = sizeof(size_t) + enc_key_len + msg_len;

  EVP_CIPHER_CTX_cleanup(&sym_ctx);
  OPENSSL_free(keyiv);  


  return outlen;
}

extern size_t decrypt_len(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen)
{

  ENGINE *e;

  e = ENGINE_get_default_RSA();


  size_t enc_key_len = 0;
  enc_key_len = * (size_t *) in;

  //decrypt the key and IV

  EVP_PKEY_CTX *ctx;
  size_t msg_len;
  size_t rem_len;
  size_t outlen;
  size_t keyiv_len;
  size_t iv_len;

  unsigned char * dummy = OPENSSL_malloc(inlen + AES_BLOCK_SIZE - 1);

  unsigned char * symkey;
  unsigned char * iv;
  unsigned char * keyiv;

  size_t symkey_len;
  

  ctx = EVP_PKEY_CTX_new(key,e);

  if(!ctx)
    printf("Null contrext\n");

  if(EVP_PKEY_decrypt_init(ctx) <= 0)
    printf("Context initialization failed\n");

  if(EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING) <= 0)
    printf("Couldn't set padding\n");

  //length of key + iv
  if(EVP_PKEY_decrypt(ctx, NULL, &keyiv_len, in + sizeof(size_t), enc_key_len)<=0)
    printf("Couldn't determine length\n");

  keyiv = OPENSSL_malloc(keyiv_len);

  if(!keyiv)
    printf("malloc failure\n");

  if(EVP_PKEY_decrypt(ctx, keyiv, &keyiv_len, in + sizeof(size_t), enc_key_len)<=0)
    printf("Decryption failed (len)\n");

  symkey_len = * (size_t *) keyiv;
  symkey = OPENSSL_malloc(symkey_len);
  memcpy(symkey, keyiv + sizeof(size_t), symkey_len);

  iv_len = keyiv_len - symkey_len - sizeof(size_t);
  iv = OPENSSL_malloc(iv_len);
  memcpy(iv, keyiv + sizeof(size_t) + symkey_len, iv_len);
 
  //decrypt message using symkey

  EVP_CIPHER_CTX sym_ctx;
  EVP_CIPHER_CTX_init(&sym_ctx);
  
  //AES
  EVP_DecryptInit_ex(&sym_ctx, EVP_aes_128_cbc() , NULL, symkey, iv);

  //decrypt
  if(!EVP_DecryptUpdate(&sym_ctx, dummy, &msg_len, in + sizeof(size_t) + enc_key_len, inlen - (sizeof(size_t) + enc_key_len) ))
    printf("Symmetric decryption (len) error\n");

  if(!EVP_DecryptFinal_ex(&sym_ctx, dummy + msg_len, &rem_len))
    printf("Symmetric decryption (len) error- remainder\n");

  msg_len += rem_len;
  outlen = msg_len;

  EVP_CIPHER_CTX_cleanup(&sym_ctx);

  OPENSSL_free(dummy);
  OPENSSL_free(keyiv);

  return outlen;
}

extern size_t decrypt(EVP_PKEY * key, size_t keylen, unsigned char * in, size_t inlen, unsigned char * out)
{

  ENGINE *e;

  e = ENGINE_get_default_RSA();

  //get the symkey

  size_t enc_key_len = 0;
  enc_key_len = * (size_t *) in;

  //decrypt the key

  EVP_PKEY_CTX *ctx;
  size_t msg_len;
  size_t rem_len;
  size_t outlen;
  size_t keyiv_len;
  size_t iv_len;


  unsigned char * symkey;
  unsigned char * iv;
  unsigned char * keyiv;

  size_t symkey_len;
  

  ctx = EVP_PKEY_CTX_new(key,e);

  if(!ctx)
    printf("Null contrext\n");

  if(EVP_PKEY_decrypt_init(ctx) <= 0)
    printf("Context initialization failed\n");

  if(EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING) <= 0)
    printf("Couldn't set padding\n");

  //length of key + IV
  if(EVP_PKEY_decrypt(ctx, NULL, &keyiv_len, in + sizeof(size_t), enc_key_len)<=0)
    printf("Couldn't determine length\n");

  keyiv = OPENSSL_malloc(keyiv_len);


  if(!keyiv)
    printf("malloc failure\n");

  if(EVP_PKEY_decrypt(ctx, keyiv, &keyiv_len, in + sizeof(size_t), enc_key_len)<=0)
    printf("Decryption failed\n");

  symkey_len = * (size_t *) keyiv;
  symkey = OPENSSL_malloc(symkey_len);
  memcpy(symkey, keyiv + sizeof(size_t), symkey_len);

  iv_len = keyiv_len - symkey_len - sizeof(size_t);
  iv = OPENSSL_malloc(iv_len);
  memcpy(iv, keyiv + sizeof(size_t) + symkey_len, iv_len);


  //message
  EVP_CIPHER_CTX sym_ctx;
  EVP_CIPHER_CTX_init(&sym_ctx);

  //AES
  EVP_DecryptInit_ex(&sym_ctx, EVP_aes_128_cbc() , NULL, symkey, iv);

  //decrypt
  if(!EVP_DecryptUpdate(&sym_ctx, out, &msg_len, in + sizeof(size_t) + enc_key_len, inlen - (sizeof(size_t) + enc_key_len) ))
    printf("Symmetric decryption error\n");

  if(!EVP_DecryptFinal_ex(&sym_ctx, out + msg_len, &rem_len))
    printf("Symmetric decryption error- remainder\n");

  msg_len += rem_len;
  outlen = msg_len;

  EVP_CIPHER_CTX_cleanup(&sym_ctx);


  OPENSSL_free(keyiv);
  

  return outlen;
}

EVP_PKEY * get_pkey(size_t * len, char side)
{
  FILE *keyfile;
  EVP_PKEY *pkey = NULL;

  *len = 512;


  if(side == 'A')
  {
    keyfile = fopen("./keys/pkeyA.pem", "r");
    pkey = PEM_read_PUBKEY(keyfile, NULL, 0, "whatever");
  }

  if(side == 'B')
  {
    keyfile = fopen("./keys/pkeyB.pem", "r");
    pkey = PEM_read_PUBKEY(keyfile, NULL, 0, "whatever");
  }

  fclose (keyfile);

  return pkey;
}

EVP_PKEY * get_skey(size_t * len, char side)
{
  FILE *keyfile;
  EVP_PKEY *skey = NULL;

  *len = 2048;

  if(side == 'A')
  {
    keyfile = fopen("./keys/skeyA.pem", "r");
    skey = PEM_read_PrivateKey(keyfile, NULL, 0, "whatever");
  }

  if(side == 'B')
  {
    keyfile = fopen("./keys/skeyB.pem", "r");
    skey = PEM_read_PrivateKey(keyfile, NULL, 0, "whatever");
  }

  fclose (keyfile);

  return skey;
}

EVP_PKEY * get_xkey(size_t * len, char side)
{
  FILE *keyfile;
  EVP_PKEY *xkey = NULL;

  *len = 512;


  if(side == 'A')
  {
    keyfile = fopen("./keys/pkeyB.pem", "r");
    xkey = PEM_read_PUBKEY(keyfile, NULL, 0, "whatever");
  }

  if(side == 'B')
  {
    keyfile = fopen("./keys/pkeyA.pem", "r");
    xkey = PEM_read_PUBKEY(keyfile, NULL, 0, "whatever");
  }

  fclose (keyfile);

  return xkey;
}

void fail(const char * fmt, ...)
{
  va_list argp;
  va_start(argp, fmt);
  vfprintf(stderr, fmt, argp);
  va_end(argp);
  printf("\n");

  // if(c != NULL) wait_close(c);

  exit(1);
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

