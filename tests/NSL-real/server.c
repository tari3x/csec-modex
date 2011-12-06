// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// Modified by Marcin Szymczak
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "net.h"
#include "lib.h"

#ifdef CSEC_VERIFY
  #include <proxies/common.h>
#endif

#include <string.h>
#include <stdio.h>

#include <openssl/evp.h>
#include <openssl/rsa.h>

int main(int argc, char ** argv)
{
  EVP_PKEY * pkey, * skey, * xkey;
  unsigned char * pkey_char, * skey_char, * xkey_char, * temp;
  size_t pkey_len, skey_len, xkey_len;
  size_t pkey_char_len, skey_char_len, xkey_char_len;

  unsigned char * m1, * m1_e;
  unsigned char * xNa;
  size_t m1_len, m1_e_len;
  size_t m1_l;

  unsigned char * m2, * m2_e;
  unsigned char * Nb;
  size_t m2_len, m2_e_len;

  unsigned char * m3, * m3_e;
  size_t m3_len, m3_e_len;

  unsigned char * p;

  unsigned char * key = malloc(KEY_LENGTH);
  unsigned char * iv = malloc(KEY_LENGTH);

  // for dropping encryption tags
  unsigned char * dummy = malloc(4);

  BIO * bio = socket_listen();

  pkey = get_pkey(&pkey_len, 'B');
  skey = get_skey(&skey_len, 'B');
  //xkey = get_xkey(&xkey_len, 'B');

  pkey_char_len = i2d_PUBKEY(pkey, NULL);
  skey_char_len = i2d_PrivateKey(skey, NULL);
  //xkey_char_len = i2d_PUBKEY(xkey, NULL);

  pkey_char = (unsigned char*)malloc(pkey_char_len+1);
  skey_char = (unsigned char*)malloc(skey_char_len+1);
  //xkey_char = (unsigned char*)malloc(xkey_char_len+1);

  temp = pkey_char;
  i2d_PUBKEY(pkey, &temp);
  
  temp = skey_char;
  i2d_PrivateKey(skey, &temp);
  
  //temp = xkey_char;
  //i2d_PUBKEY(xkey, &temp);

  /* Receive message 1 */
  
  recv(bio, dummy, 4);
  recv(bio, (unsigned char*) &m1_e_len, sizeof(m1_e_len));

  m1_e = malloc(m1_e_len);
  
  recv(bio, m1_e, m1_e_len);

  m1_len = decrypt_len(skey, skey_len, m1_e, m1_e_len);

  m1 = malloc(m1_len);

  m1_len = decrypt(skey, skey_len, m1_e, m1_e_len, m1);
/*
  if(xkey_char_len + 2*sizeof(size_t) + SIZE_NONCE + 4 != m1_len)
  {
    fprintf(stderr, "m1 has wrong length\n");
    exit(1);
  }
*/
  if(memcmp(m1, "msg1", 4))
  {
    fprintf(stderr, "B: m1 not properly tagged, aborting\n");
    exit(1);
  }

  m1_l = * (size_t *) (m1 + 4);

  if(m1_l !=  SIZE_NONCE)
  {
    fprintf(stderr, "A: m1 contains wrong length for xNa\n");
    exit(1);
  }
/*
  if(memcmp(m1 + sizeof(size_t) + m1_l + 4, xkey_char,  xkey_char_len))
  {
    fprintf(stderr, "x_xkey in m1 doesn't match xkey\n");
    exit(1);
  }
*/
  
  xkey_char_len = * (size_t *) (m1 + sizeof(size_t) + m1_l + 4);

  unsigned char * q;
  q = m1 + 2*sizeof(size_t) + m1_l + 4;

  d2i_PUBKEY(&xkey, &q, xkey_char_len);

  xkey_len = 512; //whatever

  xNa = m1 + 4 + sizeof(size_t);

#ifdef VERBOSE
    fprintf(stderr, "B: m1 received and checked");
    fprintf(stderr, "\n");
    fflush(stderr);
#endif

  /* Send message 2 */

  m2_len = 2 * SIZE_NONCE + 2 * sizeof(size_t) + 4 + pkey_char_len;
  p = m2 = malloc(m2_len);

  memcpy(p, "msg2", 4);
  p += 4;
  * (size_t *) p = m1_l;
    
  p += sizeof(size_t);
  * (size_t *) p = 20;
  p += sizeof(size_t);
  memcpy(p, xNa, m1_l);
  p += m1_l;
  Nb = p;
  nonce(Nb);
  p += SIZE_NONCE;
  memcpy(p, pkey_char, pkey_char_len);

  get_key(key);
  get_iv(iv);

  m2_e_len = encrypt_len(xkey, xkey_len, m2, m2_len, key, iv);
  m2_e = malloc(m2_e_len + sizeof(size_t) + 4);
  memcpy(m2_e, "encr", 4);
  m2_e_len = encrypt(xkey, xkey_len, m2, m2_len, key, iv, m2_e + sizeof(m2_e_len) + 4);
  * (size_t *) (m2_e + 4) = m2_e_len;

  send(bio, m2_e, m2_e_len + sizeof(m2_e_len) + 4);

#ifdef VERBOSE
    fprintf(stderr, "B: m2 sent");
    fprintf(stderr, "\n");
    fflush(stderr);
#endif

  /* Receive message 3 */

  recv(bio, dummy, 4);
  recv(bio, (unsigned char*) &m3_e_len, sizeof(m3_e_len));
  m3_e = malloc(m3_e_len);
  recv(bio, m3_e, m3_e_len);

  m3_len = decrypt_len(skey, skey_len, m3_e, m3_e_len);
  m3 = malloc(m3_len);
  m3_len = decrypt(skey, skey_len, m3_e, m3_e_len, m3);

  if(m3_len != SIZE_NONCE)
  {
    fprintf(stderr, "B: m3 has wrong length\n");
    exit(1);
  }

  if(memcmp(m3, Nb, SIZE_NONCE))
  {
    fprintf(stderr, "xNb in m3 doesn't match Nb\n");
    exit(1);
  }

#ifdef VERBOSE
    printf("B: Na = ");
    print_buffer(xNa, SIZE_NONCE);
    printf("\n");
    printf("B: Nb = ");
    print_buffer(Nb, SIZE_NONCE);
    printf("\n");
    fflush(stdout);
#endif

#ifdef CSEC_VERIFY
  event0("endB");
#endif

  // wait for the client to close, to avoid "Address already in use" errors
  wait_close(bio);

  return 0;
}
 
