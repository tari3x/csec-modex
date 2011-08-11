// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include <net.h>
#include <lib.h>

#include <proxies/common.h>

#include <string.h>
#include <stdio.h>

// #define LOWE_ATTACK

int main(int argc, char ** argv)
{
  unsigned char * pkey, * skey, * xkey;
  size_t pkey_len, skey_len, xkey_len;

  unsigned char * m1, * m1_all;
  unsigned char * Na;
  size_t m1_len, m1_e_len, m1_all_len;

  unsigned char * m2, * m2_e;
  unsigned char * xNb;
  size_t m2_len, m2_e_len;
  size_t m2_l1, m2_l2;

  unsigned char * m3_e;
  size_t m3_e_len;

  unsigned char * p;

  // for encryption tags
  unsigned char * etag = malloc(4);

  BIO * bio = socket_connect();

  pkey = get_pkey(&pkey_len, 'A');
  skey = get_skey(&skey_len, 'A');
  xkey = get_xkey(&xkey_len, 'A');

#ifdef VERBOSE
  printf("pkey = ");
  print_buffer(pkey, pkey_len);
  printf("\n");

  printf("skey = ");
  print_buffer(skey, skey_len);
  printf("\n");

  printf("xkey = ");
  print_buffer(xkey, xkey_len);
  printf("\n");
#endif

  /* Send message 1 */

  m1_len = SIZE_NONCE + 4 + pkey_len
      + sizeof(size_t);
  p = m1 = malloc(m1_len);

  memcpy(p, "msg1", 4);
  p += 4;
  * (size_t *) p = SIZE_NONCE;
  p += sizeof(size_t);
  Na = p;
  nonce(Na);
  p += SIZE_NONCE;
  memcpy(p, pkey, pkey_len);

  m1_e_len = encrypt_len(xkey, xkey_len,
                         m1, m1_len);
  m1_all_len = m1_e_len + sizeof(size_t) + 4;
  m1_all = malloc(m1_all_len);
  memcpy(m1_all, "encr", 4);
  m1_e_len =
      encrypt(xkey, xkey_len, m1,
              m1_len,
              m1_all + sizeof(m1_e_len) + 4);
  m1_all_len = m1_e_len + sizeof(size_t) + 4;
  * (size_t *) (m1_all + 4) = m1_e_len;

  send(bio, m1_all, m1_all_len);

#ifdef VERBOSE
    printf("A: m1_e sent, m1_e = ");
    print_buffer(m1_all, m1_all_len);
    printf("\n");
    fflush(stdout);
#endif

  /* Receive message 2 */

  recv(bio, etag, 4);
  recv(bio, (unsigned char*) &m2_e_len,
       sizeof(m2_e_len));
  m2_e = malloc(m2_e_len);
  recv(bio, m2_e, m2_e_len);

  m2_len = decrypt_len(skey, skey_len,
                       m2_e, m2_e_len);
  m2 = malloc(m2_len);
  m2_len =
      decrypt(skey, skey_len,
              m2_e, m2_e_len, m2);

  if(xkey_len + 2 * SIZE_NONCE
      + 2 * sizeof(size_t) + 4 != m2_len)
  {
    printf("A: m2 has wrong length\n");
    exit(1);
  }

  if(memcmp(m2, "msg2", 4))
  {
    printf("A: m2 not properly tagged\n");
    exit(1);
  }

  m2_l1 = *(size_t *) (m2 + 4);
  m2_l2 = *(size_t *) (m2 + 4 + sizeof(size_t));

  if(m2_l1 != SIZE_NONCE)
  {
    printf("A: m2 has wrong length for xNa\n");
    exit(1);
  }

  if(m2_l2 != SIZE_NONCE)
  {
    printf("A: m2 has wrong length for xNb\n");
    exit(1);
  }

  if(memcmp(m2 + 4 + 2 * sizeof(size_t),
            Na, m2_l1))
  {
    printf("A: xNa in m2 doesn't match Na\n");
    exit(1);
  }

#ifndef LOWE_ATTACK
  if(memcmp(m2 + m2_l1 + m2_l2
            + 2 * sizeof(size_t) + 4,
            xkey,  xkey_len))
  {
    printf("A: x_xkey in m2 doesn't match xkey\n");
    exit(1);
  }
#endif

  xNb = m2 + m2_l1 + 2 * sizeof(size_t) + 4;

#ifdef VERBOSE
    printf("A: m2 received and checked");
    printf("\n");
    fflush(stdout);
#endif

  /* Send message 3 */

  m3_e_len = encrypt_len(xkey, xkey_len,
                         xNb, m2_l2);
  m3_e = malloc(m3_e_len + sizeof(size_t) + 4);
  memcpy(m3_e, "encr", 4);
  m3_e_len =
      encrypt(xkey, xkey_len, xNb,
              m2_l2, m3_e + sizeof(m3_e_len) + 4);
  * (size_t *)(m3_e + 4) = m3_e_len;

  send(bio, m3_e, m3_e_len + sizeof(m3_e_len) + 4);

#ifdef VERBOSE
    printf("A: m3 sent");
    printf("\n");
    fflush(stdout);
#endif

#ifdef VERBOSE
    printf("A: Na = ");
    print_buffer(Na, SIZE_NONCE);
    printf("\n");
    printf("A: Nb = ");
    print_buffer(xNb, SIZE_NONCE);
    printf("\n");
    fflush(stdout);
#endif

  return 0;
}
