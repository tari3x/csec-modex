// Copyright (c) Mihhail Aizatulin (avatar@hot.ee), Francois Dupressoir (fdupress@gmail.com).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#ifdef VERIFY
#include <vcc.h>
#include <stdlib.h> // Contains definition for NULL, not used in compilation, but necessary for specification.

#include "table.h"
#else
#define _(...)
#endif

#define DEFAULTHOST      "localhost"
#define DEFAULTHOST_LEN  9
#define DEFAULTPORT      4433

#include <stdlib.h>
#include <stdint.h>
#include <polarssl/net.h>

int socket_listen(int *bind_fd, int *client_fd, const unsigned char *bind_ip, uint32_t bind_ip_len, int port, void *client_ip)
  _(requires \mutable_array(bind_ip,bind_ip_len) || \wrapped((unsigned char[bind_ip_len]) bind_ip))
  _(requires 0 <= port && port < 65535)
  /* Needs to write client_ip *iff* it is not NULL (and even then, it needs some kind of length for memory safety) */
  _(writes bind_fd, client_fd);

int socket_connect(int *fd, const char *host, uint32_t host_len, int port)
  _(requires \exists uint32_t host_len; \mutable_array(host,host_len) && host[host_len] == '\0')
  _(requires 0 <= port && port < 65535)
  _(writes fd);

void send(int *ch, unsigned char * msg, unsigned long len)
  _(ensures table_stable() && log_stable())
  _(requires \mutable_array(msg,len))
  _(requires Level(Low,table.B2T[from_array(msg,len)]));

int recv(int *ch, unsigned char * buf, unsigned long len)
  _(ensures table_stable())
  _(writes \array_range(buf,len))
  _(ensures \mutable_array(buf,len))
  _(ensures (\integer) \result <= (\integer) len)
  _(ensures Level(Low,getTerm(buf,len)) && table.DefinedB[from_array(buf,len)]);

void wait_close(int *c);
