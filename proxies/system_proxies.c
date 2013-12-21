
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.


// FIXME: remove as soon as we don't call crest functions directly
#include "crest.h"

#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>

#include <netdb.h>

#include "interface.h"

#include "common_internal.h"

EXTERN int ( __attribute__((__cdecl__)) memcmp_proxy)(void const * a, void const * b, size_t len)
{
  mute();
  int ret = memcmp(a, b, len);
  unmute();

  load_buf((const unsigned char*) a, len, "");
  load_buf((const unsigned char*) b, len, "");

  SymN("cmp", 2);
  assume_intype("bitstring");
  assume_len(sizeof(ret));
  StoreBuf(&ret);

  return ret;
}

EXTERN void *( __attribute__((__cdecl__)) memcpy_proxy)(void * dest, void const * src, size_t len)
{
  void * ret = dest;

  mute();
  ret = memcpy(dest, src, len);
  unmute();

  load_buf((const unsigned char*) src, len, "");
  store_buf((const unsigned char*) dest);

  return ret;
}

EXTERN void *( __attribute__((__cdecl__)) memmove_proxy)(void * dest, void const * src, size_t len)
{
  void * ret = dest;

  load_buf((const unsigned char*) src, len, "");

  mute();
  ret = memmove(dest, src, len);
  unmute();

  store_buf((const unsigned char*) dest);

  return ret;
}


extern void *malloc_proxy(size_t size)
{
  mute();
  void * ret = malloc(size);
  unmute();

  NewHeapPtr(size);
  store_buf(&ret);

  return ret;
}

extern void *__builtin_alloca_proxy(unsigned long  size)
{
  // NB calling malloc instead, because alloc automatically frees when the caller exits
  return malloc_proxy(size);
}


/*
 * realloc() changes the size of the memory block pointed to by ptr to size bytes.
 * The contents will be unchanged to the minimum of the old and new sizes; newly allocated memory will be uninitialized.
 * If  ptr is NULL, then the call is equivalent to malloc(size), for all values of size; if size is equal to zero,
 * and ptr is not NULL, then the call is equivalent to free(ptr).  Unless ptr is NULL, it must have been returned
 * by an earlier call to malloc(), calloc() or realloc().  If the area pointed to was moved, a free(ptr) is done.
 */
extern  void *realloc_proxy(void *ptr , size_t size )
{
  void * ret = NULL;

  mute();
  ret = realloc(ptr, size);
  unmute();

  NewHeapPtr(size);

  store_buf((unsigned char *) &ret);
  load_all(ptr, "");
  store_buf(ret);

  return ret;
}


/*
 * The memset() function returns a pointer to the memory area s.
 */
extern void *memset_proxy(void *s , int c , size_t n )
{
  mute();
  void * ret = memset(s, c, n);
  unmute();

  ret = s;

  load_int(c, FALSE, sizeof(char), "");

  // FIXME: this is wrong, n should go on stack
  SymN("replicate", 1);
  assume_len(n);

  store_buf(s);

  return ret;
}

/*
   read() attempts to read up to count bytes from file descriptor fd into the buffer starting at buf.

   If count is zero, read() returns zero and has no other results.
   If count is greater than SSIZE_MAX, the result is unspecified.

   On  success, the number of bytes read is returned (zero indicates end of file), and the file position
   is advanced by this number.  It is not an error if this number is smaller than the number of
   bytes requested; this may happen for example because fewer bytes are actually available right now
   (maybe because we were close to end-of-file, or because we are reading from a pipe,  or  from  a
   terminal),  or  because  read()  was  interrupted  by a signal.  On error, -1 is returned, and errno
   is set appropriately.  In this case it is left unspecified whether the file position (if any) changes.
 */
extern ssize_t read_proxy(int fd , void *buf , size_t nbytes )
{
  mute();
  ssize_t ret = read(fd, buf, nbytes);
  unmute();

  if(ret != nbytes)
  {
    proxy_fail("read_proxy: ret != nbytes not handled yet");
  }

  ret = nbytes;

  input("msg", ret);
  store_buf(buf);

  return ret;
}

extern ssize_t write_proxy(int fd , void const   *buf , size_t n )
{
  mute();
  ssize_t ret = write(fd, buf, n);
  unmute();

  if(ret != n)
  {
    proxy_fail("write_proxy: ret != n not handled yet");
  }

  ret = n;

  load_buf(buf, ret, "msg");
  output();

  return ret;
}

int strcmp_proxy(char const   *a , char const  *b )
{
  mute();
  int ret = strcmp(a, b);
  unmute();

  load_all((const unsigned char*) a, "");
  SymN("ztp", 1);
  load_all((const unsigned char*) b, "");
  SymN("ztp", 1);
  // No hint, we expect cmp to be rewritten
  SymN("cmp", 2);
  assume_len(sizeof(ret));
  store_buf(&ret);

  return ret;
}

int strncmp_proxy(char const *a, char const *b, size_t n)
{
  mute();
  int ret = strncmp(a, b, n);
  unmute();

  load_buf((const unsigned char*) a, n, "");
  SymN("ztp", 1);
  load_buf((const unsigned char*) b, n, "");
  SymN("ztp", 1);
  SymN("cmp", 2);
  assume_len(sizeof(ret));
  store_buf(&ret);

  return ret;
}


/*
 * The strcpy() and strncpy() functions return a pointer to the destination string dest.
 */
char *strcpy_proxy(char * dest , char const * src )
{
  mute();
  void * ret = strcpy(dest, src);
  unmute();

  ret = dest;

  load_all((const unsigned char*) src, "");
  SymN("ztp", 1);
  duplicate();
  test_intype("bitstring");
  load_int(0, FALSE, sizeof(char), "");
  Append();
  store_all((const unsigned char*) dest);

  return ret;
}

size_t strlen_proxy(const char *s)
{
  mute();
  size_t ret = strlen(s);
  unmute();

  load_all((const unsigned char*) s, "");
  SymN("ztp", 1);
  // Expect to be simplified to ztpSafe when possible.
  Done();
  test_intype("bitstring");
  len(sizeof(ret));
  store_buf((const unsigned char*) &ret);

  return ret;
}

/*
    struct hostent
    {
      char *h_name;                 // Official name of host.
      char **h_aliases;             // Alias list.
      int h_addrtype;               // Host address type.
      int h_length;                 // Length of address.
      char **h_addr_list;           // List of addresses from name server.
    #if defined __USE_MISC || defined __USE_GNU
    # define        h_addr  h_addr_list[0] // Address, for backward compatibility.
    #endif
    };
*/
struct hostent *gethostbyname_proxy(const char *name)
{
  mute();
  struct hostent * ret = gethostbyname(name);
  unmute();

  char * varname = (char *) malloc(strlen(name) + strlen("host_address_") + 1);
  sprintf(varname, "host_address_%s", name);

  fresh_ptr(sizeof(char*));
  StoreBuf(&ret->h_addr_list);
  varWithBufInit(varname, (unsigned char *) &ret->h_addr, (unsigned char *) &ret->h_length, sizeof(ret->h_length));

  return ret;
}


void __assert_fail_proxy(char const   *__assertion ,
                         char const   *__file ,
                         unsigned int __line ,
                         char const   *__function )
{
  mute();
  __assert_fail(__assertion, __file, __line, __function);
  unmute();
}
