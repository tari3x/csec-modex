
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.


// FIXME: remove as soon as we don't call crest functions directly
#include "crest.h"

#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include "interface.h"

#include "common_internal.h"

EXTERN int ( __attribute__((__cdecl__)) memcmp_proxy)(void const * a, void const * b, size_t len)
{
  int ret = memcmp(a, b, len);

  load_buf((const unsigned char*) a, len, "");
  load_buf((const unsigned char*) b, len, "");
  symL("cmp", "cmp", sizeof(ret), TRUE);

  CustomReturn();
  return ret;
}

EXTERN void *( __attribute__((__cdecl__)) memcpy_proxy)(void * dest, void const * src, size_t len)
{
  void * ret = dest;

  load_buf((const unsigned char*) src, len, "");

  mute();
  ret = memcpy(dest, src, len);
  unmute();

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

int strcmp_proxy(char const   *a , char const   *b )
{
  int ret = strcmp(a, b);

  load_all((const unsigned char*) a, "");
  __CrestApplyN("ztp", 1); // FIXME: allow sym to take number of params
  load_all((const unsigned char*) b, "");
  __CrestApplyN("ztp", 1);
  symL("cmp", "cmp", sizeof(ret), TRUE);

  CustomReturn();
  return ret;
}

extern int strncmp_proxy(char const *a, char const *b, size_t n)
{
  int ret = strncmp(a, b, n);

  load_buf((const unsigned char*) a, n, "");
  __CrestApplyN("ztp", 1); // FIXME: allow sym to take number of params
  load_buf((const unsigned char*) b, n, "");
  __CrestApplyN("ztp", 1);
  symL("cmp", "cmp", sizeof(ret), TRUE);

  CustomReturn();
  return ret;
}

extern void *malloc_proxy(size_t size)
{
  void * ret = NULL;

  ret = malloc(size);

  NewHeapPtr(size);

  CustomReturn();
  return ret;
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

  ret = realloc(ptr, size);

  NewHeapPtr(size);

  store_buf(&ret);
  load_all(ptr, "");
  store_buf(ret);

  return ret;
}


/*
 * The memset() function returns a pointer to the memory area s.
 */
extern void *memset_proxy(void *s , int c , size_t n )
{
  void * ret = memset(s, c, n);

  ret = s;

  load_int(c, "");
  symL("replicate", "replicate", n, TRUE);
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
  ssize_t ret = read(fd, buf, nbytes);

  if(ret != nbytes)
  {
    proxy_fail("read_proxy: ret != nbytes not handled yet");
  }

  ret = nbytes;

  symL("read", "msg", ret, FALSE);
  store_buf(buf);

  return ret;
}

extern ssize_t write_proxy(int fd , void const   *buf , size_t n )
{
  ssize_t ret = write(fd, buf, n);

  if(ret != n)
  {
    proxy_fail("write_proxy: ret != n not handled yet");
  }

  ret = n;

  load_buf(buf, ret, "msg");
  symN("write", "write", NULL, FALSE);
  event();

  return ret;
}

/*
 * The strcpy() and strncpy() functions return a pointer to the destination string dest.
 */
extern  char *strcpy_proxy(char * dest , char const * src )
{
  void * ret = strcpy(dest, src);

  ret = dest;

  load_all((const unsigned char*) src, "");
  symN("ztp", "ztp", NULL, TRUE);
  store_all((const unsigned char*) dest);

  return ret;
}
