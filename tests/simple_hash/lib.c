
#include "lib.h"

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>

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
