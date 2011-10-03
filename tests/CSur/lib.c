
#include "lib.h"

#include <stdio.h>

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
