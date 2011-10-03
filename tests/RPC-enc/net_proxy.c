 
#include "lib.h"

#include <polarssl/net.h>

#include <proxies/common.h>
#include <proxies/interface.h>

int net_recv_proxy( void *ctx, unsigned char *buf, int len )
{
  int ret = net_recv(ctx, buf, len);

  if(ret != len)
  {
    fail("read_proxy: ret != len not handled yet");
  }

  ret = len;

  symL("read", "msg", ret, FALSE);
  store_buf(buf);

  return ret;
}

int net_send_proxy( void *ctx, unsigned char *buf, int len )
{
  int ret = net_send(ctx, buf, len);

  if(ret != len)
  {
    fail("write_proxy: ret != len not handled yet");
  }

  ret = len;

  load_buf(buf, ret, "msg");
  symN("write", "write", NULL, FALSE);
  event();

  return ret;
}
