// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#define OPENSSL_MAJOR 1

#if OPENSSL_MAJOR == 0
  #include "openssl_proxies-0.9.8o.h"
#else
  #include "openssl_proxies-1.0.0.h"
#endif
