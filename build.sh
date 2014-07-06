#!/bin/bash

set -o errexit -o nounset -o pipefail

set -x

( 
  cd deps/cil-1.7.3/ 
  if [ ! -f Makefile.features ]; then
    ./configure EXTRAFEATURES="fundefs funreplace crestInstrument"
  fi
)

( cd deps/ocamlyices && ./configure --enable-custom && make )
( cd src/CIL && make )
( cd src/symtrace && make )
( 
  cd deps/cryptoverif1.12 
  if [ ! -f cryptoverif ]; then
    ./build 
  fi
)
cmake . && make
# forgetting to cmake . in proxies results in vile errors: cilly gets passed an incorrect --root 
# which breaks things in very confusing ways.
( cd proxies && cmake . && make )
markdown README.markdown > README.html
