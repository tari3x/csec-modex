
include $(CSEC_ROOT)/mk/common.mk

#CPP_SRC = $(wildcard *.cpp)
#C_SRC = $(wildcard *.c)

SYM_OBJ = openssl_proxies_sym.o system_proxies.o symbolic_interface.o common_sym.o

#OBJ = $(CPP_SRC:.cpp=.o) $(C_SRC:.c=.o)

CXXFLAGS = -g2 -Wall -Wno-attributes -Wno-unknown-pragmas -Wno-unused-label
CFLAGS   = -g2 -Wall -Wno-attributes -Wno-unknown-pragmas -Wno-unused-label

PROXY_CONF_SYM = openssl_proxies.sym.conf
CILLY = $(PROXY_SYM_CILLY)

BUILD = $(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

all: libssl_proxy_sym.a
# libssl_proxy_bin.a 

libssl_proxy_bin.a: openssl_proxies_bin.o binary_interface.o common_bin.o common_cpp.o
libssl_proxy_sym.a: $(SYM_OBJ) crestify.o common_cpp.o

libssl_proxy_bin.a libssl_proxy_sym.a:
	$(AR) $(ARFLAGS) $@ $^

$(SYM_OBJ): CC = $(CILLY)
$(SYM_OBJ): $(CIL_EXEC)

openssl_proxies%.o: openssl_proxies.c
	$(BUILD)

common_bin.o common_sym.o: common.c
	$(BUILD)

proxy_defs: proxies.out.cil.c

proxies.out:
	touch $@

# proxies.bin.out 
proxies.out.cil.c: $(OPENSSL_ROOT)/proxies.sym.out proxies.out
	echo "#include <openssl/evp.h>" > proxies.out.c
	echo "#include <openssl/ssl.h>" >> proxies.out.c
	echo "#include <openssl/x509.h>" >> proxies.out.c
	cat $^ >> proxies.out.c
	cilly -c --save-temps --dofundefs --keepunused proxies.out.c
	rm proxies.out.cil.i proxies.out.i proxies.out.o proxies.out.c
  
clean:
	$(RM) *.o *.a *.cil.c *.i *.out

.PHONY: clean all
