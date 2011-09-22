
CSEC_ROOT = ../..

P1 = bob
P2 = alice

P1_SRC = primitives_crypt.c common.c lib.c bob.c
P2_SRC = primitives_crypt.c common.c lib.c alice.c

OUTPUTS = iml.all.out

#everything: orig sym
everything: iml.all.out

all: orig sym

test: primitives_crypt.c common.c test.c
test: LDLIBS += $(PROXIES)/libssl_proxy_bin.a

include $(CSEC_ROOT)/mk/main.mk

clean::
	$(RM) alice bob
