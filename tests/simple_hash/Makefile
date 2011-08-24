
CSEC_ROOT = ../..

P1 = server
P2 = client

P1_SRC = server.c net.c
P2_SRC = client.c net.c

#everything: orig sym
everything: iml verify

all: orig sym

include $(CSEC_ROOT)/mk/main.mk

# don't compile lib with CIL cause fail has varargs
CILLY_FLAGS += --leavealone=lib

clean::
	$(RM) client server
