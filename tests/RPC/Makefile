
CSEC_ROOT = ../..

# $(shell find -name "*.c" -not -name "*.cil.c")
SRC := $(filter-out $(wildcard *.cil.c), $(wildcard *.c))

P1 = RPC
P2 = RPC

P1_CMD = server
P2_CMD = client

P1_SRC = $(SRC)
P2_SRC = $(SRC)

# for simple make call
everything: iml verify
#everything: iml verify_full

# for eclipse
all: sym

include $(CSEC_ROOT)/mk/main.mk

clean::
	$(RM) RPC
