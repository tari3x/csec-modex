
CSEC_ROOT = ../..

include $(CSEC_ROOT)/mk/common.mk

all: CIL leaves calltrace badpairs unreachable calledOpaque

# nums seems to be necessary since 3.12
BUILD_CMD = ocamlc -g -o $@ unix.cma str.cma nums.cma -I $(CIL_OBJDIR) cil.cma $^

leaves: common.ml leaves.ml 
	$(BUILD_CMD)

calltrace: common.ml calltrace.ml 
	$(BUILD_CMD)

badpairs: common.ml badpairs.ml 
	$(BUILD_CMD)

unreachable: common.ml mark.ml unreachable.ml 
	$(BUILD_CMD)

calledOpaque: common.ml mark.ml calledOpaque.ml 
	$(BUILD_CMD)

dumpBoring: common.ml dumpBoring.ml 
	$(BUILD_CMD)

CIL:
	cd $(CIL_ROOT) && make

clean:
	$(RM) *.cmi *.cmo leaves calltrace badpairs dumpBoring unreachable calledOpaque



