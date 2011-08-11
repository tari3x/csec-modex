
include $(CSEC_ROOT)/mk/common.mk

all: CIL leaves calltrace badpairs

# nums seems to be necessary since 3.12
BUILD_CMD = ocamlc -g -o $@ unix.cma str.cma nums.cma -I $(CIL_ROOT)/$(CIL_OBJDIR) cil.cma $^

leaves: leaves.ml common.ml
	$(BUILD_CMD)

calltrace: calltrace.ml common.ml
	$(BUILD_CMD)

badpairs: badpairs.ml common.ml
	$(BUILD_CMD)

dumpBoring: common.ml dumpBoring.ml 
	$(BUILD_CMD)

CIL:
	cd $(CIL_ROOT) && make

clean:
	$(RM) *.cmi *.cmo
