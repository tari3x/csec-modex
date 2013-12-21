
CSEC_ROOT = ../..

include $(CSEC_ROOT)/mk/common.mk

all: CIL leaves.exe calltrace.exe badpairs.exe unreachable.exe calledOpaque.exe

# nums seems to be necessary since 3.12
BUILD_CMD = ocamlc -g -o $@ unix.cma str.cma nums.cma -I $(CIL_OBJDIR) cil.cma $^

leaves.exe: common.ml leaves.ml 
	$(BUILD_CMD)

calltrace.exe: common.ml calltrace.ml 
	$(BUILD_CMD)

badpairs.exe: common.ml badpairs.ml 
	$(BUILD_CMD)

unreachable.exe: common.ml mark.ml unreachable.ml 
	$(BUILD_CMD)

calledOpaque.exe: common.ml mark.ml calledOpaque.ml 
	$(BUILD_CMD)

dumpBoring.exe: common.ml dumpBoring.ml 
	$(BUILD_CMD)

CIL:
	cd $(CIL_ROOT) && make

clean:
	$(RM) *.cmi *.cmo *.exe
