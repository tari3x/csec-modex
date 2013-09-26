
# vpath %.a $(PROXIES)
# vpath %.a $(OPENSSL)

include $(CSEC_ROOT)/mk/common.mk

# Switch to absolute path
CSEC_ROOT = $(CSEC_ROOT_ABS)

SSL_LIB = $(OPENSSL)/libssl.a
#BIN_SSL_LIB = $(OPENSSL)/libssl_bin.a
CRYPTO_LIB = $(OPENSSL)/libcrypto.a
#BIN_CRYPTO_LIB = $(OPENSSL)/libcrypto_bin.a
BIN_PROXY_LIB += $(PROXIES)/libssl_proxy_bin.a
SYM_PROXY_LIB += $(PROXIES)/libssl_proxy_sym.a
CRESTIFY_LIB = $(PROXIES)/libcrestify.a

ifdef USE_CRESTIFIED_OPENSSL
	SYM_SSL_LIB = $(OPENSSL_CRESTIFIED)/libssl_sym.a
	SYM_CRYPTO_LIB = $(OPENSSL_CRESTIFIED)/libcrypto_sym.a
else
	SYM_SSL_LIB = $(SSL_LIB)
	SYM_CRYPTO_LIB = $(CRYPTO_LIB)
endif


#CPATH += $(PROXIES) $(OPENSSL)/include
#CFLAGS += -I$(OPENSSL)/include

ifndef PROXY_LIBS
  PROXY_LIBS = $(CRESTIFY_LIB)
endif 

ifndef COMPILATION_ROOT
  COMPILATION_ROOT = $(PWD)
endif

CSEC_CONF_OUT = $(COMPILATION_ROOT)/csec.conf.out

PROXY_OUT = $(COMPILATION_ROOT)/proxies.out

CILLY_FLAGS = --dofunreplace --csec-config=$(CSEC_CONF_OUT) --funreplaceoutput=$(PROXY_OUT) --root=$(COMPILATION_ROOT) --doCrestInstrument --save-temps --commPrintLn

# We want to keep these separate for cmake because it checks for existence of CC.
# At the same time openssl compilation breaks if you overwrite CFLAGS, so there I pass CC="$(CC) $(CFLAGS)".
CC = $(CILLY)
CFLAGS += -g2 -Wall -Wno-attributes -Wno-unknown-pragmas -Wno-unused-label -I$(OPENSSL)/include -I$(CSEC_ROOT)/include $(CILLY_FLAGS) -DCSEC_VERIFY

# need to use filename instead of -lcrypto because the linker tends to pick up the system version
# LDLIBS += $(BASE_LIB) $(PROXY_LIB) $(BASE_LIB) $(EXTRA_DEPS)
LDLIBS := $(PROXY_OBJ) $(PROXY_LIBS) $(LDLIBS) -lstdc++

############################
## Compile with CIL
############################

# FIXME: you want to remove duplicates but preserve order
ifndef PROGS
  PROGS = ${sort $(P1) $(P2) $(P3) }
endif

compile: $(PROGS)

ifndef CSEC_CONF
  # CSEC_CONF = $(PROXIES)/openssl_proxies.sym.conf
  CSEC_CONF = $(COMPILATION_ROOT)/csec.conf
endif

PROXY_CONF = $(PROXY_LIBS:.a=.conf)

$(CSEC_CONF_OUT): $(CSEC_CONF) $(PROXY_CONF)
	cat $^ > $@

ifndef BUILD_CMD
   $(error "must define BUILD_CMD")
endif

$(PROXY_OBJ): $(CSEC_CONF_OUT) $(CIL_LIB) $(PROXY_LIBS)

$(PROGS): $(CSEC_CONF_OUT) $(CIL_LIB) $(PROXY_LIBS) $(PROXY_OBJ) $(BUILD_DEPS)
	$(BUILD_CMD)


############################
## CVM
############################

# This requires that the client and the server are separate files
CVM = ${foreach P,$(PROGS),$(P).cvm.out}

# ${foreach P,$(ORIG),$(P).cvm.out}

cvm: $(CVM)

# FIXME: generalise
$(CVM): $(PROGS) $(RUN_DEPS)
	if [ -e "$(P1)" ]; then          CVM_OUTPUT=$(P1).cvm.out ./$(P1) $(P1_CMD); fi & \
	if [ -e "$(P2)" ]; then sleep 1; CVM_OUTPUT=$(P2).cvm.out ./$(P2) $(P2_CMD); fi & \
	wait

############################
## IML
############################

ifndef IML_OUTPUTS 
  IML_OUTPUTS = iml.out
endif

copy: iml.debug.copy.out

iml.debug.copy.out: iml.debug.out
	cp $^ $@

mark:
	grep "(mark)" iml.debug.out > mark.out

iml: iml.out

ifdef DEBUG_IML
iml.out iml.raw.out: $(CVM) $(IMLTRACE)
	{ $(IMLTRACE) $(CVM) iml.raw.out | tee iml.out; } 2>&1 | tee iml.debug.out
else
iml.out iml.raw.out: $(CVM) $(IMLTRACE)
	{ $(IMLTRACE) $(CVM) iml.raw.out | tee iml.out; } > iml.debug.out 2>&1
endif



############################
## ProVerif
############################

ifndef PV_OUTPUTS 
  PV_INPUTS = $(shell find . -name "*.pv.in")
  PV_OUTPUTS = $(PV_INPUTS:.in=.out)
endif

pv: $(PV_OUTPUTS)
	for f in $(PV_OUTPUTS); do\
		$(PROVERIF) -in pi $$f | grep "RESULT\|queries";\
	done


pv_full: $(PV_OUTPUTS)
	for f in $(PV_OUTPUTS); do\
		$(PROVERIF) -in pi $$f;\
	done


%.pv.out: iml.raw.out %.pv.in $(PITRACE)
	{ $(PITRACE) iml.raw.out $*.pv.in | tee $@; } > $*.pv.debug.out 2>&1


############################
## CryptoVerif
############################

ifndef CV_OUTPUTS 
  CV_INPUTS = $(shell find . -name "*.cv.in")
  CV_OUTPUTS = $(CV_INPUTS:.in=.out)
endif

cv: $(CV_OUTPUTS)
	for f in $(CV_OUTPUTS); do\
		$(CRYPTOVERIF) -lib $(CV_DEFAULT) $$f | grep "RESULT\|queries";\
	done

cv_full: $(CV_OUTPUTS)
	for f in $(CV_OUTPUTS); do\
		$(CRYPTOVERIF) -lib $(CV_DEFAULT) $$f;\
	done

%.cv.out: iml.raw.out $(CV_DEFAULT).cvl %.cv.in $(CVTRACE)
	{ $(CVTRACE) iml.raw.out $(CV_DEFAULT) $*.cv.in | tee $@; } > $*.cv.debug.out 2>&1

#cvmodel.out: iml.raw.out $(CV_DEFAULT).cvl cvtemplate.in $(CVTRACE)
#	{ $(CVTRACE) iml.raw.out $(CV_DEFAULT) cvtemplate.in | tee $@; } > cvmodel.debug.out 2>&1

############################
## Testing
############################

ifndef OUTPUTS
  OUTPUTS = $(IML_OUTPUTS) $(PV_OUTPUTS) $(CV_OUTPUTS)
endif
GOOD_OUTPUTS = $(OUTPUTS:.out=.good.txt)

check: $(GOOD_OUTPUTS)

%.good.txt: %.out
	@if diff $@ $<; then\
		echo "$<: Test OK.";\
	else\
		echo "$<: Test not OK.";\
#		exit 1;\
	fi
#    touch $@;\

bless: $(OUTPUTS)
	rename out good.txt $^


############################
## Callgraph info
############################

ifdef USE_CRESTIFIED_OPENSSL
OPENSSL_CALLGRAPH = $(OPENSSL_CRESTIFIED)/openssl.callgraph.out
OPENSSL_GLOBS = $(OPENSSL_CRESTIFIED)/openssl.globs.out
endif

ifndef LOCAL_CALLGRAPH
LOCAL_CALLGRAPH = $(shell find . -name "*.callgraph.out")
# the problem with this is that cryptokix doesn't rely on sym to build itself
#$(LOCAL_CALLGRAPH): sym
endif

ifndef LOCAL_GLOBS
LOCAL_GLOBS = $(shell find . -name "*.globs.out")
#$(LOCAL_GLOBS): sym
endif

# PROXY_CALLGRAPH = $(shell find $(PROXIES) -name "*.callgraph.out")
# PROXY_GLOBS = $(shell find $(PROXIES) -name "*.globs.out")

LIB_CALLGRAPH = $(PROXY_LIBS:.a=.callgraph.out)
LIB_GLOBS = $(PROXY_LIBS:.a=.globs.out)

filegraph: sym
	cat *.callgraph.out $(PROXIES)/openssl.fullgraph.out | sort -u > fullgraph.out
	mkdir -p defs
	cp *.defs.out defs
	cp -r $(PROXIES)/defs .
	time reachable fullgraph.out | clusterise defs | tee filegraph.out
	cat filegraph.out | sort -u | graph2dot > filegraph.dot
	time dot -Tpdf filegraph.dot > filegraph.pdf

# $(PROXY_CALLGRAPH) $(OPENSSL_CALLGRAPH)
callgraph.out: $(LOCAL_CALLGRAPH) $(LIB_CALLGRAPH)
	cat $^ > callgraph.out

# $(PROXY_GLOBS) $(OPENSSL_GLOBS)
globs.out: $(LOCAL_GLOBS) $(LIB_GLOBS)
	cat $^ > globs.out

# The list of called functions produced by symbolic execution.
called.out: iml

funlist: funlist_compile funlist_run

# This one depends on compilation only.
# We want this to work even if funlist_run fails, so that we can tell the user to instrument main().
# Make sure to call leaves first, as it gives better diagnostics.
funlist_compile: callgraph.out globs.out
	@echo "==== Reachable functions not proxied, opaque or crestified:"
	@$(CSEC_ROOT)/src/CIL/leaves
	@echo "==== Bad pairs:"
	@$(CSEC_ROOT)/src/CIL/badpairs
	@echo "==== Unreachable boring functions:"
	@$(CSEC_ROOT)/src/CIL/unreachable $(CSEC_CONF)
	@#echo "==== Instrumented boring functions:"
	@#comm -12 boring.out crestified.out
	@#echo "==== Unreachable boring functions:"
	@#comm -23 boring.out leaves.out

# This one depends on running the program.
funlist_run: called.out
	@echo "==== Called boring functions:"
	@$(CSEC_ROOT)/src/CIL/calledOpaque $(CSEC_CONF) "called.out"

############################
## Misc
############################


clean::
	$(RM) *.exe *.o *.cil.c *.i *.out

phony:

.PHONY: phony

