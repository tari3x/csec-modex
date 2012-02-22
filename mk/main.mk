
# vpath %.a $(PROXIES)
# vpath %.a $(OPENSSL)

include $(CSEC_ROOT)/mk/common.mk

#CPATH += $(PROXIES) $(OPENSSL)/include
#CFLAGS += -I$(OPENSSL)/include

CFLAGS += -g2 -Wall -Wno-attributes -Wno-unknown-pragmas -Wno-unused-label -I$(OPENSSL)/include -I$(CSEC_ROOT)/include

# need to use filename instead of -lcrypto because the linker tends to pick up the system version
LDLIBS += $(BASE_LIB) $(PROXY_LIB) $(BASE_LIB) $(EXTRA_DEPS)
LDLIBS += -lstdc++

SSL_LIB = $(OPENSSL)/libssl.a
#BIN_SSL_LIB = $(OPENSSL)/libssl_bin.a
CRYPTO_LIB = $(OPENSSL)/libcrypto.a
#BIN_CRYPTO_LIB = $(OPENSSL)/libcrypto_bin.a
BIN_PROXY_LIB += $(PROXIES)/libssl_proxy_bin.a
SYM_PROXY_LIB += $(PROXIES)/libssl_proxy_sym.a

ifdef USE_CRESTIFIED_OPENSSL
	SYM_SSL_LIB = $(OPENSSL_CRESTIFIED)/libssl_sym.a
	SYM_CRYPTO_LIB = $(OPENSSL_CRESTIFIED)/libcrypto_sym.a
else
	SYM_SSL_LIB = $(SSL_LIB)
	SYM_CRYPTO_LIB = $(CRYPTO_LIB)
endif

PROXY_CONF_BIN = $(PROXIES)/openssl_proxies.bin.conf
ifndef PROXY_CONF_SYM
	PROXY_CONF_SYM = $(PROXIES)/openssl_proxies.sym.conf
endif
PROXY_OUT = $(PROXIES)/proxies.out

BIN_CILLY = $(CILLY) --dofunreplace --csec-config=$(PROXY_CONF_BIN) --funreplaceoutput=$(PROXY_OUT) $(CILLY_FLAGS)
SYM_CILLY = $(CILLY) --dofunreplace --csec-config=$(PROXY_CONF_SYM) --funreplaceoutput=$(PROXY_OUT) $(CILLY_FLAGS) --doCrestInstrument --save-temps --commPrintLn

ifndef BUILD_CMD
	BUILD_CMD = $(CC) $(CFLAGS) $(CPPFLAGS) $(BUILD_SRC) $(LDFLAGS) $(LDLIBS) -o $@
endif

ORIG = ${sort $(P1) $(P2) $(P3)}
BIN = ${foreach P,$(ORIG),$(P).bin}
SYM = ${foreach P,$(ORIG),$(P).sym}

BINTRACES = bintrace.P1.out
CVM = cvm.P1.out
IML = iml.P1.out

ifdef P2 
	BINTRACES += bintrace.P2.out
	CVM += cvm.P2.out
	IML += iml.P2.out
endif

ifdef P3 
	BINTRACES += bintrace.P3.out
	CVM += cvm.P3.out
	IML += iml.P3.out
endif


copy: $(IML:.out=.debug.copy.out)

iml.%.debug.copy.out: iml.%.out
	cp iml.$*.debug.out $@

mark:
	grep "(mark)" iml.debug.out > mark.out

iml: iml.out
bin_traces: $(BINTRACES)
cvm: $(CVM)

compile: orig sym

orig: $(ORIG)
bin: $(BIN)
sym: $(SYM)

run: SHELL = /bin/bash
run: orig
	if [ -e "$(P1)" ]; then ./$(P1) $(P1_CMD); fi &  \
	if [ -e "$(P2)" ]; then sleep 1; ./$(P2) $(P2_CMD); fi & \
	if [ -e "$(P3)" ]; then sleep 2; ./$(P3) $(P3_CMD); fi & \
	wait


ifdef DEBUG_IML
iml.out iml.raw.out: $(CVM) $(IMLTRACE)
	{ $(IMLTRACE) $(CVM) iml.raw.out | tee iml.out; } 2>&1 | tee iml.debug.out
else
iml.out iml.raw.out: $(CVM) $(IMLTRACE)
	{ $(IMLTRACE) $(CVM) iml.raw.out | tee iml.out; } > iml.debug.out 2>&1
endif


#annot:
#	rename bin.res.txt bin.annot.txt *.bin.res.txt

#%.bin.res.txt: %.bin.out.txt $(BINTRACE)
#	bintrace $< > $@

$(CVM): $(SYM)
	if [ -e "$(P1).sym" ]; then ./$(P1).sym $(P1_CMD) > cvm.P1.out; fi & \
	if [ -e "$(P2).sym" ]; then sleep 1; ./$(P2).sym $(P2_CMD) > cvm.P2.out; fi & \
	if [ -e "$(P3).sym" ]; then sleep 2; ./$(P3).sym $(P3_CMD) > cvm.P3.out; fi & \
	wait

$(ORIG): BASE_LIB = $(SSL_LIB) $(CRYPTO_LIB)
$(ORIG): CFLAGS += -DVERBOSE
$(ORIG): $(SSL_LIB) $(CRYPTO_LIB)
	$(BUILD_CMD)

%.bin: CFLAGS += -DCSEC_VERIFY
%.bin: CC = $(BIN_CILLY)
%.bin: BASE_LIB = $(BIN_SSL_LIB) $(BIN_CRYPTO_LIB)
%.bin: PROXY_LIB = $(BIN_PROXY_LIB)
%.bin: $(PROXY_CONF_BIN) $(BIN_PROXY_LIB) $(BIN_SSL_LIB) $(BIN_CRYPTO_LIB) 
	$(BUILD_CMD)

%.sym: CFLAGS += -DCSEC_VERIFY
%.sym: CC = $(SYM_CILLY)
%.sym: BASE_LIB = $(SYM_SSL_LIB) $(SYM_CRYPTO_LIB)
%.sym: PROXY_LIB = $(SYM_PROXY_LIB)
%.sym: $(PROXY_CONF_SYM) $(SYM_PROXY_LIB) $(SYM_SSL_LIB) $(SYM_CRYPTO_LIB) 
	$(BUILD_CMD)

# Can't say $(CLIENT).%, because $(CLIENT).c would also match.
# Should work with mpp, see multiple targets in sandbox
$(P1) $(P1).bin $(P1).sym: BUILD_SRC = $(P1_SRC)
$(P1) $(P1).bin $(P1).sym: $(P1_SRC) $(CIL_LIB)

ifneq ($(P1), $(P2))
$(P2) $(P2).bin $(P2).sym: BUILD_SRC = $(P2_SRC)
$(P2) $(P2).bin $(P2).sym: $(P2_SRC) $(CIL_LIB)
endif

ifneq ($(P2), $(P3))
$(P3) $(P3).bin $(P3).sym: BUILD_SRC = $(P3_SRC)
$(P3) $(P3).bin $(P3).sym: $(P3_SRC) $(CIL_LIB)
endif

# can't use an implicit rule due to a bug in make (https://savannah.gnu.org/bugs/index.php?29104)
# makepp doesn't understand this, but do use makepp as soon as bug
# https://sourceforge.net/tracker/?func=detail&aid=2961995&group_id=138953&atid=742140
# is fixed and you can just add libraries to SLL_LIB without fear of cilly mangling them
#$(sort $(CLIENT).bin $(SERVER).bin $(CLIENT).sym $(SERVER).sym $(CLIENT) $(SERVER)): 
#	$(BUILD_CMD)

############################
## ProVerif
############################

ifndef PV_OUTPUTS 
  PV_OUTPUTS = model.pv.out
endif

pv: $(PV_OUTPUTS)
	for f in $(CV_OUTPUTS); do\
		$(PROVERIF) -in pi $^ | grep RESULT;\
	done


pv_full: $(PV_OUTPUTS)
	for f in $(CV_OUTPUTS); do\
		$(PROVERIF) -in pi $^;\
	done


%.pv.out: iml.raw.out %.pv.in $(PITRACE)
	{ $(PITRACE) iml.raw.out $*.pv.in | tee $@; } > $*.pv.debug.out 2>&1


############################
## CryptoVerif
############################

ifndef CV_OUTPUTS 
  CV_OUTPUTS = model.cv.out
endif

cv: $(CV_OUTPUTS)
	for f in $(CV_OUTPUTS); do\
		$(CRYPTOVERIF) -lib $(CV_DEFAULT) $$f | grep RESULT;\
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
  OUTPUTS = iml.out $(PV_OUTPUTS) $(CV_OUTPUTS)
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

PROXY_CALLGRAPH = $(shell find $(PROXIES) -name "*.callgraph.out")
PROXY_GLOBS = $(shell find $(PROXIES) -name "*.globs.out")

filegraph: sym
	cat *.callgraph.out $(PROXIES)/openssl.fullgraph.out | sort -u > fullgraph.out
	mkdir -p defs
	cp *.defs.out defs
	cp -r $(PROXIES)/defs .
	time reachable fullgraph.out | clusterise defs | tee filegraph.out
	cat filegraph.out | sort -u | graph2dot > filegraph.dot
	time dot -Tpdf filegraph.dot > filegraph.pdf

callgraph.out: $(LOCAL_CALLGRAPH) $(PROXY_CALLGRAPH) $(OPENSSL_CALLGRAPH)
	cat $^ > callgraph.out

globs.out: $(LOCAL_GLOBS) $(PROXY_GLOBS) $(OPENSSL_GLOBS)
	cat $^ > globs.out

funlist: callgraph.out globs.out
	@echo "==== Reachable functions not proxied, opaque or crestified:"
	@leaves
	@echo "==== Bad pairs:"
	@badpairs
	@#echo "==== Instrumented boring functions:"
	@#comm -12 boring.out crestified.out
	@#echo "==== Unreachable boring functions:"
	@#comm -23 boring.out leaves.out

############################
## Misc
############################


clean::
	$(RM) *.bin *.sym *.exe *.o *.cil.c *.i *.out

phony:

.PHONY: phony

