
# vpath %.a $(PROXIES)
# vpath %.a $(OPENSSL_ROOT)

include $(CSEC_ROOT)/mk/common.mk

#CPATH += $(PROXIES) $(OPENSSL_ROOT)/include
#CFLAGS += -I$(OPENSSL_ROOT)/include

CFLAGS += -g2 -Wall -Wno-attributes -Wno-unknown-pragmas -Wno-unused-label

# need to use filename instead of -lcrypto because the linker tends to pick up the system version
LDLIBS += $(BASE_LIB) $(PROXY_LIB) $(BASE_LIB) $(EXTRA_DEPS)
LDLIBS += -lstdc++

SSL_LIB =  $(OPENSSL_ROOT)/libssl.a
BIN_SSL_LIB = $(OPENSSL_ROOT)/libssl_bin.a
SYM_SSL_LIB = $(OPENSSL_ROOT)/libssl_sym.a
CRYPTO_LIB = $(OPENSSL_ROOT)/libcrypto.a
BIN_CRYPTO_LIB = $(OPENSSL_ROOT)/libcrypto_bin.a
SYM_CRYPTO_LIB = $(OPENSSL_ROOT)/libcrypto_sym.a
BIN_PROXY_LIB += $(PROXIES)/libssl_proxy_bin.a
SYM_PROXY_LIB += $(PROXIES)/libssl_proxy_sym.a

PROXY_CONF_BIN = $(PROXIES)/openssl_proxies.bin.conf
ifndef PROXY_CONF_SYM
	PROXY_CONF_SYM = $(PROXIES)/openssl_proxies.sym.conf
endif
PROXY_OUT = $(PROXIES)/proxies.out

BIN_CILLY = cilly --dofunreplace --csec-config=$(PROXY_CONF_BIN) --funreplaceoutput=$(PROXY_OUT) $(CILLY_FLAGS)
SYM_CILLY = cilly --dofunreplace --csec-config=$(PROXY_CONF_SYM) --funreplaceoutput=$(PROXY_OUT) $(CILLY_FLAGS) --doCrestInstrument --save-temps --commPrintLn

BUILD_CMD = $(CC) $(CFLAGS) $(CPPFLAGS) $(BUILD_SRC) $(LDFLAGS) $(LDLIBS) -o $@

ifndef OUTPUTS 
	OUTPUTS = iml.all.out pvmodel.out
endif
GOOD_OUTPUTS = $(OUTPUTS:.out=.good.txt)

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

check: $(GOOD_OUTPUTS)

%.good.txt: %.out
	@if diff $@ $<; then\
		echo "Test OK.";\
    touch $@;\
	else\
		echo "Test not OK.";\
	fi

copy: $(IML:.out=.debug.copy.out)

iml.%.debug.copy.out: iml.%.out
	cp iml.$*.debug.out $@

mark:
	grep "(mark)" iml.debug.out > mark.out

iml: iml.all.out
bin_traces: $(BINTRACES)
cvm: $(CVM)

replace_good: $(OUTPUTS)
	rename out good.txt $^

verify: pvmodel.out
	proverif -in pi $^ | grep RESULT

verify_full: pvmodel.out
	proverif -in pi $^

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

pvmodel.out: $(CVM) query.in env.in crypto.in $(PITRACE)
	{ pitrace $(filter-out $(PITRACE), $^) | tee $@; } > pvmodel.debug.out 2>&1

# FIXME: reverse P1, P2 order when going static
iml.all.out: $(IML)
	echo -n "let A = " > $@
	cat iml.P2.out >> $@
	echo -n "let B = " >> $@
	cat iml.P1.out >> $@
#cat $^ > $@

filegraph: sym
	cat *.callgraph.out $(PROXIES)/openssl.fullgraph.out | sort -u > fullgraph.out
	mkdir -p defs
	cp *.defs.out defs
	cp -r $(PROXIES)/defs .
	time reachable fullgraph.out | clusterise defs | tee filegraph.out
	cat filegraph.out | sort -u | graph2dot > filegraph.dot
	time dot -Tpdf filegraph.dot > filegraph.pdf

callgraph.out: sym $(OPENSSL_ROOT)/openssl.callgraph.out
	cat *.callgraph.out $(OPENSSL_ROOT)/openssl.callgraph.out > callgraph.out

globs.out: sym $(OPENSSL_ROOT)/openssl.globs.out
	cat *.globs.out $(OPENSSL_ROOT)/openssl.globs.out > globs.out

funlist: callgraph.out globs.out
	@echo "==== Reachable functions not proxied, opaque or crestified:"
	@leaves
	@#echo "==== Instrumented boring functions:"
	@#comm -12 boring.out crestified.out
	@#echo "==== Unreachable boring functions:"
	@#comm -23 boring.out leaves.out

#annot:
#	rename bin.res.txt bin.annot.txt *.bin.res.txt

#%.bin.res.txt: %.bin.out.txt $(BINTRACE)
#	bintrace $< > $@
 
iml.%.out: cvm.%.out $(SYMTRACE)
	{ symtrace $< | tee $@; } > iml.$*.debug.out 2>&1

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
$(P1) $(P1).bin $(P1).sym: $(P1_SRC) $(CIL_EXEC)

ifneq ($(P1), $(P2))
$(P2) $(P2).bin $(P2).sym: BUILD_SRC = $(P2_SRC)
$(P2) $(P2).bin $(P2).sym: $(P2_SRC) $(CIL_EXEC)
endif

ifneq ($(P2), $(P3))
$(P3) $(P3).bin $(P3).sym: BUILD_SRC = $(P3_SRC)
$(P3) $(P3).bin $(P3).sym: $(P3_SRC) $(CIL_EXEC)
endif

# can't use an implicit rule due to a bug in make (https://savannah.gnu.org/bugs/index.php?29104)
# makepp doesn't understand this, but do use makepp as soon as bug
# https://sourceforge.net/tracker/?func=detail&aid=2961995&group_id=138953&atid=742140
# is fixed and you can just add libraries to SLL_LIB without fear of cilly mangling them
#$(sort $(CLIENT).bin $(SERVER).bin $(CLIENT).sym $(SERVER).sym $(CLIENT) $(SERVER)): 
#	$(BUILD_CMD)

clean::
	$(RM) *.bin *.sym *.exe *.o *.cil.c *.i *.out

phony:

.PHONY: phony
