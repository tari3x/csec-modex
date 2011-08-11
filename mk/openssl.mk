
# every target should leave the compilation in pristine state:
# both libssl.a and libcrypto.a as well as all object files should be vanilla-compiled

# don't call make clean, it deletes all library files.

# if an object file doesn't exist, OpenSSL makefile will recompile the source and repackage the library


include $(CSEC_ROOT)/mk/common.mk

MK = $(CSEC_ROOT)/mk/openssl.mk

CONF = $(PROXIES)/openssl_proxies.sym.conf
PROXY_OUT = $(OPENSSL_ROOT)/proxies.sym.out

CIL_OUT = $(shell find . -name "*.cil.c")
OUT = $(shell find . -name "*.out")

DIRS = crypto ssl 
# engines

ALL_OBJ = $(shell find $(DIRS) -name "*.o")

SYM_DIRS = ssl crypto/comp crypto/buffer crypto/stack
# crypto/objects
SYM_FILES = crypto/mem.c crypto/dsa/dsa_ossl.c crypto/dsa/dsa_lib.c
# crypto/evp/names.c
SYM_SRC = $(shell find $(SYM_DIRS) -name "*.c" -not -name "*.cil.c") $(SYM_FILES)
# not all source files get compiled, but we need to take only those object files that actually exist
SYM_OBJ = $(shell find $(SYM_DIRS) -name "*.o") $(SYM_FILES:.c=.o)
SYM_CALLGRAPH = $(wildcard $(SYM_SRC:.c=.i.callgraph.out))
ALL_CALLGRAPH = $(wildcard $(ALL_OBJ:.o=.i.callgraph.out))
SYM_GLOBS = $(wildcard $(SYM_SRC:.c=.i.globs.out))

COMPILATION_ROOT = ${shell readlink -f $(OPENSSL_ROOT) }

SYM_CC = cilly --dofunreplace --doCrestInstrument --root=$(COMPILATION_ROOT) --csec-config=$(CONF) --funreplaceoutput=$(PROXY_OUT) --save-temps --commPrintLn -Wno-attributes

# some files that CIL 1.3.7 can't process:
# CIL_EXCLUDE = sha512.c $(shell find crypto/bn crypto/ec a -name "*.c")

CALLGRAPH_CC = cilly --dofunreplace --root=$(COMPILATION_ROOT) --save-temps --commPrintLn -Wno-attributes $(addprefix --leavealone=, $(basename $(notdir $(CIL_EXCLUDE))))

define save
cp libssl.a libssl.a.csec-bak
cp libcrypto.a libcrypto.a.csec-bak
rename .o .o.bak $(OBJ)
endef

define restore 
mv libssl.a.csec-bak libssl.a
mv libcrypto.a.csec-bak libcrypto.a
rename .o.bak .o $(OBJ:.o=.o.bak)
endef

sym: libssl_sym.a

restore:
	$(restore)

#compile: clean
#	$(MAKE) DIRS="$(DIRS)"

libssl_sym.a libcrypto_sym.a: OBJ = $(SYM_OBJ)
libssl_sym.a libcrypto_sym.a: $(CIL_EXEC) $(CONF) $(MK) | proxy_clean
	$(save)
	$(MAKE) DIRS="$(DIRS)" CC="$(SYM_CC)"
	cat $(SYM_CALLGRAPH) > $(OPENSSL_ROOT)/openssl.callgraph.out
	cat $(SYM_GLOBS)     > $(OPENSSL_ROOT)/openssl.globs.out
	mv libssl.a libssl_sym.a
	mv libcrypto.a libcrypto_sym.a
	$(restore)

callgraph: OBJ = $(ALL_OBJ)
callgraph: proxy_clean
	$(save)
	$(MAKE) DIRS="$(DIRS)" CC="$(CALLGRAPH_CC)"
	cat $(ALL_CALLGRAPH) > $(OPENSSL_ROOT)/openssl.callgraph.out
	cp --parents $$(find . -name "*.defs.out") $(OPENSSL_ROOT)/defs
	$(restore)

#$(MAKE) DIRS="$(DIRS)" clean
#$(MAKE) DIRS="$(DIRS)" clean
#$(MAKE)

proxy_clean:
	$(RM) $(PROXY_OUT)

clean: proxy_clean
	$(RM) $(OUT)
	$(RM) $(CIL_OUT)
