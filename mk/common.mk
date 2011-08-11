
# some system dependency, I guess autoconf would be real nice here
ifdef WINDIR
  EXTRA_DEPS = -lwsock32 -ladvapi32 -lgdi32 -luser32
  CIL_OBJDIR = /obj/x86_WIN32
  # stupid make can't account for exe extension on cygwin
  # no, it actually seems to be fine
  # EXE = .exe 
else
  EXTRA_DEPS = -ldl
  CIL_OBJDIR = /obj/x86_LINUX
endif

CIL_EXEC = $(CIL_ROOT)/$(CIL_OBJDIR)/cil.a

PROXIES = $(CSEC_ROOT)/proxies

BINTRACE = ${shell readlink -f $$(which bintrace)}
SYMTRACE = ${shell readlink -f $$(which symtrace)}
PITRACE  = ${shell readlink -f $$(which pitrace)}

PROXY_SYM_CILLY = cilly --doCrestInstrument --csec-config=$(PROXY_CONF_SYM) --save-temps --commPrintLn
