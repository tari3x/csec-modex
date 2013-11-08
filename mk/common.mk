
CSEC_ROOT_ABS = /home/avatar/docs/verification/svn/csec-modex

CIL_ROOT = /home/avatar/docs/verification/svn/csec-modex/deps/cil-1.3.7-svn

OCAMLYICES_ROOT = /home/avatar/docs/verification/svn/csec-modex/deps/ocamlyices

CIL_OBJDIR = /home/avatar/docs/verification/svn/csec-modex/deps/cil-1.3.7-svn/obj/x86_LINUX
CIL_LIB = /home/avatar/docs/verification/svn/csec-modex/deps/cil-1.3.7-svn/obj/x86_LINUX/cil.a

OPENSSL = /home/avatar/docs/verification/svn/csec-modex/deps/openssl-1.0.0d
OPENSSL_CRESTIFIED = /home/avatar/docs/verification/svn/csec-modex/deps/openssl-1.0.0d-crestified

PROXIES = /home/avatar/docs/verification/svn/csec-modex/proxies

IMLTRACE = /home/avatar/docs/verification/svn/csec-modex/src/symtrace/imltrace
PITRACE  = /home/avatar/docs/verification/svn/csec-modex/src/symtrace/pitrace
CVTRACE  = /home/avatar/docs/verification/svn/csec-modex/src/symtrace/cvtrace

PROVERIF = /home/avatar/docs/verification/svn/csec-modex/deps/proverif1.84/proverif

CV_ROOT = /home/avatar/docs/verification/svn/csec-modex/deps/cryptoverif1.12
CRYPTOVERIF = /home/avatar/docs/verification/svn/csec-modex/deps/cryptoverif1.12/cryptoverif
CV_DEFAULT = /home/avatar/docs/verification/svn/csec-modex/deps/cryptoverif1.12/default

CILLY = /home/avatar/docs/verification/svn/csec-modex/deps/cil-1.3.7-svn/bin/cilly

PROXY_SYM_CILLY = $(CILLY) --doCrestInstrument --csec-config=$(PROXY_CONF_SYM) --save-temps --commPrintLn

OCAML_LIB = /home/avatar/.opam/4.00.1/lib/ocaml

# some system dependency, I guess autoconf would be real nice here
# ifdef WINDIR
#   EXTRA_DEPS = -lwsock32 -ladvapi32 -lgdi32 -luser32
#   CIL_OBJDIR = /obj/x86_WIN32
#   # stupid make can't account for exe extension on cygwin
#   # no, it actually seems to be fine
#   # EXE = .exe 
# else
#   EXTRA_DEPS = -ldl
#   CIL_OBJDIR = /obj/x86_LINUX
# endif
