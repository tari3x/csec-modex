
CSEC_ROOT = ../..

include $(CSEC_ROOT)/mk/common.mk

CV_LIB = cryptoverif/cryptoverif.cmx

COMMON_SRC = types.ml utils.ml simplify.ml solver.mli solver_yices.ml solver.ml exp.ml execute.ml transform.ml
# solver_simple.ml 

# Profiling:
# can compile with ocamlopt -p to use gprof
# valgrind doesn't need special compilation (just -g)
#OCAMLC = ocamlcp
#OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -I /usr/local/lib nums.cma ocamlyices.cma str.cma

# Optimised:
## OCAMLC = ocamlfind ocamlopt 
## -verbose
OCAMLC = ocamlopt
OCAML_INC = -I $(OCAMLYICES_ROOT) -I /usr/local/lib -I cryptoverif
OCAML_FLAGS = -g $(OCAML_INC) nums.cmxa ocamlyices.cmxa str.cmxa
## OCAML_FLAGS = -g -package ocamlyices -package str -linkpkg 
## OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -package num ocamlyices.cmxa -package str -linkpkg 

# doesn't work:
#$(addprefix -I $(CIL_ROOT), /src /src/frontc $(CIL_OBJDIR))

all: imltrace pitrace cvtrace
htdoc: doc

imltrace: $(COMMON_SRC) imltrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

pitrace: $(COMMON_SRC) pitrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

cvtrace: $(CV_LIB) $(COMMON_SRC) cvtrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

$(CV_LIB):
	cd cryptoverif && $(MAKE)

doc: $(COMMON_SRC) imltrace.ml pitrace.ml cvtrace.ml
	mkdir -p $@
	touch $@  
	ocamldoc -I $(OCAMLYICES_ROOT) -I $(OCAML_LIB) -I cryptoverif -html -d $@ $^

clean:
	$(RM) cvtrace *.cmi *.cmo *.cmx *.o
