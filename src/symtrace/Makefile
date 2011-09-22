
CSEC_ROOT = ../..

include $(CSEC_ROOT)/mk/common.mk

COMMON_SRC = types.ml utils.ml simplify.ml solver.mli solver_yices.ml solver.ml exp.ml execute.ml
# solver_simple.ml 

# Profiling:
# (can compile with ocamlopt -p to use gprof)
#OCAMLC = ocamlcp
#OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -I /usr/local/lib nums.cma ocamlyices.cma str.cma

# Optimised:
## OCAMLC = ocamlfind ocamlopt 
## -verbose
OCAMLC = ocamlopt
OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -I /usr/local/lib nums.cmxa ocamlyices.cmxa str.cmxa
## OCAML_FLAGS = -g -package ocamlyices -package str -linkpkg 
## OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -package num ocamlyices.cmxa -package str -linkpkg 

# doesn't work:
#$(addprefix -I $(CIL_ROOT), /src /src/frontc $(CIL_OBJDIR))

all: imltrace pitrace
htdoc: doc

imltrace: $(COMMON_SRC) imltrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

pitrace: $(COMMON_SRC) pitrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

doc: $(COMMON_SRC) imltrace.ml pitrace.ml
	mkdir -p $@
	touch $@  
	ocamldoc -html -d $@ $^
  
clean:
	$(RM) imltrace pitrace *.cmi *.cmo *.cmx *.o
