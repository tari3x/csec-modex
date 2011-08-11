
include $(CSEC_ROOT)/mk/common.mk

COMMON_SRC = types.ml utils.ml simplify.ml solver.mli solver_yices.ml solver.ml exp.ml execute.ml
# solver_simple.ml 

# use ocamlcp for profiling
# or compile with ocamlopt -p to use gprof
OCAMLC = ocamlfind ocamlopt
OCAML_FLAGS = -g -package ocamlyices -package str -linkpkg 
# doesn't work:
#$(addprefix -I $(CIL_ROOT), /src /src/frontc $(CIL_OBJDIR))

all: symtrace pitrace
htdoc: doc

symtrace: $(COMMON_SRC) symtrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

pitrace: $(COMMON_SRC) pitrace.ml
	$(OCAMLC) $(OCAML_FLAGS) -o $@ $^

doc: $(COMMON_SRC) symtrace.ml pitrace.ml
	mkdir -p $@
	touch $@  
	ocamldoc -html -d $@ $^
  
clean:
	$(RM) symtrace pitrace *.cmi *.cmo *.cmx *.o


