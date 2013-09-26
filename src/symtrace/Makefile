CSEC_ROOT = ../..

include $(CSEC_ROOT)/mk/common.mk

# Debug and profiling:
# can compile with ocamlopt -p to use gprof
# valgrind doesn't need special compilation (just -g)
# OCAMLC_BYTECODE = ocamlcp
# OCAML_FLAGS_BYTECODE = -g -I $(OCAMLYICES_ROOT) -I /usr/local/lib nums.cma ocamlyices.cma str.cma

OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAML_INC = -I $(OCAMLYICES_ROOT) -I /usr/local/lib -I cryptoverif
OCAML_FLAGS = -g $(OCAML_INC) 
OCAML_LIBS = nums.cma ocamlyices.cma str.cma unix.cma
OCAMLOPT_LIBS = $(OCAML_LIBS:.cma=.cmxa)
## OCAML_FLAGS = -g -I $(OCAMLYICES_ROOT) -package num ocamlyices.cmxa -package str -linkpkg 

CV_LIB = cryptoverif/cryptoverif.cmx

SRC = ${wildcard *.ml *.mli}

COMMON_CMO = common.cmo iml.cmo solver.cmo simplify.cmo transform_imltrace.cmo symex.cmo
COMMON_CMX = $(COMMON_CMO:.cmo=.cmx)

# doesn't work:
#$(addprefix -I $(CIL_ROOT), /src /src/frontc $(CIL_OBJDIR))

# pitrace cvtrace
all: imltrace cvtrace
htdoc: doc

imltrace: $(COMMON_CMX) imltrace.cmx
	$(OCAMLOPT) $(OCAML_FLAGS) $(OCAMLOPT_LIBS) -o $@ $^ 

pitrace: $(COMMON_CMX) transform.cmx pitrace.cmx
	$(OCAMLOPT) $(OCAML_FLAGS) $(OCAMLOPT_LIBS) -o $@ $^

cvtrace: $(CV_LIB) $(COMMON_CMX) transform.cmx cvtrace.cmx
	$(OCAMLOPT) $(OCAML_FLAGS) $(OCAMLOPT_LIBS) -o $@ $^

top: $(COMMON_CMO)
	ocamlmktop -o $@ $(OCAML_INC) $(OCAML_LIBS) $^

$(CV_LIB):
	cd cryptoverif && $(MAKE)

doc: $(COMMON_SRC) imltrace.ml pitrace.ml cvtrace.ml
	mkdir -p $@
	touch $@  
	ocamldoc -I $(OCAMLYICES_ROOT) -I $(OCAML_LIB) -I cryptoverif -html -d $@ $^

clean:
	$(RM) cvtrace imltrace top *.cmi *.cmo *.cmx *.o

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAML_FLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAML_FLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAML_FLAGS) -c $<

# Dependencies
.depend: $(SRC)
	ocamldep $(OCAML_INC) *.mli *.ml > .depend

include .depend
	