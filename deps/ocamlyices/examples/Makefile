TEST = one two future

all: native byte

byte: $(TEST:=.byte)

native: $(TEST:=.opt)

%.byte: %.ml
	#ocamlc -I +ocamlyices nums.cma ocamlyices.cma $< -o $@
	ocamlfind ocamlc -package ocamlyices -linkpkg $< -o $@

%.opt: %.ml
	#ocamlopt -I +ocamlyices nums.cmxa ocamlyices.cmxa $< -o $@
	ocamlfind ocamlopt -package ocamlyices -linkpkg $< -o $@

clean:
	$(RM) *.cmi *.cmo *.cmx *.o
	$(RM) *.byte *.opt

.PHONY: all native byte clean distclean mrproper
