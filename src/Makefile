

all: build

build:
	ocamlc btree.ml -o btree

build_with_bisect:
	ocamlfind ocamlc \
		-package bisect -linkpkg -syntax camlp4o -o btree btree.ml

clean:
	-rm  btree  *.cmi  *.cmo *.cmp *.out
