all: build_lem

build_lem:
	../../lem/lem btree.lem

build_with_bisect:
	ocamlfind ocamlc \
		-package bisect -linkpkg -syntax camlp4o -o btree btree.ml

clean:
	-rm  btree  *.cmi  *.cmo *.cmp *.out
