SHELL:=bash

#LEMFLAGS:=-only_changed_output -wl_unused_vars ign -wl_rename err
LEM:=$(shell command -v ../src_ext/lem/lem || command -v lem)
EXTRACTDIR:=$(shell dirname $(LEM))/ocaml-lib/
CAMLCINCLUDES:=-I $(EXTRACTDIR) extract.cma
CAMLC:=ocamlfind ocamlc nums.cma $(CAMLCINCLUDES) -linkpkg # -package zarith

BTREE_FILE:=btree.lem
ISA_GEN_DIR:=isabelle/gen_isabelle
OC_GEN_DIR:=ocaml/gen_ocaml
COVERAGE_DIR=ocaml/result_$(shell date -I)
BISECT_FILE=$(shell find $(COVERAGE_DIR) -name bisect*.out)

all: build_lem generate_isa_btree generate_ocaml_btree build_ocaml

build_lem: $(BTREE_FILE)
	$(LEM) $(BTREE_FILE)

generate_isa_btree: build_lem
	make -C isabelle

generate_ocaml_btree: build_lem
	mkdir -p $(OC_GEN_DIR)
	$(LEM) -ocaml -outdir $(OC_GEN_DIR) $(BTREE_FILE)
	chmod ugo-w $(OC_GEN_DIR)/*.ml

build_ocaml: generate_ocaml_btree
	$(CAMLC) -a -o $(OC_GEN_DIR)/btree.cma $(OC_GEN_DIR)/btree.ml

run_ocaml_tests: build_ocaml
	$(CAMLC) \
		-package bisect -syntax camlp4o -o $(OC_GEN_DIR)/tests -I $(OC_GEN_DIR) $(OC_GEN_DIR)/btree.ml $(OC_GEN_DIR)/btreeAuxiliary.ml
	./$(OC_GEN_DIR)/tests
	mkdir -p $(COVERAGE_DIR)
	mv bisect*.out $(COVERAGE_DIR)
	bisect-report -html $(COVERAGE_DIR) $(BISECT_FILE)
	echo "to see the report use:"
	echo "firefox $(COVERAGE_DIR)/index.html"

clean:
	-rm -rf $(OC_GEN_DIR) $(ISA_GEN_DIR)
