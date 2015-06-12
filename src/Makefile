LEM:=$(shell command -v ../src_ext/lem/lem || command -v lem)
LEMFLAGS:=-only_changed_output -wl_unused_vars ign -wl_rename err
EXTRACTDIR:=$(shell dirname $(LEM))/ocaml-lib/
CAMLCINCLUDES:=-I $(EXTRACTDIR) extract.cma

BTREE_FILE:=btree.lem
ISA_GEN_DIR:=isabelle/gen_isabelle
OC_GEN_DIR:=ocaml/gen_ocaml
CAMLC:=ocamlfind ocamlc nums.cma $(CAMLCINCLUDES) -package zarith


all: build_lem generate_isa_btree generate_ocaml_btree build_ocaml build_ocaml_with_bisect

build_lem: $(BTREE_FILE)
	$(LEM) $(BTREE_FILE)

generate_isa_btree: build_lem
	mkdir -p $(ISA_GEN_DIR)
	$(LEM) -isa -add_full_isa_lib_path -outdir $(ISA_GEN_DIR) $(BTREE_FILE)
	chmod ugo-w $(ISA_GEN_DIR)/*

generate_ocaml_btree: build_lem
	mkdir -p $(OC_GEN_DIR)
	$(LEM) -ocaml -outdir $(OC_GEN_DIR) $(BTREE_FILE)
	chmod ugo-w $(OC_GEN_DIR)/btree.ml

build_ocaml: generate_ocaml_btree
	$(CAMLC) -linkpkg -o $(OC_GEN_DIR)/btree $(OC_GEN_DIR)/btree.ml
	-ln -s $(OC_GEN_DIR)/btree btree

build_ocaml_with_bisect: generate_ocaml_btree
	$(CAMLC) \
		-package bisect -linkpkg -syntax camlp4o -o $(OC_GEN_DIR)/btree_bisect $(OC_GEN_DIR)/btree.ml

clean:
	-rm -rf $(OC_GEN_DIR) $(ISA_GEN_DIR)
