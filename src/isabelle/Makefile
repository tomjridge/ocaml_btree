LEM:=$(shell command -v ../../src_ext/lem/lem || command -v lem)
ISA_GEN_DIR:=gen_isabelle
all: ../btree.lem
	mkdir -p $(ISA_GEN_DIR)
	$(LEM) -isa -add_full_isa_lib_path -outdir $(ISA_GEN_DIR) ../btree.lem
	chmod ugo-w $(ISA_GEN_DIR)/*.thy
