.PHONY: indent

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst FStar.StructNG.fst

ALL=$(filter-out $(FLAKY) ,$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL))

indent: $(addsuffix -indent, $(ALL))

%-ver: %
	$(FSTAR) $^
	touch $@

%.fst-indent: %.fst
	$(FSTAR) --indent $^ > $^.indent.fst

%.fsti-indent: %.fsti
	$(FSTAR) --indent $^ > $^.indent.fsti

verify-indent: $(addsuffix -verindent, $(wildcard *.indent.fst))

%-verindent: %
	$(FSTAR) $^

wc:
	wc -l prims.fst $(ALL)

##

include ml/Makefile.include

REALIZED=$(addsuffix .fst, $(NOEXTRACT_MODULES))
EXTRACT_ALL=$(filter-out $(REALIZED) $(HYPERSTACK),$(wildcard FStar.*.fst FStar.*.fsti))

.mgen: *.fst
	@# creating a dummy file so that the target is not regenerated unless a file has changed
	touch .mgen
	mkdir -p ml/extracted
	$(FSTAR) --lax --codegen OCaml --odir ml/extracted $(FSTAR_DEFAULT_ARGS) $(EXTRACT_ALL)
