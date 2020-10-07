SRC_DIRS	:= src
ALL_VFILES	:= $(sort $(shell find $(SRC_DIRS) -name "*.v"))
ALL_VOFILES	:= $(ALL_VFILES:.v=.vo)
BINS		:= statdb-cli remap-nbd replicate-nbd

COQRFLAGS	:= -R src POCS
COQARGS		:= $(COQRFLAGS) -w -undo-batch-mode

ALECTRYON_OPTIONS := \
	alectryon.py \
	$(HOME)/code/sw/alectryon/alectryon.py \
	$(HOME)/refsrc/alectryon/alectryon.py
ALECTRYON := $(shell for f in $(ALECTRYON_OPTIONS); do if test -e $$f; then echo $$f; break; fi; done)

default: $(ALL_VOFILES)

.coqdeps.d: $(ALL_VFILES)
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	@coqc $(COQARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.vos) $(ALL_VFILES:.v=.vok) $(ALL_VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;

	@echo "CLEAN extraction"
	@rm -rf $(foreach d,$(BINS),$(d)/extract)
	@rm -rf $(foreach d,$(BINS),$(d)/.stack-work)
	@rm -f $(foreach b,$(BINS),bin/$(b))

	@echo "CLEAN doc"
	@rm -f doc/*.html

	rm -f .coqdeps.d

docs: $(ALL_VOFILES)
	./scripts/docs.sh $(ALECTRYON)

.PHONY: default clean docs
.DELETE_ON_ERROR:

%/extract: %/Extract.v %/fiximports.py
	@mkdir -p $@
	coqtop $(COQARGS) -batch -load-vernac-source $<
	./scripts/add-preprocess.sh $@/*.hs

statdb-cli/extract: src/Lab1/StatDbCli.vo
remap-nbd/extract: src/Lab2/RemappedServer.vo
replicate-nbd/extract: src/Lab4/ReplicatedServer.vo

bin/%: %/extract
	mkdir -p $(@D)
	cd $(patsubst %/extract,%,$<) && PATH="$(PATH):"$(shell pwd)"/bin" stack install

lab%-handin.tar.gz:
	tar -czf $@ $$(find . -name "*.v" -or -name "Makefile")
