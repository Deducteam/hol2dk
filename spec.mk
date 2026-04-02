.SUFFIXES:

KIND := $(shell if test -f KIND; then cat KIND; fi)
BASE := $(shell if test -f BASE; then cat BASE; fi)
ROOT_PATH := $(shell if test -f ROOT_PATH; then cat ROOT_PATH; fi)
REQUIRING := $(shell if test -f REQUIRING; then cat REQUIRING; fi)
VOFILES := $(shell if test -f VOFILES; then cat VOFILES; fi)

.PHONY: default
default: all

.PHONY: usage
usage:
	@echo "usage: make TARGET"
	@echo "TARGETS: update-vfiles update-vo-mk gen-base-spec rm-spec-files"
	@echo "WARNING: targets must be done in this order"

MAKEFILE := $(firstword $(MAKEFILE_LIST))

.PHONY: all
all:
	$(MAKE) -f $(MAKEFILE) update-vfiles
	$(MAKE) -f $(MAKEFILE) update-vo-mk
	$(MAKE) -f $(MAKEFILE) gen-base-spec
	$(MAKE) -f $(MAKEFILE) rm-spec-files

FILES := $(shell find . -maxdepth 1 -type f -a -name '*.v' -a ! -name '*_spec.v' -a ! -name '*_term_abbrevs*.v' -a ! -name $(BASE)_types.v -a ! -name $(BASE)_terms.v -a ! -name $(BASE)_axioms.v -a ! -name $(BASE)_type_abbrevs.v $(VOFILES:%.vo=-a ! -name %.v))

.PHONY: update-vfiles
update-vfiles: $(FILES:%=%.update)

# https://stackoverflow.com/questions/71744922/how-do-i-remove-duplicate-lines-using-sed-without-sorting
%.update:
	@echo update $*
	@sed -i -e 's/^\(\(Require\|Include\) .*_part_.*_spec\(\.content(HOL_Light_Context)\|\)\)\.$$/\1_./g' -e "s/^Require .*_spec\.$$/Require Import $(ROOT_PATH).$(BASE)_spec./" -e "s/^Include .*_spec\.content(HOL_Light_Context)\.$$/Include $(ROOT_PATH).$(BASE)_spec.content(HOL_Light_Context)./" -e 's/^\(\(Require\|Include\) .*_part_.*_spec\(\|.content(HOL_Light_Context)\)\)_\.$$/\1./' $*
	@sed -i -e '$$!N; /^\(\(Require\|Include\) .*\)\n\1$$/!P; D' $*

# https://www.linuxquestions.org/questions/programming-9/how-to-check-duplicate-word-in-line-with-sed-935605/
.PHONY: update-vo-mk
update-vo-mk: vo.mk
	@echo update vo.mk ...
	@sed -e 's/\([^ ]*_part_[^ ]*_spec\).vo/\1_.vo/g' -e "s/ [^ ]*_spec.vo/ $(BASE)_spec.vo/g" -e 's/_spec_.vo/_spec.vo/g' -e ':a; s/\([^ \.]\+\.vo\) \1/\1/g;ta' vo.mk > new-vo.mk
	@echo $(BASE)_spec.vo: context.vo >> new-vo.mk
	@touch -r vo.mk new-vo.mk
	@cp -p new-vo.mk vo.mk
	@rm -f new-vo.mk

vo.mk:
	$(MAKE) dep

.PHONY: gen-base-spec
gen-base-spec: $(BASE)_spec.v

$(BASE)_spec.v:
	@echo generate $@ ...
	@echo Require Import $(ROOT_PATH).context. > $@
ifeq ($(KIND),modules)
	@echo Module content\(HOL_Light_Context : HOL_Light_Theory\). >> $@
	@echo Import HOL_Light_Context. >> $@
endif
	@find . -maxdepth 1 -name '*_spec.v' -a ! -name $@ -a ! -name '*_part_*_spec.v' | xargs cat | sed -e '/^\(Require\|Proof\|Section\|End\|Module\|Include\|Context\)/d' -e 's/^Lemma \(\w*\) \(\((\|{\).*\()\|}\)\) :/Axiom \1 : forall \2,/' -e 's/^Lemma /Axiom /' >> $@
ifeq ($(KIND),modules)
	@echo End content. >> $@
endif

.PHONY: rm-spec-files
rm-spec-files:
	find . -maxdepth 1 -name '*_spec.v' -a ! -name '*_part_*_spec.v' -a ! -name $(BASE)_spec.v -delete
