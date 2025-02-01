BASE := $(shell if test -f BASE; then cat BASE; fi)

.SUFFIXES:

.PHONY: default
default: all

MAKEFILE := $(firstword $(MAKEFILE_LIST))

.PHONY: all
all:
	$(MAKE) -f $(MAKEFILE) update-vfiles
	$(MAKE) -f $(MAKEFILE) update-vo-mk
	$(MAKE) -f $(MAKEFILE) spec
	$(MAKE) -f $(MAKEFILE) rm-spec

.PHONY: usage
usage:
	@echo "usage: make TARGET"
	@echo "TARGETS: update-vfiles update-vo-mk spec rm-spec"
	@echo "WARNING: targets must be done in this order"

FILES := $(shell find . -maxdepth 1 -name '*.v' -a ! -name '*_spec.v' -a ! -name '*_term_abbrevs*.v' -a ! -name $(BASE)_types.v -a ! -name $(BASE)_terms.v -a ! -name $(BASE)_axioms.v -a ! -name $(BASE)_type_abbrevs.v)

.PHONY: update-vfiles
update-vfiles: $(FILES:%=%.update)

%.update:
	sed -i -e 's/^\(Require .*_part_.*_spec\)\.$$/\1_./g' -e '/^Require .*_spec\.$$/d' -e 's/^\(Require .*_part_.*_spec\)_\.$$/\1./' -e "s/^Require Import HOLLight.theory_hol\.$$/Require Import HOLLight.theory_hol HOLLight.$(BASE)_spec./" $*

# https://www.linuxquestions.org/questions/programming-9/how-to-check-duplicate-word-in-line-with-sed-935605/
.PHONY: update-vo-mk
update-vo-mk: vo.mk
	sed -e 's/\([^ ]*_part_[^ ]*_spec\).vo/\1_.vo/g' -e "s/ [^ ]*_spec.vo/ $(BASE)_spec.vo/g" -e 's/_spec_.vo/_spec.vo/g' -e ':a; s/\([^ \.]\+\.vo\) \1/\1/g;ta' vo.mk > new-vo.mk
	echo 'hol_spec.vo: theory_hol.vo hol_types.vo hol_terms.vo' >> new-vo.mk
	touch -r vo.mk new-vo.mk
	cp -p new-vo.mk vo.mk
	rm -f new-vo.mk

vo.mk:
	$(MAKE) dep

.PHONY: spec
spec $(BASE)_spec.v &:
	head -n4 T_DEF_spec.v > $(BASE)_spec.v
	find . -maxdepth 1 -name '*_spec.v' -a ! -name $(BASE)_spec.v -a ! -name '*_part_*_spec.v' | xargs cat | sed -e '/^Require /d' -e 's/^Lemma /Axiom /' -e '/^Proof\./d' >> $(BASE)_spec.v

.PHONY: rm-spec
rm-spec:
	find . -maxdepth 1 -name '*_spec.v' -a ! -name '*_part_*_spec.v' -a ! -name $(BASE)_spec.v -delete
