.SUFFIXES:

BASE = $(shell if test -f BASE; then cat BASE; fi)

STI_FILES := $(wildcard *.sti)

.PHONY: default
default:
	@echo "targets: split lp dep-lpo lpo v dep-vo vo opam clean-<target> clean-all"

.PHONY: dep
dep: dep-lpo dep-vo

.PHONY: split
split:
	hol2dk split $(BASE)

.PHONY: clean-split
clean-split:
	find . -maxdepth 1 -name '*.sti' -delete
	find . -maxdepth 1 -name '*.nbp' -delete
	find . -maxdepth 1 -name '*.pos' -a ! -name $(BASE).pos -delete
	find . -maxdepth 1 -name '*.use' -a ! -name $(BASE).use -delete
	rm -f $(BASE).thp

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

FILES_WITH_SHARING = $(shell if test -f FILES_WITH_SHARING; then cat FILES_WITH_SHARING; fi)

$(FILES_WITH_SHARING:%=%.lp): HOL2DK_OPTIONS = --max-proofs 500000 --max-abbrevs 250 #--use-sharing

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(STI_FILES:%.sti=%.lp)

%.lp: %.sti
	hol2dk $(HOL2DK_OPTIONS) theorem $(BASE) $@

.PHONY: clean-lp
clean-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

include lpo.mk

lpo.mk:
	touch $@

.PHONY: dep-lpo
dep-lpo:
	find . -maxdepth 1 -name '*.lp' -exec $(HOL2DK_DIR)/dep-lp.sh {} \; > lpo.mk

.PHONY: clean-dep-lpo
clean-dep-lpo:
	rm -f lpo.mk

LP_FILES := $(wildcard *.lp)

.PHONY: lpo
lpo: $(LP_FILES:%.lp=%.lpo)

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: v
v: $(LP_FILES:%.lp=%.v)

%.v: %.lp
	@echo lambdapi export -o stt_coq $<
	@lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp --use-notations --requiring coq.v $< | sed -e 's/^Require Import hol-light\./Require Import /g' > $@

.PHONY: clean-v
clean-v:
	find . -maxdepth 1 -name '*.v' -a ! -name coq.v -delete

.PHONY: dep-vo
dep-vo: lpo.mk
	sed -e 's/\.lpo/.vo/g' -e 's/: theory_hol.vo/: coq.vo theory_hol.vo/' -e 's/theory_hol.vo:/theory_hol.vo: coq.vo/' lpo.mk > vo.mk
#find . -maxdepth 1 -name '*.v' -exec $(HOL2DK_DIR)/dep-coq.sh {} \; > vo.mk

include vo.mk

vo.mk:
	touch $@

.PHONY: clean-dep-vo
clean-dep-vo:
	rm -f vo.mk

.PHONY: vo
vo: $(LP_FILES:%.lp=%.vo)

COQC_OPTIONS = # -w -coercions
%.vo: %.v
	@echo coqc $<
	@coqc $(COQC_OPTIONS) -R . HOLLight $<

.PHONY: clean-vo
clean-vo:
	find . -maxdepth 1 -name '*.vo*' -delete
	find . -maxdepth 1 -name '*.glob' -delete
	find . -maxdepth 1 -name '.*.aux' -delete
	rm -f .lia.cache .nia.cache

.PHONY: opam
opam: $(BASE)_opam.vo

.PRECIOUS: $(BASE)_opam.v

$(BASE)_opam.lp:
	hol2dk axm $(BASE).lp

.PHONY: clean-opam
clean-opam:
	rm -f $(BASE)_opam.*

.PHONY: clean-all
clean-all: clean-split clean-lp clean-dep-lpo clean-lpo clean-v clean-dep-vo clean-vo clean-opam
