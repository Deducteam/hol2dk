.SUFFIXES:

BASE = $(shell if test -f BASE; then cat BASE; fi)

.PHONY: default
default:
	@echo "targets: split lp lpo v vo opam clean-<target> clean-all"

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

.PHONY: lp
lp: lp-stage1
	$(MAKE) lp-stage2

STI_FILES := $(wildcard *.sti)

.PHONY: lp-stage1
lp-stage1: $(BASE_FILES:%=%.lp) $(STI_FILES:%.sti=%.lp)

MIN_FILES := $(wildcard *.min)

.PHONY: lp-stage2
lp-stage2: $(MIN_FILES:%.min=%.lp) $(MIN_FILES:%.min=%_type_abbrevs.lp)

HOL2DK_OPTIONS = --max-steps 100000 --max-abbrevs 1000000

FILES_WITH_SHARING = $(shell if test -f FILES_WITH_SHARING; then cat FILES_WITH_SHARING; fi)

#$(FILES_WITH_SHARING:%=%.lp): HOL2DK_OPTIONS = --max-steps 100000 --max-abbrevs 20000 #--use-sharing

%.lp %.lpo.mk %.brv %.brp &: %.sti
	hol2dk $(HOL2DK_OPTIONS) theorem $(BASE) $*.lp

%.lp %_type_abbrevs.lp &: %.min
	hol2dk abbrev $(BASE) $*.lp

.PHONY: clean-lp
clean-lp: clean-mk clean-min clean-brv clean-brp clean-lpo clean-v clean-vo
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: clean-mk
clean-mk:
	find . -maxdepth 1 -name '*.lpo.mk' -delete
	rm -f lpo.mk vo.mk

.PHONY: clean-min
clean-min:
	find . -maxdepth 1 -name '*.min' -delete

.PHONY: clean-brv
clean-brv:
	find . -maxdepth 1 -name '*.brv' -delete

.PHONY: clean-brp
clean-brp:
	find . -maxdepth 1 -name '*.brp' -delete

include lpo.mk

LP_FILES := $(wildcard *.lp)

lpo.mk: $(LP_FILES:%.lp=%.lpo.mk)
	find . -maxdepth 1 -name '*.lpo.mk' | xargs cat > $@
#	find . -maxdepth 1 -name '*.lp' -exec $(HOL2DK_DIR)/dep-lpo {} \; > lpo.mk

theory_hol.lpo.mk: theory_hol.lp
	$(HOL2DK_DIR)/dep-lpo $< > $@

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
clean-v: clean-vo
	find . -maxdepth 1 -name '*.v' -a ! -name coq.v -delete

vo.mk: lpo.mk
	sed -e 's/\.lpo/.vo/g' -e 's/: theory_hol.vo/: coq.vo theory_hol.vo/' -e 's/theory_hol.vo:/theory_hol.vo: coq.vo/' lpo.mk > vo.mk
#	find . -maxdepth 1 -name '*.v' -exec $(HOL2DK_DIR)/dep-vo {} \; > vo.mk

include vo.mk

.PHONY: vo
vo: $(LP_FILES:%.lp=%.vo)

COQC_OPTIONS = # -w -coercions
%.vo: %.v
	@echo coqc $<
	@coqc $(COQC_OPTIONS) -R . HOLLight $<

.PHONY: clean-vo
clean-vo: clean-vos clean-glob clean-aux
	rm -f .lia.cache .nia.cache

.PHONY: clean-vos
clean-vos:
	find . -maxdepth 1 -name '*.vo*' -delete

.PHONY: clean-glob
clean-glob:
	find . -maxdepth 1 -name '*.glob' -delete

.PHONY: clean-aux
clean-aux:
	find . -maxdepth 1 -name '.*.aux' -delete

.PHONY: opam
opam: $(BASE)_opam.vo

.PRECIOUS: $(BASE)_opam.v

$(BASE)_opam.lp:
	hol2dk axm $(BASE).lp

.PHONY: clean-opam
clean-opam:
	rm -f $(BASE)_opam.*

.PHONY: clean-all
clean-all: clean-split clean-lp clean-lpo clean-v clean-vo clean-opam

.PHONY: all
all:
	$(MAKE) clean-all
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) vo
