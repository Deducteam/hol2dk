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

#HOL2DK_OPTIONS = --max-steps 20000 --max-abbrevs 500000

#FILES_WITH_SHARING = $(shell if test -f FILES_WITH_SHARING; then cat FILES_WITH_SHARING; fi)

#$(FILES_WITH_SHARING:%=%.lp): HOL2DK_OPTIONS = --max-steps 100000 --max-abbrevs 20000 #--use-sharing

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) lp-stage1
	$(MAKE) lp-stage2
	$(MAKE) lp-stage3

ifeq ($(INCLUDE_VO_MK),1)
INCLUDE_LPO_MK=1
endif

ifeq ($(INCLUDE_LPO_MK),1)
SET_LP_FILES=1
endif

ifeq ($(SET_LP_FILES),1)
STI_FILES := $(wildcard *.sti)

.PHONY: lp-stage1
lp-stage1: $(STI_FILES:%.sti=%.max)
endif

%.max: %.sti
	hol2dk $(HOL2DK_OPTIONS) thmsplit $(BASE) $*.lp

ifeq ($(SET_LP_FILES),1)
IDX_FILES := $(wildcard *.idx)

.PHONY: lp-stage2
lp-stage2: $(IDX_FILES:%.idx=%.lp)
endif

%.lp: %.idx
	hol2dk $(HOL2DK_OPTIONS) thmpart $(BASE) $*.lp

ifeq ($(SET_LP_FILES),1)
MIN_FILES := $(wildcard *.min)

.PHONY: lp-stage3
lp-stage3: $(MIN_FILES:%.min=%.lp)
endif

%.lp: %.min
	hol2dk abbrev $(BASE) $*.lp

.PHONY: clean-lp
clean-lp: rm-lp rm-mk rm-min rm-max rm-idx rm-brv rm-brp rm-lpo clean-v rm-vo

.PHONY: rm-lp
rm-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: rm-mk
rm-mk:
	find . -maxdepth 1 -name '*.lpo.mk' -delete
	rm -f lpo.mk vo.mk

.PHONY: rm-max
rm-max:
	find . -maxdepth 1 -name '*.max' -delete

.PHONY: rm-idx
rm-idx:
	find . -maxdepth 1 -name '*.idx' -delete

.PHONY: rm-brv
rm-brv:
	find . -maxdepth 1 -name '*.brv' -delete

.PHONY: rm-brp
rm-brp:
	find . -maxdepth 1 -name '*.brp' -delete

.PHONY: rm-min
rm-min:
	find . -maxdepth 1 -name '*.min' -delete

ifeq ($(SET_LP_FILES),1)
LP_FILES := $(wildcard *.lp)
endif

ifeq ($(INCLUDE_LPO_MK),1)
include lpo.mk

lpo.mk: theory_hol.lpo.mk $(wildcard *.lpo.mk)
	find . -maxdepth 1 -name '*.lpo.mk' | xargs cat > $@

theory_hol.lpo.mk: theory_hol.lp
	$(HOL2DK_DIR)/dep-lpo $< > $@
endif

.PHONY: lpo
lpo: $(LP_FILES:%.lp=%.lpo)
ifneq ($(INCLUDE_LPO_MK),1)
	$(MAKE) SET_LP_FILES=1 INCLUDE_LPO_MK=1 $@
endif

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo: rm-lpo

.PHONY: rm-lpo
rm-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: v
v: $(LP_FILES:%.lp=%.v)
ifneq ($(SET_LP_FILES),1)
	$(MAKE) SET_LP_FILES=1 $@
endif

%.v: %.lp
	@echo lambdapi export -o stt_coq $<
	@lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp --use-notations --requiring coq.v $< | sed -e 's/^Require Import hol-light\./Require Import /g' > $@

.PHONY: clean-v
clean-v: rm-v clean-vo

.PHONY: rm-v
rm-v:
	find . -maxdepth 1 -name '*.v' -a ! -name coq.v -delete

ifeq ($(INCLUDE_VO_MK),1)
include vo.mk

vo.mk: lpo.mk
	sed -e 's/\.lpo/.vo/g' -e 's/: theory_hol.vo/: coq.vo theory_hol.vo/' -e 's/theory_hol.vo:/theory_hol.vo: coq.vo/' lpo.mk > vo.mk
endif

.PHONY: vo
vo: $(LP_FILES:%.lp=%.vo)
ifneq ($(INCLUDE_VO_MK),1)
	$(MAKE) SET_LP_FILES=1 INCLUDE_LPO_MK=1 INCLUDE_VO_MK=1 $@
endif

COQC_OPTIONS = -no-glob # -w -coercions
%.vo: %.v
	@echo coqc $<
	@coqc $(COQC_OPTIONS) -R . HOLLight $<

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-cache

.PHONY: rm-vo
rm-vo:
	find . -maxdepth 1 -name '*.vo*' -delete

.PHONY: rm-glob
rm-glob:
	find . -maxdepth 1 -name '*.glob' -delete

.PHONY: rm-aux
rm-aux:
	find . -maxdepth 1 -name '.*.aux' -delete

.PHONY: rm-cache
rm-cache:
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
clean-all: clean-split clean-lp clean-lpo clean-v clean-vo clean-opam

.PHONY: all
all:
	$(MAKE) clean-all
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) vo
