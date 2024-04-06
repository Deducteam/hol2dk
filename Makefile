.SUFFIXES:

BASE = $(shell if test -f BASE; then cat BASE; fi)

.PHONY: default
default:
	@echo "targets: split lp lpo v vo opam clean-<target> clean-all"

.PHONY: split
split:
	hol2dk split $(BASE)

.PHONY: clean-split
clean-split: rm-sti rm-nbp rm-pos rm-use rm-thp

.PHONY: rm-sti
rm-sti:
	find . -maxdepth 1 -name '*.sti' -delete

.PHONY: rm-nbp
rm-nbp:
	find . -maxdepth 1 -name '*.nbp' -delete

.PHONY: rm-pos
rm-pos:
	find . -maxdepth 1 -name '*.pos' -a ! -name $(BASE).pos -delete

.PHONY: rm-use
rm-use:
	find . -maxdepth 1 -name '*.use' -a ! -name $(BASE).use -delete

.PHONY: rm-thp
rm-thp:
	rm -f $(BASE).thp

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

ifeq ($(INCLUDE_VO_MK),1)
INCLUDE_LPO_MK=1
endif

ifeq ($(INCLUDE_LPO_MK),1)
SET_LP_FILES=1
endif

ifeq ($(SET_LP_FILES),1)
LP_FILES := $(wildcard *.lp)
endif

ifeq ($(SET_STI_FILES),1)
STI_FILES := $(wildcard *.sti)
endif

ifeq ($(SET_MIN_FILES),1)
MIN_FILES := $(wildcard *.min)
endif

ifeq ($(SET_IDX_FILES),1)
IDX_FILES := $(wildcard *.idx)
endif

BIG_FILES = $(shell for f in `cat BIG_FILES 2> /dev/null | sed -e '/^#/d'`; do if test -f $$f.sti; then echo $$f; fi; done)

.PHONY: print-big-files
print-big-files:
	@echo $(BIG_FILES)

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(BIG_FILES:%=%.max)
	$(MAKE) SET_STI_FILES=1 SET_IDX_FILES=1 lp-proofs
	$(MAKE) SET_MIN_FILES=1 lp-abbrevs

.PHONY: lp-proofs
lp-proofs: $(STI_FILES:%.sti=%.lp) $(IDX_FILES:%.idx=%.lp)

MAX_PROOF = --max-proof-size 500_000

%.max: %.siz
	hol2dk $(MAX_PROOF) thmsplit $(BASE) $*.lp

%.siz: %.sti
	hol2dk thmsize $(BASE) $*

.PRECIOUS: $(BIG_FILES:%=%.siz)

MAX_ABBREV = --max-abbrev-size 2_000_000

%.lp: %.idx
	hol2dk $(MAX_ABBREV) thmpart $(BASE) $*.lp

%.lp: %.sti
	hol2dk $(HOL2DK_OPTIONS) theorem $(BASE) $*.lp

.PHONY: lp-abbrevs
lp-abbrevs: $(MIN_FILES:%.min=%.lp)

%.lp: %.min
	hol2dk abbrev $(BASE) $*.lp

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo-mk rm-mk rm-min rm-max rm-idx rm-brv rm-brp rm-lpo clean-lpo clean-v

.PHONY: rm-lp
rm-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: rm-lpo-mk
rm-lpo-mk:
	find . -maxdepth 1 -name '*.lpo.mk' -delete

.PHONY: rm-mk
rm-mk:
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

ifeq ($(INCLUDE_LPO_MK),1)
include lpo.mk

LPO_MK_FILES := $(wildcard *.lpo.mk)

lpo.mk: theory_hol.lpo.mk $(LPO_MK_FILES)
	find . -maxdepth 1 -name '*.lpo.mk' | xargs cat > $@

theory_hol.lpo.mk: theory_hol.lp
	$(HOL2DK_DIR)/dep-lpo $< > $@
endif

.PHONY: lpo
lpo: $(LP_FILES:%.lp=%.lpo)
ifneq ($(INCLUDE_LPO_MK),1)
	$(MAKE) INCLUDE_LPO_MK=1 $@
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
	$(MAKE) INCLUDE_VO_MK=1 $@
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
clean-all: clean-split clean-lp clean-opam

.PHONY: all
all:
	$(MAKE) clean-all
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) vo

ifeq ($(SET_THM_FILES),1)
THM_FILES := $(shell find . -name '*.v' -a ! -name '*_spec.v' -a ! -name '*_abbrevs.v' -a ! -name '*_types.v' -a ! -name '*_terms.v' -a ! -name '*_axioms.v' -a ! -name '*_subterms.v' -a ! -name 'theory_hol.v' -a ! -name 'coq.v')
endif

.PHONY: spec
spec: $(THM_FILES:%.v=%_spec.v) $(THM_FILES:%.v=%_spec.lpo.mk)
	$(MAKE) INCLUDE_VO_MK=1

%_spec.v: %.v
	sed -i -e 's/Require Import \([^\.]*\)\./Require Import \1_spec./' -e '/^Require /s/abbrevs_spec/abbrevs/' -e '/^Require /s/coq_spec/coq/' -e '/^Require /s/theory_hol_spec/theory_hol/' -e '/^Require /s/types_spec/types/' -e '/^Require /s/terms_spec/terms/' -e '/^Require /s/axioms_spec/axioms/' $<
	sed -i -e 's/\.lpo/_spec.lpo/g' -e 's/_spec\.lpo:/.lpo:/' -e 's/_abbrevs_spec\.lpo/_abbrevs.lpo/g' -e 's/theory_hol_spec\.lpo/theory_hol.lpo/' -e 's/_types_spec\.lpo/_types.lpo/' -e 's/_terms_spec\.lpo/_terms.lpo/' -e 's/_axioms_spec\.lpo/_axioms.lpo/' $*.lpo.mk
	for f in coq theory_hol $(BASE_FILES) $*_type_abbrevs $*_term_abbrevs; do printf "Require Import %s.\n" $$f; done > $@
	sed -e '/^Require /d' -e '/^Proof. /d' -e 's/^Lemma /Axiom /' -e 's/) :/),/' -e 's/} :/},/' -e 's/^Axiom \([^ ]*\) /Axiom \1 : /' -e 's/: :/:/' -e 's/: \(.*\),/: forall \1,/' $< >> $@

%_spec.lpo.mk:
	echo -n "$*_spec.lpo:" > $@
	for f in theory_hol $(BASE_FILES) $*_type_abbrevs $*_term_abbrevs; do printf " %s.lpo" $$f; done >> $@
	echo >> $@

.PHONY: undo-spec
undo-spec: clean-spec lpo.mk.undo-spec
	$(MAKE) $(THM_FILES:%.v=%.v.undo-spec)

%.v.undo-spec:
	sed -i -e '/^Require /s/_spec//' $*.v
	sed -i -e 's/_spec\.lpo/.lpo/g' $*.lpo.mk

lpo.mk.undo-spec:
	sed -i -e '/_spec\.lpo:/d' -e 's/_spec\.lpo/.lpo/g' lpo.mk

.PHONY: clean-spec
clean-spec: rm-spec rm-spec-lpo-mk

.PHONY: rm-spec
rm-spec:
	find . -maxdepth 1 -name '*_spec.v' -delete

.PHONY: rm-spec-lpo-mk
rm-spec-lpo-mk:
	find . -maxdepth 1 -name '*_spec.lpo.mk' -delete
