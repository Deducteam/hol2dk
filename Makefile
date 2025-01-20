.SUFFIXES:

BASE := $(shell if test -f BASE; then cat BASE; fi)
ROOT_PATH := $(shell if test -f ROOT_PATH; then cat ROOT_PATH; else echo HOLLight; fi)
ERASING := $(shell if test -f ERASING; then cat ERASING; fi)
REQUIRING := $(shell if test -f REQUIRING; then cat REQUIRING; fi)
VOFILES := $(shell if test -f VOFILES; then cat VOFILES; fi)

MAX_PROOF = 500_000
MAX_ABBREV = 2_000_000

HOL2DK := hol2dk --root-path $(ROOT_PATH)

.PHONY: default
default:
	@echo "usage: make TARGET [VAR=VAL ...]"
	@echo "targets: split lp lpo v vo opam clean-<target> clean-all"
	@echo "variables:"
	@echo "  MAX_PROOF: hol2dk max proof size (default is $(MAX_PROOF))"
	@echo "  MAX_ABBREV: hol2dk max abbrev size (default is $(MAX_ABBREV))"

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

.PHONY: lpsig
lpsig: $(BASE_FILES:%=%.lp)

$(BASE_FILES:%=%.lp) &:
	$(HOL2DK) sig $(BASE).lp

.PHONY: vsig
vsig: $(BASE_FILES:%=%.v)

.PHONY: sig
sig: vsig
	$(MAKE) INCLUDE_VO_MK=1 $(BASE_FILES:%=%.vo)

.PHONY: single
single: $(BASE).lp

$(BASE).lp:
	$(HOL2DK) $(BASE).lp

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

ifeq ($(SET_SED_FILES),1)
SED_FILES := $(wildcard *.sed)
endif

BIG_FILES = $(shell for f in `cat BIG_FILES 2> /dev/null | sed -e '/^#/d'`; do if test -f $$f.sti; then echo $$f; fi; done)

.PHONY: echo-big-files
echo-big-files:
	@echo $(BIG_FILES)

.PHONY: find-big-files
find-big-files:
	@if test -f BIG_FILES; then cat BIG_FILES; fi > /tmp/big-files
	@find . -name '*.lp' -size +10M | sed -e 's/^.\///' -e 's/.lp$$//' -e 's/_term_abbrevs//' -e 's/_part_.*$$//' >> /tmp/big-files
	@sort -u /tmp/big-files

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(BIG_FILES:%=%.max)
	$(MAKE) SET_STI_FILES=1 SET_IDX_FILES=1 lp-proofs
	$(MAKE) SET_MIN_FILES=1 lp-abbrevs
	$(HOL2DK) type_abbrevs $(BASE)
	$(MAKE) SET_SED_FILES=1 rename-abbrevs

.PHONY: rename-abbrevs
rename-abbrevs: $(SED_FILES:%.sed=%.lp.rename-abbrevs)

%.lp.rename-abbrevs: %.sed
	sed -i -f $*.sed $*.lp

.PHONY: lp-proofs
lp-proofs: $(STI_FILES:%.sti=%.lp) $(IDX_FILES:%.idx=%.lp)

%.max: %.siz
	$(HOL2DK) --max-proof-size $(MAX_PROOF) thmsplit $(BASE) $*.lp

%.siz: %.sti
	hol2dk thmsize $(BASE) $*

.PRECIOUS: $(BIG_FILES:%=%.siz)

%.lp: %.idx
	$(HOL2DK) --max-abbrev-size $(MAX_ABBREV) thmpart $(BASE) $*.lp

%.lp: %.sti
	$(HOL2DK) theorem $(BASE) $*.lp

.PHONY: lp-abbrevs
lp-abbrevs: $(MIN_FILES:%.min=%.lp)

%.lp: %.min
	$(HOL2DK) abbrev $(BASE) $*.lp

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo-mk rm-mk rm-min rm-max rm-idx rm-brv rm-brp rm-typ rm-sed rm-lpo rm-siz clean-lpo clean-v
	rm -f lpo.mk

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

.PHONY: rm-typ
rm-typ:
	find . -maxdepth 1 -name '*.typ' -delete

.PHONY: rm-sed
rm-sed:
	find . -maxdepth 1 -name '*.sed' -delete

.PHONY: rm-siz
rm-siz:
	find . -maxdepth 1 -name '*.siz' -delete

ifeq ($(INCLUDE_LPO_MK),1)
include lpo.mk

LPO_MK_FILES := theory_hol.lpo.mk $(wildcard *.lpo.mk)

lpo.mk: $(LPO_MK_FILES)
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
	@lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(ERASING) --use-notations --requiring "$(REQUIRING)" $< > $@

.PHONY: clean-v
clean-v: rm-v clean-vo
	rm -f vo.mk

.PHONY: rm-v
rm-v:
	find . -maxdepth 1 -name '*.v' -a -type f -delete

ifeq ($(INCLUDE_VO_MK),1)
include vo.mk

vo.mk: lpo.mk
	cp deps.mk $@
	sed -e 's/\.lp/.v/g' -e "s/^theory_hol.vo:/theory_hol.vo: $(VOFILES) /" lpo.mk >> $@
endif

.PHONY: dep
dep:
	$(MAKE) INCLUDE_VO_MK=1 nothing

.PHONY: nothing
nothing:

.PHONY: vo
vo: $(LP_FILES:%.lp=%.vo)
ifeq ($(PROGRESS),1)
	rm -f .finished
	$(HOL2DK_DIR)/progress &
endif
ifneq ($(INCLUDE_VO_MK),1)
	$(MAKE) INCLUDE_VO_MK=1 vo
	touch .finished
endif

COQC_OPTIONS = -no-glob # -w -coercions
%.vo: %.v
	@echo coqc $<
	@coqc $(COQC_OPTIONS) -R . $(ROOT_PATH) $<

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
opam:
	$(MAKE) INCLUDE_VO_MK=1 $(BASE)_opam.vo

.PRECIOUS: $(BASE)_opam.v

$(BASE)_opam.lp:
	$(HOL2DK) axm $(BASE).lp

.PHONY: clean-opam
clean-opam:
	rm -f $(BASE)_opam.*

.PHONY: clean-all
clean-all: clean-split clean-lp clean-opam rm-dump

.PHONY: rm-dump
rm-dump:
	rm -f dump*.prf

.PHONY: all
all:
	$(MAKE) clean-all
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) vo

.PHONY: votodo
votodo:
	find . -name '*.v' | sort > /tmp/vfiles
	find . -name '*.vo' | sed -e 's/\.vo$$/.v/' | sort > /tmp/vofiles
	diff /tmp/vofiles /tmp/vfiles | sed -e '/^[^>]/d' -e 's/^> .\///' > votodo
	@export v=`wc -l votodo | sed -e 's/ votodo//'`; export n=`find . -name \*.v | wc -l`; echo remains $$v/$$n=`expr $${v}00 / $$n`\% 

.PHONY: lptodo
lptodo: votodo
	sed -e 's/\.v$$/.lp/' votodo > lptodo

.PHONY: clean-lptodo
clean-lptodo: lptodo
	xargs -a lptodo rm -f

.PHONY: clean-votodo
clean-votodo: votodo
	xargs -a votodo rm -f

.PHONY: lpsize
lpsize:
	find . -maxdepth 1 -name '*.lp' -print0 | du --files0-from=- --total -s -h | tail -1
