.SUFFIXES:

BASE := $(shell if test -f BASE; then cat BASE; fi)
ROOT_PATH := $(shell if test -f ROOT_PATH; then cat ROOT_PATH; fi)
MAPPING := $(shell if test -f MAPPING; then cat MAPPING; fi)
REQUIRING := $(shell if test -f REQUIRING; then cat REQUIRING; fi)
VOFILES := $(shell if test -f VOFILES; then cat VOFILES; fi)

MAX_PROOF = 500_000
MAX_ABBREV = 2_000_000

HOL2DK := hol2dk --root-path $(ROOT_PATH)

.PHONY: default
default: help

.PHONY: help
help:
	@echo "usage: make TARGET [VAR=VAL ...]"
	@echo "targets: split lp lpo v merge-spec-files rm-empty-deps vo opam clean-<target> clean-all"
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
	find . -maxdepth 1 -name '*.nbp' -a ! -name $(BASE).nbp -delete

.PHONY: rm-pos
rm-pos:
	find . -maxdepth 1 -name '*.pos' -a ! -name $(BASE).pos -delete

.PHONY: rm-use
rm-use:
	find . -maxdepth 1 -name '*.use' -a ! -name $(BASE).use -delete

.PHONY: rm-thp
rm-thp:
	-rm -f $(BASE).thp

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	$(HOL2DK) sig $(BASE).lp

$(BASE)_opam.lp:
	$(HOL2DK) axm $(BASE).lp

.PHONY: opam
opam: $(BASE_FILES:%=%.v) $(BASE)_opam.v

.PHONY: clean-opam
clean-opam:
	-rm -f $(BASE)_opam.*

.PHONY: single
single: $(BASE).lp

$(BASE).lp:
	$(HOL2DK) $(BASE).lp

ifeq ($(INCLUDE_VO_MK),1)
INCLUDE_LPO_MK=1
SET_V_FILES=1
endif

ifeq ($(INCLUDE_LPO_MK),1)
SET_LP_FILES=1
endif

ifeq ($(SET_LP_FILES),1)
LP_FILES := $(wildcard *.lp)
endif

ifeq ($(SET_V_FILES),1)
V_FILES := $(wildcard *.v)
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
	@find . -maxdepth 1 -name '*.lp' -size +10M | sed -e 's/^.\///' -e 's/.lp$$//' -e 's/_term_abbrevs//' -e 's/_part_.*$$//' >> /tmp/big-files
	@sort -u /tmp/big-files

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(BIG_FILES:%=%.max)
	$(MAKE) SET_STI_FILES=1 SET_IDX_FILES=1 lp-proofs
	$(MAKE) SET_MIN_FILES=1 lp-abbrevs
	$(MAKE) $(BASE)_type_abbrevs.lp
	$(MAKE) SET_SED_FILES=1 rename-abbrevs

$(BASE)_type_abbrevs.lp:
	$(HOL2DK) type_abbrevs $(BASE)

.PHONY: rename-abbrevs
rename-abbrevs: $(SED_FILES:%.sed=%.lp.rename-abbrevs)

%.lp.rename-abbrevs: %.lp
	sed -i -f $*.sed $*.lp
	touch $@

.PHONY: rm-rename-abbrevs
rm-rename-abbrevs:
	find . -maxdepth 1 -name '*.rename-abbrevs' -delete

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
clean-lp: rm-lp rm-lpo-mk rm-mk rm-min rm-max rm-idx rm-brv rm-brp rm-typ rm-sed rm-lpo rm-siz rm-rename-abbrevs clean-lpo clean-v
	-rm -f lpo.mk

.PHONY: rm-lp
rm-lp:
	-find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: rm-lpo-mk
rm-lpo-mk:
	-find . -maxdepth 1 -name '*.lpo.mk' -delete

.PHONY: rm-mk
rm-mk:
	-rm -f lpo.mk vo.mk

.PHONY: rm-max
rm-max:
	-find . -maxdepth 1 -name '*.max' -delete

.PHONY: rm-idx
rm-idx:
	-find . -maxdepth 1 -name '*.idx' -delete

.PHONY: rm-brv
rm-brv:
	-find . -maxdepth 1 -name '*.brv' -delete

.PHONY: rm-brp
rm-brp:
	-find . -maxdepth 1 -name '*.brp' -delete

.PHONY: rm-min
rm-min:
	-find . -maxdepth 1 -name '*.min' -delete

.PHONY: rm-typ
rm-typ:
	-find . -maxdepth 1 -name '*.typ' -delete

.PHONY: rm-sed
rm-sed:
	-find . -maxdepth 1 -name '*.sed' -delete

.PHONY: rm-siz
rm-siz:
	-find . -maxdepth 1 -name '*.siz' -delete

ifeq ($(INCLUDE_LPO_MK),1)
include lpo.mk

LPO_MK_FILES := theory_hol.lpo.mk $(wildcard *.lpo.mk)

lpo.mk: $(LPO_MK_FILES)
	-find . -maxdepth 1 -name '*.lpo.mk' | xargs cat > $@

theory_hol.lpo.mk: theory_hol.lp
	echo 'theory_hol.lpo:' > $@
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
	-find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: get-check-mappings
get-check-mappings:
	@echo generate mappings-checking file ...
	@hol2dk check-mappings $(BASE) $(HOL2DK_DIR)/encoding.lp $(HOL2DK_DIR)/renaming.lp $(MAPPING) $(REQUIRING)

ROCQ_OPTIONS = -q -no-glob -w none
.PHONY: check-get-mappings
check-mappings: get-check-mappings $(VOFILES)
	@echo start checking ...
	@rocq compile $(ROCQ_OPTIONS) -R . $(ROOT_PATH) $(BASE)_checkmappings.v
	@echo clean files ...
	@-rm -f $(BASE)_checkmappings.v
	@-rm -f $(BASE)_checkmappings.vo
	@-rm -f $(BASE)_checkmappings.vok
	@-rm -f $(BASE)_checkmappings.vos

.PHONY: v
v: $(LP_FILES:%.lp=%.v)
ifneq ($(SET_LP_FILES),1)
	$(MAKE) SET_LP_FILES=1 $@
endif

%.v: %.lp
	@echo lambdapi export -o stt_coq $<
	@lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --mapping $(MAPPING) --use-notations --requiring "$(REQUIRING)" $< > $@

.PHONY: clean-v
clean-v: rm-v clean-vo
	-rm -f vo.mk

.PHONY: rm-v
rm-v:
	-find . -maxdepth 1 -name '*.v' $(VOFILES:%.vo=-a ! -name %.v) -delete

.PHONY: rm-empty-deps
rm-empty-deps: $(V_FILES:%=%.rm)
ifneq ($(SET_V_FILES),1)
	$(MAKE) SET_V_FILES=1 $@
else
	@echo update vo.mk ...
	@sed -e "s/ theory_hol.vo/ $(VOFILES)/" -e "s/ $(BASE)_types.vo//" -e "s/ $(BASE)_axioms.vo//" vo.mk > new-vo.mk
	@touch -r vo.mk new-vo.mk
	@cp -p new-vo.mk vo.mk
	@-rm -f new-vo.mk
endif

%.v.rm: %.v
	@echo update $<
	@if test ! -h $<; then sed -i -e "/^Require Import $(ROOT_PATH)\.theory_hol\.$$/d" -e "/^Require Import $(ROOT_PATH)\.$(BASE)_types\.$$/d" -e "/^Require Import $(ROOT_PATH)\.$(BASE)_axioms\.$$/d" $<; fi

.PHONY: merge-spec-files
merge-spec-files:
	$(MAKE) -f $(HOL2DK_DIR)/spec.mk

ifeq ($(INCLUDE_VO_MK),1)
include vo.mk
include deps.mk
endif

.PHONY: dep
ifeq ($(INCLUDE_LPO_MK),1)
dep vo.mk &: lpo.mk
	sed -e 's/\.lp/.v/g' -e "s/^theory_hol.vo:/theory_hol.vo: $(VOFILES) /" lpo.mk > vo.mk
else
dep vo.mk &:
	$(MAKE) INCLUDE_LPO_MK=1 dep
endif

.PHONY: vo
vo: $(V_FILES:%.v=%.vo)
ifeq ($(PROGRESS),1)
	-rm -f .finished
	$(HOL2DK_DIR)/progress &
endif
ifneq ($(INCLUDE_VO_MK),1)
	$(MAKE) INCLUDE_VO_MK=1 $@
	touch .finished
endif

%.vo: %.v
	@echo rocq $<
	@rocq compile $(ROCQ_OPTIONS) -R . $(ROOT_PATH) $<

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-cache

.PHONY: rm-vo
rm-vo:
	-find . -maxdepth 1 -name '*.vo*' -delete

.PHONY: rm-glob
rm-glob:
	-find . -maxdepth 1 -name '*.glob' -delete

.PHONY: rm-aux
rm-aux:
	-find . -maxdepth 1 -name '.*.aux' -delete

.PHONY: rm-cache
rm-cache:
	-rm -f .lia.cache .nia.cache

.PHONY: clean-all
clean-all: clean-split clean-lp clean-opam

.PHONY: all
all:
	$(MAKE) clean-all
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) from-v

.PHONY: from-v
from-v:
	$(MAKE) clean-v
	$(MAKE) v
	$(MAKE) merge-spec-files
	$(MAKE) rm-empty-deps
	/usr/bin/time -f "%E" $(MAKE) -k vo

.PHONY: votodo
votodo:
	find . -maxdepth 1 -name '*.v' | sort > /tmp/vfiles
	find . -maxdepth 1 -name '*.vo' | sed -e 's/\.vo$$/.v/' | sort > /tmp/vofiles
	diff /tmp/vofiles /tmp/vfiles | sed -e '/^[^>]/d' -e 's/^> .\///' > votodo
	@export v=`wc -l votodo | sed -e 's/ votodo//'`; export n=`find . -maxdepth 1 -name \*.v | wc -l`; echo remains $$v/$$n=`expr $${v}00 / $$n`\% 

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
