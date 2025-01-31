BASE := $(shell if test -f BASE; then cat BASE; fi)
ROOT_PATH := $(shell if test -f ROOT_PATH; then cat ROOT_PATH; fi)
MAPPING := $(shell if test -f MAPPING; then cat MAPPING; fi)
REQUIRING := $(shell if test -f REQUIRING; then cat REQUIRING; fi)
VOFILES := $(shell if test -f VOFILES; then cat VOFILES; fi)

.SUFFIXES:

.PHONY: default
default:
	@echo "usage: make TARGET [VAR=VAL ...]"
	@echo "targets: part lp lpo v vo opam clean-<target> clean-all"
	@echo "variables:"
	@echo "  NB_PARTS"

.PHONY: part
part $(BASE).dg &:
	hol2dk mk $(NB_PARTS) $(BASE)

$(BASE).mk: $(BASE).dg
	hol2dk mkfile $(BASE)

.PHONY: rm-mk
rm-mk:
	rm -f lpo.mk vo.mk

.PHONY: rm-dk
rm-dk:
	find . -maxdepth 1 -name '*.dk' -a ! -name theory_hol.dk -delete

.PHONY: rm-typ
rm-typ:
	find . -maxdepth 1 -name '*.typ' -delete

.PHONY: rm-sed
rm-sed:
	find . -maxdepth 1 -name '*.sed' -delete

.PHONY: rm-lp
rm-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: rm-lpo
rm-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: rm-lpo-mk
rm-lpo-mk:
	find . -maxdepth 1 -name '*.lpo.mk' -delete

.PHONY: rm-v
rm-v:
	find . -maxdepth 1 -name '*.v' -a -type f -delete

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

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo-mk rm-mk rm-typ rm-sed rm-lpo clean-lpo clean-v
	rm -f lpo.mk

.PHONY: clean-lpo
clean-lpo: rm-lpo

.PHONY: clean-v
clean-v: rm-v clean-vo
	rm -f vo.mk

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-cache

.PHONY: clean-all
clean-all: clean-lp

# lp type abbrevs replacement

SED_FILES := $(wildcard *.sed)

.PHONY: rename-abbrevs
rename-abbrevs: $(SED_FILES:%_term_abbrevs.sed=%.lp.rename-abbrevs)

%.lp.rename-abbrevs: %_term_abbrevs.sed
	sed -i -f $*_term_abbrevs.sed $*.lp $*_term_abbrevs.lp
	sed -i -e "s/^require .*_type_abbrevs;/require open $(ROOT_PATH).$(BASE)_type_abbrevs;/" $*.lp $*_term_abbrevs.lp

# lpo file generation

LP_FILES := $(wildcard *.lp)

.PHONY: lpo
lpo: $(LP_FILES:%.lp=%.lpo)

%.lpo: %.lp
	lambdapi check -v0 -w -c $<

include lpo.mk

LPO_MK_FILES := theory_hol.lpo.mk $(wildcard *.lpo.mk)

lpo.mk: $(LPO_MK_FILES)
	find . -maxdepth 1 -name '*.lpo.mk' | xargs cat > $@

theory_hol.lpo.mk: theory_hol.lp
	$(HOL2DK_DIR)/dep-lpo $< > $@

# v file generation

.PHONY: v
v: $(LP_FILES:%.lp=%.v)

%.v: %.lp
	lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --mapping $(MAPPING) --use-notations --requiring "$(REQUIRING)" $< > $@

# vo file generation

.PHONY: vo
vo: $(LP_FILES:%.lp=%.vo)

COQC_OPTIONS = -no-glob # -w -coercions

%.vo: %.v
	@echo coqc $<
	@coqc $(COQC_OPTIONS) -R . $(ROOT_PATH) $<

include vo.mk

vo.mk: lpo.mk
	sed -e 's/\.lp/.v/g' -e "s/^theory_hol.vo:/theory_hol.vo: $(VOFILES) /" lpo.mk > $@

theory_hol.vo: $(VOFILES)

include deps.mk

# dk file generation

# the order is important for generating hol.dk
DK_FILES_TO_GEN := $(shell echo theory_hol $(BASE)_types $(BASE)_terms $(BASE)_axioms; for k in `seq 1 $(NB_PARTS)`; do echo $(BASE)_part_$${k}_type_abbrevs $(BASE)_part_$${k}_term_abbrevs $(BASE)_part_$${k}; done)

.PHONY: dk
dk: $(BASE).dk

$(BASE).dk: $(DK_FILES_TO_GEN:%=%.dk) $(BASE)_theorems.dk
	cat $+ > $@

$(BASE)_types.dk $(BASE)_terms.dk $(BASE)_axioms.dk &: $(BASE).sig
	hol2dk sig $(BASE).dk

$(BASE)_theorems.dk: $(BASE).sig $(BASE).thm $(BASE).pos $(BASE).prf
	hol2dk thm $(BASE).dk

# lp file generation

LP_FILES_TO_GEN := $(shell echo theory_hol $(BASE) $(BASE)_opam $(BASE)_types $(BASE)_terms $(BASE)_axioms; for k in `seq 1 $(NB_PARTS)`; do echo $(BASE)_part_$${k}; done)

.PHONY: lp
lp: $(LP_FILES_TO_GEN:%=%.lp)
	$(MAKE) -f $(BASE).mk $(BASE)_type_abbrevs.lp
	$(MAKE) -f $(BASE).mk rename-abbrevs

$(BASE)_types.lp $(BASE)_terms.lp $(BASE)_axioms.lp &: $(BASE).sig
	hol2dk sig $(BASE).lp

$(BASE).lp: $(BASE).sig $(BASE).thm $(BASE).pos $(BASE).prf
	hol2dk thm $(BASE).lp

$(BASE)_opam.lp: $(BASE).sig $(BASE).thm $(BASE).pos $(BASE).prf
	hol2dk axm $(BASE).lp

$(BASE)_type_abbrevs.lp:
	hol2dk type_abbrevs $(BASE)
	rm -f *_part_*_type_abbrevs.lp *_part_*_type_abbrevs.lpo.mk
