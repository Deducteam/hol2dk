.SUFFIXES:

BASE = hol

STP_FILES := $(wildcard *.stp)

.PHONY: default
default:
	@echo targets: stp lp mklp lpo v mkv vo

.PHONY: stp
stp:
	hol2dk split $(BASE)

.PHONY: clean-stp
clean-stp:
	find . -name '*.stp' -exec rm -f {} `basename {}`.pos `basename {}`.use \;

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(STP_FILES:%.stp=%.lp)

%.lp: %.stp
	hol2dk theorem $(BASE) $@

.PHONY: clean-lp
clean-lp:
	find . -maxdepth 0 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: lpo
lpo: theory_hol.lpo $(BASE_FILES:%=%.lpo) $(STP_FILES:%.stp=%.lpo) $(STP_FILES:%.stp=%_type_abbrevs.lpo) $(STP_FILES:%.stp=%_term_abbrevs.lpo)

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo:
	find . -maxdepth 0 -name '*.lpo' -delete

.PHONY: v
v: theory_hol.v $(BASE_FILES:%=%.v) $(STP_FILES:%.stp=%.v) $(STP_FILES:%.stp=%_type_abbrevs.v) $(STP_FILES:%.stp=%_term_abbrevs.v)

%.v: %.lp
	lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp --use-notations --requiring coq.v $< | sed -e 's/^Require Import hol-light\./Require Import /g' > $@

.PHONY: clean-v
clean-v:
	find . -maxdepth 0 -name '*.v' -a ! -name coq.v -delete

.PHONY: mkv
mkv coq.mk:
	find . -maxdepth 0 -name '*.v' -exec $(HOL2DK_DIR)/dep-coq.sh {} \; > coq.mk

include coq.mk

.PHONY: mklp
mklp lp.mk:
	find . -maxdepth 0 -name '*.lp' -exec $(HOL2DK_DIR)/dep-lp.sh {} \; > lp.mk

include lp.mk

.PHONY: vo
vo: coq.vo theory_hol.vo $(BASE_FILES:%=%.vo) $(STP_FILES:%.stp=%.vo) $(STP_FILES:%.stp=%_type_abbrevs.vo) $(STP_FILES:%.stp=%_term_abbrevs.vo)

%.vo: %.v
	coqc -R . HOLLight $<

.PHONY: clean-vo
clean-vo:
	find . -maxdepth 0 -name '*.vo*' -delete
	find . -maxdepth 0 -name '*.glob' -delete
	find . -maxdepth 0 -name '.*.aux' -delete
	rm -f .lia.cache .nia.cache

.PHONY: clean-all
clean-all: clean-stp clean-lp clean-lpo clean-v clean-vo
	rm -f coq.mk
