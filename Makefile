.SUFFIXES:

BASE=hol_upto_arith

STP_FILES := $(wildcard *.stp)

.PHONY: default
default:
	@echo targets: stp lp dep lpo v vo

.PHONY: stp
stp:
	hol2dk split $(BASE)

.PHONY: clean-stp
clean-stp:
	rm -f $(STP_FILES) $(STP_FILES:%.stp=%.pos) $(STP_FILES:%.stp=%.use)

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(STP_FILES:%.stp=%.lp)

%.lp: %.stp
	hol2dk theorem $(BASE) $@

.PHONY: clean-lp
clean-lp:
	rm -f `ls *.lp | grep -v theory_hol.lp`

.PHONY: lpo
lpo: theory_hol.lpo $(BASE_FILES:%=%.lpo) $(STP_FILES:%.stp=%.lpo) $(STP_FILES:%.stp=%_type_abbrevs.lpo) $(STP_FILES:%.stp=%_term_abbrevs.lpo)

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo:
	rm -f *.lpo

.PHONY: v
v: theory_hol.v $(BASE_FILES:%=%.v) $(STP_FILES:%.stp=%.v) $(STP_FILES:%.stp=%_type_abbrevs.v) $(STP_FILES:%.stp=%_term_abbrevs.v)

%.v: %.lp
	lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp --use-notations --requiring coq.v $< | sed -e 's/^Require Import hol-light\./Require Import /g' > $@

.PHONY: clean-v
clean-v:
	rm -f `ls *.v | grep -v coq.v`

.PHONY: dep
dep coq.mk:
	$(HOL2DK_DIR)/coqdep.sh theory_hol.v $(BASE_FILES:%=%.v) $(STP_FILES:%.stp=%.v) $(STP_FILES:%.stp=%_type_abbrevs.v) $(STP_FILES:%.stp=%_term_abbrevs.v) > coq.mk

include coq.mk

.PHONY: vo
vo: coq.vo theory_hol.vo $(BASE_FILES:%=%.vo) $(STP_FILES:%.stp=%.vo) $(STP_FILES:%.stp=%_type_abbrevs.vo) $(STP_FILES:%.stp=%_term_abbrevs.vo)

%.vo: %.v
	coqc -R . HOLLight $<

.PHONY: clean-vo
clean-vo:
	rm -f *.vo* *.glob .lia.cache .nia.cache .*.aux

.PHONY: clean-all
clean-all: clean-stp clean-lp clean-lpo clean-v clean-vo
	rm -f coq.mk
