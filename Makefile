.SUFFIXES:

BASE = hol

STI_FILES := $(wildcard *.sti)

.PHONY: default
default:
	@echo targets: sti lp mklp lpo v mkv vo

.PHONY: sti
sti:
	hol2dk split $(BASE)

.PHONY: clean-sti
clean-sti:
	find . -maxdepth 1 -name '*.sti' -exec rm -f {} `basename {}`.nbp `basename {}`.pos `basename {}`.use \;
	rm -f $(BASE).thp

BASE_FILES := $(BASE)_types $(BASE)_terms $(BASE)_axioms

$(BASE_FILES:%=%.lp) &:
	hol2dk sig $(BASE).lp

.PHONY: lp
lp: $(BASE_FILES:%=%.lp) $(STI_FILES:%.sti=%.lp)

%.lp: %.sti
	hol2dk theorem $(BASE) $@

.PHONY: clean-lp
clean-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name theory_hol.lp -delete

.PHONY: lpo
lpo: theory_hol.lpo $(BASE_FILES:%=%.lpo) $(STI_FILES:%.sti=%.lpo) $(STI_FILES:%.sti=%_type_abbrevs.lpo) $(STI_FILES:%.sti=%_term_abbrevs.lpo)

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: v
v: theory_hol.v $(BASE_FILES:%=%.v) $(STI_FILES:%.sti=%.v) $(STI_FILES:%.sti=%_type_abbrevs.v) $(STI_FILES:%.sti=%_term_abbrevs.v)

%.v: %.lp
	lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp --use-notations --requiring coq.v $< | sed -e 's/^Require Import hol-light\./Require Import /g' > $@

.PHONY: clean-v
clean-v:
	find . -maxdepth 1 -name '*.v' -a ! -name coq.v -delete

.PHONY: mkv
mkv coq.mk:
	find . -maxdepth 1 -name '*.v' -exec $(HOL2DK_DIR)/dep-coq.sh {} \; > coq.mk

include coq.mk

.PHONY: mklp
mklp lp.mk:
	find . -maxdepth 1 -name '*.lp' -exec $(HOL2DK_DIR)/dep-lp.sh {} \; > lp.mk

include lp.mk

.PHONY: vo
vo: coq.vo theory_hol.vo $(BASE_FILES:%=%.vo) $(STI_FILES:%.sti=%.vo) $(STI_FILES:%.sti=%_type_abbrevs.vo) $(STI_FILES:%.sti=%_term_abbrevs.vo)

%.vo: %.v
	coqc -R . HOLLight $<

.PHONY: clean-vo
clean-vo:
	find . -maxdepth 1 -name '*.vo*' -delete
	find . -maxdepth 1 -name '*.glob' -delete
	find . -maxdepth 1 -name '.*.aux' -delete
	rm -f .lia.cache .nia.cache

.PHONY: clean-all
clean-all: clean-sti clean-lp clean-lpo clean-v clean-vo
	rm -f lp.mk coq.mk
