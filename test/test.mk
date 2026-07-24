.SUFFIXES:

NB_TESTS := 5

TESTS := $(shell seq -f "test%g" $(NB_TESTS))
DIRS := $(TESTS:test%=output%)

.PHONY: default
default: $(TESTS)

test%: output%
	$(MAKE) -C output$* -f ../test/test.mk do-test$*

.PRECIOUS: $(DIRS)

output%:
	mkdir -p output$*

clean:
	-rm -rf $(DIRS)

.PHONY: config
config:
	hol2dk config hol_upto_arith.ml HOLLight Stdlib.NArith.BinNat ../test/type.v ../test/mappings_N.v ../test/mappings_N.mk --mapping ../test/mappings_N.lp --renaming ../test/renaming.lp

# single dk

do-test1: config
	hol2dk hol_upto_arith.dk
	dk check hol_upto_arith.dk

# single lp

do-test2: config
	hol2dk hol_upto_arith.lp
	lambdapi check -v0 -w -c hol_upto_arith.lp

# multi dk

do-test3: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk dk
	dk check hol_upto_arith.dk

# multi lp with mk

do-test4: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk lp
	$(MAKE) -f hol_upto_arith.mk lpo
	$(MAKE) -f hol_upto_arith.mk v
	$(MAKE) -f hol_upto_arith.mk vo

# multi lp with split

do-test5: config
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) merge-spec-files
	$(MAKE) rm-empty-deps
	$(MAKE) vo
