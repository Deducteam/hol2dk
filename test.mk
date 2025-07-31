.SUFFIXES:

.PHONY: default
default: test1 test2 test3 test4 test5

test%:
	mkdir -p output$*
	$(MAKE) -C output$* -f ../test.mk do-test$*

clean:
	-rm -rf output1 output2 output3 output4 output5

.PHONY: config
config:
	hol2dk config hol_upto_arith.ml HOLLight Stdlib.NArith.BinNat ../test/type.v ../test/mappings_N.v ../test/mappings_N.mk ../test/mappings_N.lp

# single dk

.PHONY: test1 do-test1
do-test1: config
	hol2dk hol_upto_arith.dk
	dk check hol_upto_arith.dk

# single lp

.PHONY: test2 do-test2
do-test2: config
	hol2dk hol_upto_arith.lp
	lambdapi check -v0 -w -c hol_upto_arith.lp

# multi dk

.PHONY: test3 do-test3
do-test3: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk dk
	dk check hol_upto_arith.dk

# multi lp with mk

.PHONY: test4 do-test4
do-test4: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk lp
	$(MAKE) -f hol_upto_arith.mk lpo
	$(MAKE) -f hol_upto_arith.mk v
	$(MAKE) -f hol_upto_arith.mk vo

# multi lp with split

.PHONY: test5 do-test5
do-test5: config
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) merge-spec-files
	$(MAKE) rm-empty-deps
	$(MAKE) vo
