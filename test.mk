.SUFFIXES:

.PHONY: default
default: test1 test2 test3 test4 test5

clean:
	-rm -rf output1 output2 output3 output4 output5

.PHONY: config
config:
	hol2dk config hol_upto_arith.ml HOLLight Stdlib.NArith.BinNat ../test/type.v ../test/mappings_N.v ../test/mappings_N.mk ../test/mappings_N.lp

# single dk

.PHONY: test1
test1:
	mkdir -p output1
	$(MAKE) -C output1 -f ../test.mk do-test1

.PHONY: do-test1
do-test1: config
	hol2dk hol_upto_arith.dk
	dk check hol_upto_arith.dk

# single lp

.PHONY: test2
test2:
	mkdir -p output2
	$(MAKE) -C output2 -f ../test.mk do-test2

.PHONY: do-test2
do-test2: config
	hol2dk hol_upto_arith.lp
	lambdapi check -v0 -w -c hol_upto_arith.lp

# multi dk

.PHONY: test3
test3:
	mkdir -p output3
	$(MAKE) -C output3 -f ../test.mk do-test3

.PHONY: do-test3
do-test3: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk dk
	dk check hol_upto_arith.dk

# multi lp with mk

.PHONY: test4
test4:
	mkdir -p output4
	$(MAKE) -C output1 -f ../test.mk do-test4

.PHONY: do-test4
do-test4: config
	hol2dk mk 3 hol_upto_arith
	$(MAKE) -f hol_upto_arith.mk lp
	$(MAKE) -f hol_upto_arith.mk lpo
	$(MAKE) -f hol_upto_arith.mk v
	$(MAKE) -f hol_upto_arith.mk vo

# multi lp with split

.PHONY: test5
test5:
	mkdir -p output5
	$(MAKE) -C output5 -f ../test.mk do-test5

.PHONY: do-test5
do-test5: config
	$(MAKE) split
	$(MAKE) lp
	$(MAKE) lpo
	$(MAKE) v
	$(MAKE) merge-spec-files
	$(MAKE) rm-empty-deps
	$(MAKE) vo
