.SUFFIXES:

.PHONY: default
default: test1 test2 test3 test4 test5

# single dk

.PHONY: test1
test1:
	mkdir -p output1
	$(MAKE) -C output1 -f ../test.mk do-test1

.PHONY: do-test1
do-test1:
	hol2dk config hol_upto_arith.ml HOLLight ../test/mappings_N.v ../test/mappings_N.lp
	hol2dk hol_upto_arith.dk
	dk check hol_upto_arith.dk

# single lp

.PHONY: test2
test2:
	mkdir -p output2
	$(MAKE) -C output2 -f ../test.mk do-test2

.PHONY: do-test2
do-test2:
	hol2dk config hol_upto_arith.ml HOLLight ../test/mappings_N.v ../test/mappings_N.lp
	hol2dk hol_upto_arith.lp
	lambdapi check -v0 -w -c hol_upto_arith.lp

# multi dk

.PHONY: test3
test3:
	mkdir -p output3
	$(MAKE) -C output3 -f ../test.mk do-test3

.PHONY: do-test3
do-test3:
	hol2dk config hol_upto_arith.ml HOLLight ../test/mappings_N.v ../test/mappings_N.lp
	hol2dk mk 3 hol_upto_arith
	make -f hol_upto_arith.mk -j3 dk
	dk check hol_upto_arith.dk

# multi lp with mk

.PHONY: test4
test4:
	mkdir -p output4
	$(MAKE) -C output1 -f ../test.mk do-test4

.PHONY: do-test4
do-test4:
	hol2dk config hol_upto_arith.ml HOLLight ../test/mappings_N.v ../test/mappings_N.lp
	hol2dk mk 3 hol_upto_arith
	make -f hol_upto_arith.mk -j3 lp
	make -f hol_upto_arith.mk -j3 lpo
	make -f hol_upto_arith.mk -j3 v

# multi lp with split

.PHONY: test5
test5:
	mkdir -p output5
	$(MAKE) -C output5 -f ../test.mk do-test5

.PHONY: do-test5
do-test5:
	hol2dk config hol_upto_arith.ml HOLLight ../test/mappings_N.v ../test/mappings_N.lp
	make split
	make -j3 lp
	make -j3 lpo
	make -j3 v

# cleaning

clean:
	-rm -rf output1 output2 output3 output4 output5
