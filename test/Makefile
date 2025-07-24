.PHONY: check-spec
check-spec: check-spec.mk
	$(MAKE) -f check-spec.mk

HOL2DK_COQ_MODULES := type mappings_N Sig_mappings_N Check_mappings_N terms theorems With_N Sig_With_N Check_With_N Spec_mappings_N Spec_With_N
HOL2DK_VFILES := $(HOL2DK_COQ_MODULES:%=%.v)

check-spec.mk: $(HOL2DK_VFILES)
	rocq makefile -R . HOLLight $+ -o $@

Spec_%.v: Sig_%.v
	sed -e '/^Module Type Spec./d' -e '/^End Spec./d' -e '/^Include Spec./d' $* > $@

.PHONY: clean
clean:
	-rm -f Spec_With_N.v Spec_mappings_N.v
	$(MAKE) -f check-spec.mk clean
