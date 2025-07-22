.PHONY: check-spec
check-spec: check-spec.mk
	$(MAKE) -f check-spec.mk

HOL2DK_COQ_MODULES := type mappings_N Sig_mappings_N Check_mappings_N With_N Sig_With_N Check_With_N Spec_mappings_N Spec_With_N
HOL2DK_VFILES := $(HOL2DK_COQ_MODULES:%=%.v)

check-spec.mk: $(HOL2DK_VFILES)
	rocq makefile -R . HOLLight $+ -o $@

Spec_With_N.v: Spec_mappings_N.v Sig_With_N.v
	cat $+ | sed -e '/^Require Export HOLLight_Real_With_N.type./d' -e '/^Require HOLLight.Spec_mappings_N./d' -e '/^Module Type Spec./d' -e '/^Include HOLLight.Spec_mappings_N.Spec./d' -e '/^End Spec./d' -e '/^Include Spec./d' > $@

Spec_mappings_N.v: type.v Sig_mappings_N.v
	cat $+ | sed -e '/^Require Export HOLLight_Real_With_N.type./d' -e '/^Module Type Spec./d' -e '/^End Spec./d' -e '/^Include Spec./d' > $@
