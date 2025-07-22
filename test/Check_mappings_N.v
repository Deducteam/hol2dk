Require HOLLight.Sig_mappings_N HOLLight.mappings_N.
Require Import HOLLight_Real_With_N.type Coq.NArith.BinNat Coq.ZArith.ZArith.

Module Extra.
  
  Definition GEQ {A:Type'} := @eq A.

  Module ExtensionalityFacts := Coq.Logic.ExtensionalityFacts.
  
  Definition N := Coq.Numbers.BinNums.N.
  Definition N0 := Coq.Numbers.BinNums.N0.

  Module N.
    Definition succ := N.succ.
    Definition pred := N.pred.
    Definition double := N.double.
    Definition mul := N.mul.
    Definition add := N.add.
    Definition sub := N.sub.
    Definition lt := N.lt.
    Definition le := N.le.
    Definition gt := N.gt.
    Definition ge := N.ge.
    Definition pow := N.pow.
    Definition max := N.max.
    Definition min := N.min.
    Definition div := N.div.
    Definition modulo := N.modulo.
    Definition Even := N.Even.
    Definition Odd := N.Odd.
  End N.

  Module List.
    Definition rev := List.rev.
    Definition map := List.map.
    Definition removelast := List.removelast.
    Definition Forall := List.Forall.
    Definition ForallOrdPairs := List.ForallOrdPairs.
    Definition In := List.In.
  End List.

  Module Ascii.
    Definition ascii := Coq.Strings.Ascii.ascii.
    Definition zero := Coq.Strings.Ascii.zero.
  End Ascii.

End Extra.

Module Impl : HOLLight.Sig_mappings_N.Spec.
  Include mappings_N.
  Include Extra.
End Impl.
