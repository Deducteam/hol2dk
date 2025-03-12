Require HOLLight.Sig_With_N HOLLight_Real_With_N.mappings HOLLight.With_N HOLLight.Check_mappings_N.
Require Import Coq.NArith.BinNat Coq.ZArith.ZArith.

Module Impl : HOLLight.Sig_With_N.Spec.
  
  Include HOLLight_Real_With_N.mappings.
  Include HOLLight.With_N.

  Include HOLLight.Check_mappings_N.Extra.

  Definition R := Coq.Reals.Rdefinitions.R.
  Definition R0 := Coq.Reals.Rdefinitions.R0.
  Definition Rle := Coq.Reals.Rdefinitions.Rle.
  Definition Rge := Coq.Reals.Rdefinitions.Rge.
  Definition Rlt := Coq.Reals.Rdefinitions.Rlt.
  Definition Rgt := Coq.Reals.Rdefinitions.Rgt.
  Definition Rplus := Coq.Reals.Rdefinitions.Rplus.
  Definition Rmult := Coq.Reals.Rdefinitions.Rmult.
  Definition Rinv := Coq.Reals.Rdefinitions.Rinv.
  Definition Ropp := Coq.Reals.Rdefinitions.Ropp.
  Definition Rdiv := Coq.Reals.Rdefinitions.Rdiv.
  Definition Rminus := Coq.Reals.Rdefinitions.Rminus.
  Definition IZR := Coq.Reals.Rdefinitions.IZR.

  Definition Rabs := Coq.Reals.Rbasic_fun.Rabs.
  Definition Rmax := Coq.Reals.Rbasic_fun.Rmax.
  Definition Rmin := Coq.Reals.Rbasic_fun.Rmin.

  Definition Z := Coq.Numbers.BinNums.Z.
  Definition Z0 := Coq.Numbers.BinNums.Z0.

  Module Z.
    Definition le := Z.le.
    Definition lt := Z.lt.
    Definition ge := Z.ge.
    Definition gt := Z.gt.
    Definition opp := Z.opp.
    Definition add := Z.add.
    Definition sub := Z.sub.
    Definition mul := Z.mul.
    Definition abs := Z.abs.
    Definition sgn := Z.sgn.
    Definition max := Z.max.
    Definition min := Z.min.
    Definition divide := Z.divide.
  End Z.

End Impl.
