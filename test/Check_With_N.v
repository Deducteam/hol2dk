Require HOLLight.Sig_With_N HOLLight.mappings_N HOLLight.With_N HOLLight.Check_mappings_N.
Require Import Stdlib.NArith.BinNat Stdlib.ZArith.ZArith.

Module Impl : HOLLight.Sig_With_N.Spec.
  
  Include HOLLight.mappings_N.
  Include HOLLight.With_N.

  Include HOLLight.Check_mappings_N.Extra.

  Definition R := Stdlib.Reals.Rdefinitions.R.
  Definition R0 := Stdlib.Reals.Rdefinitions.R0.
  Definition Rle := Stdlib.Reals.Rdefinitions.Rle.
  Definition Rge := Stdlib.Reals.Rdefinitions.Rge.
  Definition Rlt := Stdlib.Reals.Rdefinitions.Rlt.
  Definition Rgt := Stdlib.Reals.Rdefinitions.Rgt.
  Definition Rplus := Stdlib.Reals.Rdefinitions.Rplus.
  Definition Rmult := Stdlib.Reals.Rdefinitions.Rmult.
  Definition Rinv := Stdlib.Reals.Rdefinitions.Rinv.
  Definition Ropp := Stdlib.Reals.Rdefinitions.Ropp.
  Definition Rdiv := Stdlib.Reals.Rdefinitions.Rdiv.
  Definition Rminus := Stdlib.Reals.Rdefinitions.Rminus.
  Definition IZR := Stdlib.Reals.Rdefinitions.IZR.

  Definition Rabs := Stdlib.Reals.Rbasic_fun.Rabs.
  Definition Rmax := Stdlib.Reals.Rbasic_fun.Rmax.
  Definition Rmin := Stdlib.Reals.Rbasic_fun.Rmin.

  Definition Z := Corelib.Numbers.BinNums.Z.
  Definition Z0 := Corelib.Numbers.BinNums.Z0.

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
