Require Import coq ClassicalEpsilon.

(*******************************************************************************)
(* Properties of Coq real numbers *)
(*******************************************************************************)

Require Export Rbase Rbasic_fun.

Open Scope R_scope.

Definition R' := {| type := R; el := 0%R |}.

Canonical R'.
(*
Fixpoint Rpower_nat r n : R :=
  match n with
  | 0 => 1
  | S n => r * Rpower_nat r n
  end.

Lemma Rnot_le x y : (~ x <= y) = (x > y).
Proof.
  apply prop_ext; intro h.
  apply Rnot_le_gt. exact h.
  apply Rgt_not_le. exact h.
Qed.

Lemma real_abs_def :
  Rabs = (fun y0 : R => @COND R (Rle (INR (NUMERAL 0)) y0) y0 (Ropp y0)).
Proof.
  apply fun_ext; intro r. unfold Rabs. destruct (Rcase_abs r).
  assert (h: (INR (NUMERAL 0) <= r) = False). rewrite is_False, Rnot_le. exact r0.
  rewrite h, COND_False. reflexivity.
  assert (h: (INR (NUMERAL 0) <= r) = True). rewrite is_True. apply Rge_le. exact r0.
  rewrite h, COND_True. reflexivity.
Qed.

Lemma real_div_def : Rdiv = (fun y0 : R => fun y1 : R => Rmult y0 (Rinv y1)).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. reflexivity.
Qed.

Lemma real_sub_def : Rminus = (fun y0 : R => fun y1 : R => Rplus y0 (Ropp y1)).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. reflexivity.
Qed.

Lemma real_ge_def : Rge = (fun y0 : R => fun y1 : R => Rle y1 y0).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. apply prop_ext; intro h.
  apply Rge_le. exact h. apply Rle_ge. exact h.
Qed.

Lemma real_gt_def : Rgt = (fun y0 : R => fun y1 : R => Rlt y1 y0).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. apply prop_ext; intro h.
  apply Rgt_lt. exact h. apply Rlt_gt. exact h.
Qed.

Lemma real_lt_def : Rlt = (fun y0 : R => fun y1 : R => ~ (Rle y1 y0)).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. apply prop_ext; intro h.
  rewrite Rnot_le. exact h. rewrite Rnot_le in h. exact h.
Qed.

Lemma real_max_def : Rmax = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y1 y0).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. unfold Rmax.
  destruct (Rle_dec x y).
  rewrite <- (is_True (x <= y)) in r. rewrite r, COND_True. reflexivity.
  rewrite <- (is_False (x <= y)) in n. rewrite n, COND_False. reflexivity.
Qed.

Lemma real_min_def : Rmin = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y0 y1).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. unfold Rmin.
  destruct (Rle_dec x y).
  rewrite <- (is_True (x <= y)) in r. rewrite r, COND_True. reflexivity.
  rewrite <- (is_False (x <= y)) in n. rewrite n, COND_False. reflexivity.
Qed.

Lemma REAL_COMPLETE : forall P : R -> Prop,
    ((exists x : R, P x) /\ (exists M : R, forall x : R, (P x) -> Rle x M))
    -> exists M : R, (forall x : R, (P x) -> Rle x M)
               /\ (forall M' : R, (forall x : R, (P x) -> Rle x M') -> Rle M M').
Proof.
  intros P [P_nonempty P_bounded].
  destruct (completeness P P_bounded P_nonempty) as [M M_is_lub].
  exists M. apply M_is_lub.
Qed.

Lemma REAL_LE_ANTISYM : forall x : R, forall y : R, ((Rle x y) /\ (Rle y x)) = (x = y).
Proof.
  intros x y. apply prop_ext.
  intros [h1 h2]. apply Rle_antisym. exact h1. exact h2.
  intro e. subst. split; apply Rle_refl.
Qed.

Lemma REAL_LE_TRANS : forall x : R, forall y : R, forall z : R, ((Rle x y) /\ (Rle y z)) -> Rle x z.
Proof.
  intros x y z [xy yz]. apply Rle_trans with y. exact xy. exact yz.
Qed.

Lemma REAL_LE_TOTAL : forall x : R, forall y : R, (Rle x y) \/ (Rle y x).
Proof.
  intros x y. destruct (Rtotal_order x y) as [lt|[eq|gt]].
  left. apply Rlt_le. exact lt.
  left. apply Req_le. exact eq.
  right. apply Rlt_le. exact gt.
Qed.

Lemma REAL_OF_NUM_ADD: forall m : nat, forall n : nat, (Rplus (INR m) (INR n)) = (INR (Nat.add m n)).
Proof. intros m n. symmetry. apply plus_INR. Qed.

Lemma REAL_LE_MUL: forall x : R, forall y : R, ((Rle (INR (NUMERAL 0)) x) /\ (Rle (INR (NUMERAL 0)) y)) -> Rle (INR (NUMERAL 0)) (Rmult x y).
Proof.
  intros x y. simpl. intros [hx hy]. apply Rmult_le_pos. exact hx. exact hy.
Qed.

Lemma REAL_OF_NUM_MUL: forall m : nat, forall n : nat, (Rmult (INR m) (INR n)) = (INR (Nat.mul m n)).
Proof. intros m n. symmetry. apply mult_INR. Qed.

Lemma real_pow_def : Rpower_nat = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R) (fun real_pow' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R => forall _24085 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : R, (real_pow' _24085 x (NUMERAL 0)) = (INR (NUMERAL (BIT1 0)))) /\ (forall x : R, forall n : nat, (real_pow' _24085 x (S n)) = (Rmult x (real_pow' _24085 x n)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))).
Proof.
  generalize (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))); generalize (@prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Rpower_nat). split; simpl; intro x; reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction y; simpl. rewrite h0. reflexivity. rewrite hs, IHy. reflexivity.
Qed.
*)
(*******************************************************************************)
(* Proof that Coq R is a fourcolor.model of real numbers. *)
(*******************************************************************************)

Definition Rsup : (R -> Prop) -> R.
Proof.
  intro E. case (excluded_middle_informative (bound E)); intro h.
  case (excluded_middle_informative (exists x, E x)); intro i.
  destruct (completeness E h i) as [b j]. exact b.
  exact 0. exact 0.
Defined.

Lemma is_lub_Rsup E : bound E -> (exists x, E x) -> is_lub E (Rsup E).
Proof.
  intros h i. unfold Rsup. case (excluded_middle_informative (bound E)); intro h'.
  case (excluded_middle_informative (exists x, E x)); intro i'.
  destruct (completeness E h' i') as [b j]. exact j. contradiction. contradiction.
Qed.

Require Import fourcolor.real.
Import Real.

Definition R_struct : structure := {|
  val := R;
  le := Rle;
  sup := Rsup;
  add := Rplus;
  zero := R0;
  opp := Ropp; 
  mul := Rmult;
  one := R1;
  inv := Rinv
|}.

Canonical R_struct.

Lemma Rsup_upper_bound E : has_sup E -> ub E (Rsup E).
Proof.
  intros [i j]. unfold Rsup. case (excluded_middle_informative (bound E)); intro c.
  case (excluded_middle_informative (exists x : R, E x)); intro d.
  destruct (completeness E c d) as [b [k l]]. intros x h. apply k. exact h.
  intros x h. assert (exists x : R, E x). exists x. exact h. contradiction.
  intros x h. assert (exists x : R, E x). exists x. exact h. contradiction.
Qed.

Lemma Rsup_total E x : has_sup E -> down E x \/ Rle (sup E) x.
Proof.  
  intros [i [b j]]. case (classic (down E x)); intro k. auto. right.
  assert (l : bound E). exists b. exact j.
  generalize (is_lub_Rsup E l i); intros [m n]. apply n.
  intros y hy.
  unfold down in k. rewrite ex2_eq, not_exists_eq in k.
  generalize (k y); intro k'. rewrite not_conj_eq, not_or_eq in k'.
  unfold Rle. left. apply Rnot_le_lt. apply k'. exact hy.
Qed.

(* Remark: in fourcolor, le is primitive and eq is defined as the
intersection of le and the inverse of le, but in coq, lt is primitive
and le is defined from lt and Logic.eq. *)

Lemma eq_R_struct : @eq R_struct = @Logic.eq R.
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  apply prop_ext; intro h. destruct h as [h i]. apply Rle_antisym; auto.
  subst y. split; apply Rle_refl.
Qed.

Lemma Radd_commutative (x y : val R_struct) : eq (add x y) (add y x).
Proof. rewrite eq_R_struct. apply Rplus_comm. Qed.

Lemma Radd_associative (x y z : val R_struct) :
  eq (add x (add y z)) (add (add x y) z).
Proof. rewrite eq_R_struct. rewrite Rplus_assoc. reflexivity. Qed.

Lemma Radd_zero_left x : eq (add (zero R_struct) x) x.
Proof. rewrite eq_R_struct. apply Rplus_0_l. Qed.

Lemma Radd_opposite_right x : eq (add x (opp x)) (zero R_struct).
Proof. rewrite eq_R_struct. apply Rplus_opp_r. Qed.

Lemma Rmul_commutative (x y : val R_struct) : eq (mul x y) (mul y x).
Proof. rewrite eq_R_struct. apply Rmult_comm. Qed.

Lemma Rmul_associative (x y z : val R_struct) :
  eq (mul x (mul y z)) (mul (mul x y) z).
Proof. rewrite eq_R_struct. rewrite Rmult_assoc. reflexivity. Qed.

Lemma Rmul_distributive_right (x y z : val R_struct) :
  eq (mul x (add y z)) (add (mul x y) (mul x z)).
Proof. rewrite eq_R_struct. apply Rmult_plus_distr_l. Qed.

Lemma Rmul_one_left x : eq (mul (one R_struct) x) x.
Proof. rewrite eq_R_struct. apply Rmult_1_l. Qed.

Lemma Rmul_inverse_right x : ~eq x (zero R_struct) -> eq (mul x (inv x)) (one R_struct).
Proof. rewrite eq_R_struct. apply Rinv_r. Qed.

Lemma Rone_nonzero : ~ eq (one R_struct) (zero R_struct).
Proof. rewrite eq_R_struct. apply R1_neq_R0. Qed.

Lemma R_axioms : axioms R_struct.
Proof.
  apply Axioms.
  apply Rle_refl.
  apply Rle_trans.
  apply Rsup_upper_bound.
  apply Rsup_total.  
  apply Rplus_le_compat_l.
  apply Radd_commutative.
  apply Radd_associative.
  apply Radd_zero_left.
  apply Radd_opposite_right.
  apply Rmult_le_compat_l.
  apply Rmul_commutative.
  apply Rmul_associative.
  apply Rmul_distributive_right.
  apply Rmul_one_left.
  apply Rmul_inverse_right.
  apply Rone_nonzero.
Qed.

Definition R_model : model := {|
  model_structure := R_struct;
  model_axioms := R_axioms;
|}.

Lemma eq_R_model :
  @eq (model_structure R_model) = @Logic.eq (val (model_structure R_model)).
Proof. exact eq_R_struct. Qed.

Close Scope R_scope.

(*******************************************************************************)
(* Subtype *)
(*******************************************************************************)

Section Subtype.

  Variables (A : Type) (P : A -> Prop) (a : A) (h : P a).

  Definition subtype := {| type := {x : A | P x}; el := exist P a h |}.

  Definition dest : subtype -> A := fun x => proj1_sig x.
  
  Definition mk : A -> subtype :=
    fun x => COND_dep (P x) subtype (exist P x) (fun _ => exist P a h).

  Lemma dest_mk x : P x = (dest (mk x) = x).
  Proof.
    apply prop_ext.
    intro hx. unfold mk, COND_dep. destruct excluded_middle_informative.
    reflexivity. contradiction.
    destruct (mk x) as [b i]. simpl. intro e. subst x. exact i.
  Qed.

  Lemma mk_dest x : mk (dest x) = x.
  Proof.
    unfold mk, COND_dep. destruct x as [b i]; simpl.
    destruct excluded_middle_informative.
    rewrite (proof_irrelevance _ p i). reflexivity.
    contradiction.
  Qed.

End Subtype.

Arguments subtype [A P a].
Arguments mk [A P a].
Arguments dest [A P a].
Arguments dest_mk [A P a].
Arguments mk_dest [A P a].

Canonical subtype.

(*******************************************************************************)
(* Quotient *)
(*******************************************************************************)

Section Quotient.

  Variables (A : Type') (R : A -> A -> Prop).

  Definition is_eq_class X := exists a, X = R a.

  Definition class_of x := R x.

  Lemma is_eq_class_of x : is_eq_class (class_of x).
  Proof. exists x. reflexivity. Qed.

  Local Definition a := el A.
  
  Definition quotient := subtype (is_eq_class_of a).

  Definition mk_quotient : (A -> Prop) -> quotient := mk (is_eq_class_of a).
  Definition dest_quotient : quotient -> (A -> Prop) := dest (is_eq_class_of a).

  Lemma mk_dest_quotient : forall x, mk_quotient (dest_quotient x) = x.
  Proof. exact (mk_dest (is_eq_class_of a)). Qed.

  Lemma dest_mk_quotient : forall x, is_eq_class x = (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk (is_eq_class_of a)). Qed.

End Quotient.

Arguments quotient [A].
Arguments mk_quotient [A].
Arguments dest_quotient [A].
Arguments mk_dest_quotient [A].
Arguments dest_mk_quotient [A].

(*******************************************************************************)
(* Nearly additive sequences of natural numbers *)
(*******************************************************************************)

Import Coq.Init.Datatypes.

Definition dist := fun _22820 : prod nat nat => Nat.add (Nat.sub (@fst nat nat _22820) (@snd nat nat _22820)) (Nat.sub (@snd nat nat _22820) (@fst nat nat _22820)).

Definition is_nadd := fun _23130 : nat -> nat => exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (Nat.mul m (_23130 n)) (Nat.mul n (_23130 m)))) (Nat.mul B (Nat.add m n)).

Lemma DIST_REFL : forall n : nat, dist (n,n) = 0.
Proof.
  intro n. unfold dist. simpl. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma is_nadd_0 : is_nadd (fun _ => 0).
Proof. exists 0. intros m n. rewrite !Nat.mul_0_r, DIST_REFL. reflexivity. Qed.    

Definition nadd := subtype is_nadd_0.

Definition mk_nadd := mk is_nadd_0.
Definition dest_nadd := dest is_nadd_0.

Lemma axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.
Proof. exact (mk_dest is_nadd_0). Qed.

Lemma axiom_20 : forall (r : nat -> nat), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).
Proof. exact (dest_mk is_nadd_0). Qed.

Definition nadd_of_num : nat -> nadd := fun _23288 : nat => mk_nadd (fun n : nat => Nat.mul _23288 n).

Definition nadd_le : nadd -> nadd -> Prop := fun _23295 : nadd => fun _23296 : nadd => exists B : nat, forall n : nat, Peano.le (dest_nadd _23295 n) (Nat.add (dest_nadd _23296 n) B).

Definition nadd_add : nadd -> nadd -> nadd := fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : nat => Nat.add (dest_nadd _23311 n) (dest_nadd _23312 n)).

Definition nadd_mul : nadd -> nadd -> nadd := fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : nat => dest_nadd _23325 (dest_nadd _23326 n)).

Definition nadd_rinv : nadd -> nat -> nat := fun _23462 : nadd => fun n : nat => Nat.div (Nat.mul n n) (dest_nadd _23462 n).

Definition nadd_eq : nadd -> nadd -> Prop := fun _23276 : nadd => fun _23277 : nadd => exists B : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd _23276 n) (dest_nadd _23277 n))) B.

Definition nadd_inv : nadd -> nadd := fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv _23476)).

(*******************************************************************************)
(* hreal *)
(*******************************************************************************)

Definition hreal := quotient nadd_eq.

Definition mk_hreal := mk_quotient nadd_eq.
Definition dest_hreal := dest_quotient nadd_eq.

Lemma axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.
Proof. exact (mk_dest_quotient nadd_eq). Qed.

Lemma axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).
Proof. exact (dest_mk_quotient nadd_eq). Qed.

Definition hreal_of_num : nat -> hreal := fun m : nat => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u).

Definition hreal_add : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Definition hreal_mul : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Definition hreal_le : hreal -> hreal -> Prop := fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Definition hreal_inv : hreal -> hreal := fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x')).

(*******************************************************************************)
(* Operations on treal (pairs of hreal's) *)
(*******************************************************************************)

Definition treal_of_num : nat -> prod hreal hreal := fun _23721 : nat => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL 0)).

Definition treal_neg : (prod hreal hreal) -> prod hreal hreal := fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726).

Definition treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736)).

Definition treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758))).

Definition treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779)).

Definition treal_inv : (prod hreal hreal) -> prod hreal hreal := fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d)))))).

Definition treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810)).

(*******************************************************************************)
(* HOL-Light real numbers *)
(*******************************************************************************)

Definition real := quotient treal_eq.

Module real.

Definition mk_real := mk_quotient treal_eq.
Definition dest_real := dest_quotient treal_eq.

Lemma axiom_23 : forall (a : real), (mk_real (dest_real a)) = a.
Proof. exact (mk_dest_quotient treal_eq). Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof. exact (dest_mk_quotient treal_eq). Qed.

End real.

Import real.

Definition real_le : real -> real -> Prop := fun x1 : real => fun y1 : real => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1'))).

Definition real_add : real -> real -> real := fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1'))).

Definition real_mul : real -> real -> real := fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1'))).

Definition real_neg : real -> real := fun x1 : real => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1')).

Definition real_of_num : nat -> real := fun m : nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u).

Definition real_inv : real -> real := fun x : real => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x')).

(*******************************************************************************)
(* Proof that real is a fourcolor.model of real numbers. *)
(*******************************************************************************)

Axiom REAL_COMPLETE: forall P : real -> Prop, ((exists x : real, P x) /\ (exists M : real, forall x : real, (P x) -> real_le x M)) -> exists M : real, (forall x : real, (P x) -> real_le x M) /\ (forall M' : real, (forall x : real, (P x) -> real_le x M') -> real_le M M').

Definition real_sup : (real -> Prop) -> real.
Proof.
  intro P. case (excluded_middle_informative (exists x, P x)); intro h.
  case (excluded_middle_informative (exists M, forall x, (P x) -> real_le x M)); intro i.
  set (Q := fun M => (forall x : real, P x -> real_le x M) /\
                    (forall M' : real, (forall x : real, P x -> real_le x M') -> real_le M M')).
  exact (ε Q). exact (real_of_num 0). exact (real_of_num 0).
Defined.

Definition real_struct : structure := {|
  val := real;
  le := real_le;
  sup := real_sup;
  add := real_add;
  zero := real_of_num 0;
  opp := real_neg;
  mul := real_mul;
  one := real_of_num 1;
  inv := real_inv
|}.

Canonical real_struct.

Lemma real_sup_is_lub E :
  has_sup E -> ub E (real_sup E) /\ (forall b, ub E b -> real_le (real_sup E) b).
Proof.
  intros [i j]. unfold real_sup.
  destruct (excluded_middle_informative (exists x : real, E x)).
  destruct (excluded_middle_informative (exists M : real, forall x : real, E x -> real_le x M)).
  set (Q := fun M : real =>
              (forall x : real, E x -> real_le x M) /\
                (forall M' : real, (forall x : real, E x -> real_le x M') -> real_le M M')).
  assert (k: exists M : real, Q M). apply (REAL_COMPLETE E (conj i j)).
  generalize (ε_spec k); intros [l m]. auto. contradiction. contradiction.
Qed.

Lemma real_sup_upper_bound E : has_sup E -> ub E (real_sup E).
Proof. intro h. apply (proj1 (real_sup_is_lub E h)). Qed.

Axiom REAL_LT_IMP_LE : forall x : real, forall y : real, (lt x y) -> real_le x y.

Lemma real_sup_total E x : has_sup E -> down E x \/ real_le (real_sup E) x.
Proof.
  intro h. case (classic (down E x)); intro k. auto. right.
  generalize (real_sup_is_lub E h); intros [i j]. apply j.
  intros y hy.
  unfold down in k. rewrite ex2_eq, not_exists_eq in k.
  generalize (k y); intro k'. rewrite not_conj_eq, not_or_eq in k'.
  apply REAL_LT_IMP_LE. auto.
Qed.

Axiom REAL_LE_REFL: forall x : real, real_le x x.
Axiom REAL_LE_TRANS: forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le y z)) -> real_le x z.
Axiom REAL_LE_LADD: forall x : real, forall y : real, forall z : real, (real_le (real_add x y) (real_add x z)) = (real_le y z).
Axiom REAL_ADD_SYM: forall x : real, forall y : real, (real_add x y) = (real_add y x).
Axiom REAL_LE_ANTISYM: forall x : real, forall y : real, ((real_le x y) /\ (real_le y x)) = (x = y).
Axiom REAL_ADD_ASSOC: forall x : real, forall y : real, forall z : real, (real_add x (real_add y z)) = (real_add (real_add x y) z).
Axiom REAL_ADD_LID: forall x : real, (real_add (real_of_num (NUMERAL 0)) x) = x.
Axiom REAL_ADD_LINV: forall x : real, (real_add (real_neg x) x) = (real_of_num (NUMERAL 0)).
Axiom REAL_LE_LMUL: forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_le y z)) -> real_le (real_mul x y) (real_mul x z).
Axiom REAL_MUL_SYM: forall x : real, forall y : real, (real_mul x y) = (real_mul y x).
Axiom REAL_MUL_ASSOC: forall x : real, forall y : real, forall z : real, (real_mul x (real_mul y z)) = (real_mul (real_mul x y) z).
Axiom REAL_ADD_LDISTRIB: forall x : real, forall y : real, forall z : real, (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z)).
Axiom REAL_MUL_LID: forall x : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) x) = x.
Axiom REAL_MUL_LINV: forall x : real, (~ (x = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x) x) = (real_of_num (NUMERAL (BIT1 0))).
Axiom REAL_OF_NUM_EQ: forall m : nat, forall n : nat, ((real_of_num m) = (real_of_num n)) = (m = n).
Axiom REAL_INV_0 : (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).

Lemma eq_real_struct: @eq real_struct = @Logic.eq real.
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  unfold eq. rewrite REAL_LE_ANTISYM. reflexivity.
Qed.

Lemma real_axioms : axioms real_struct.
Proof.
  apply Axioms.
  apply REAL_LE_REFL.
  intros x y z xy yz; apply (REAL_LE_TRANS x y z (conj xy yz)).
  apply real_sup_upper_bound.
  apply real_sup_total.
  intros x y z yz; rewrite REAL_LE_LADD; exact yz.
  intros x y. rewrite eq_real_struct. apply REAL_ADD_SYM.
  intros x y z. rewrite eq_real_struct. apply REAL_ADD_ASSOC.
  intro x. rewrite eq_real_struct. apply REAL_ADD_LID.
  intro x. rewrite eq_real_struct. rewrite REAL_ADD_SYM. apply REAL_ADD_LINV.
  intros x y z hx yz. apply REAL_LE_LMUL. auto.
  intros x y. rewrite eq_real_struct. apply REAL_MUL_SYM.
  intros x y z. rewrite eq_real_struct. apply REAL_MUL_ASSOC.
  intros x y z. rewrite eq_real_struct. apply REAL_ADD_LDISTRIB.
  intro x. rewrite eq_real_struct. apply REAL_MUL_LID.
  intro x. rewrite eq_real_struct. rewrite REAL_MUL_SYM. apply REAL_MUL_LINV.
  unfold one, zero. simpl. rewrite eq_real_struct, REAL_OF_NUM_EQ. auto.
Qed.

Definition real_model : model := {|
  model_structure := real_struct;
  model_axioms := real_axioms;
|}.

Lemma eq_real_model:
  @eq (model_structure real_model) = @Logic.eq (val (model_structure real_model)).
Proof. exact eq_real_struct. Qed.

Require Import fourcolor.realcategorical.

Definition R_of_real := @Rmorph_to real_model R_model.
Definition real_of_R := @Rmorph_to R_model real_model.

Lemma R_of_real_of_R r : R_of_real (real_of_R r) = r.
Proof. rewrite <- eq_R_model. apply (@Rmorph_to_inv R_model real_model). Qed.

Lemma real_of_R_of_real r : real_of_R (R_of_real r) = r.
Proof. rewrite <- eq_real_model. apply (@Rmorph_to_inv real_model R_model). Qed.

(*******************************************************************************)
(* Mapping of HOL-Light reals to Coq reals. *)
(*******************************************************************************)

Definition mk_real : ((prod hreal hreal) -> Prop) -> R := fun x => R_of_real (mk_real x).

Definition dest_real : R -> (prod hreal hreal) -> Prop := fun x => dest_real (real_of_R x).

Lemma axiom_23 : forall (a : R), (mk_real (dest_real a)) = a.
Proof. intro a. unfold mk_real, dest_real. rewrite axiom_23. apply R_of_real_of_R. Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof.
  intro c. unfold dest_real, mk_real. rewrite real_of_R_of_real, <- axiom_24.
  reflexivity.  
Qed.

(*Lemma R_of_real_morph : morphism R_of_real.
Proof. apply Rmorph_toP. Qed.*)

Lemma real_of_R_morph : morphism real_of_R.
Proof. apply Rmorph_toP. Qed.

Lemma le_morph_R x y : le x y = le (real_of_R x) (real_of_R y).
Proof.
  generalize (morph_le real_of_R_morph x y); intros [h i]. apply prop_ext; auto.
Qed.

Lemma real_le_def : Rle = (fun x1 : R => fun y1 : R => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  unfold dest_real. rewrite le_morph_R.
  generalize (real_of_R x); clear x; intro x.
  generalize (real_of_R y); clear y; intro y.
  reflexivity.
Qed.

Lemma add_morph_R x y : real_of_R (add x y) = (add (real_of_R x) (real_of_R y)).
Proof. rewrite <- eq_real_model. apply (morph_add real_of_R_morph). Qed.

Lemma add_eq x y : add x y = R_of_real (add (real_of_R x) (real_of_R y)).
Proof. rewrite <- add_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_add_def : Rplus = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  rewrite add_eq. unfold mk_real. apply f_equal. reflexivity.
Qed.

Lemma mul_morph_R x y : real_of_R (mul x y) = (mul (real_of_R x) (real_of_R y)).
Proof. rewrite <- eq_real_model. apply (morph_mul real_of_R_morph). Qed.

Lemma mul_eq x y : mul x y = R_of_real (mul (real_of_R x) (real_of_R y)).
Proof. rewrite <- mul_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_mul_def : Rmult = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  rewrite mul_eq. unfold mk_real. apply f_equal. reflexivity.
Qed.

Lemma zero_morph_R : real_of_R 0%R = real_of_num 0.
Proof. rewrite <- eq_real_model. apply (morph_zero real_of_R_morph). Qed.

Lemma zero_eq : 0%R = R_of_real (real_of_num 0).
Proof. rewrite <- zero_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma inv_morph_R x : real_of_R (inv x) = inv (real_of_R x).
Proof.
  case (classic (x = 0%R)); intro h.
  subst x. unfold inv. simpl. rewrite Rinv_0, zero_eq, !real_of_R_of_real.
  Set Printing All.
  change (@Logic.eq (type real) (real_of_num O) (real_inv (real_of_num O))).
  symmetry. apply REAL_INV_0.
  rewrite <- eq_real_model. apply (morph_inv real_of_R_morph).
  rewrite eq_R_model. exact h.
  Unset Printing All.
Qed.

Lemma inv_eq x : inv x = R_of_real (inv (real_of_R x)).
Proof. rewrite <- inv_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_inv_def : Rinv = (fun x : R => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x'))).
Proof. apply fun_ext; intro x. rewrite inv_eq. unfold mk_real. reflexivity. Qed.

Lemma neg_morph_R x : real_of_R (opp x) = opp (real_of_R x).
Proof. rewrite <- eq_real_model. apply (morph_opp real_of_R_morph). Qed.

Lemma neg_eq x : opp x = R_of_real (opp (real_of_R x)).
Proof. rewrite <- neg_morph_R, R_of_real_of_R. reflexivity. Qed.

Lemma real_neg_def : Ropp = (fun x1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1'))).
Proof. apply fun_ext; intro x. rewrite neg_eq. unfold mk_real. reflexivity. Qed.

Lemma one_morph_R : real_of_R 1%R = real_of_num 1.
Proof. rewrite <- eq_real_model. apply (morph_one real_of_R_morph). Qed.

Lemma one_eq : 1%R = R_of_real (real_of_num 1).
Proof. rewrite <- one_morph_R, R_of_real_of_R. reflexivity. Qed.

Require Import Lia.

Lemma INR_eq n : INR (S n) = (INR n + 1)%R.
Proof.
  induction n; simpl.
  rewrite Rplus_0_l. reflexivity.
  destruct n as [|n]. reflexivity. reflexivity.
Qed.

Lemma real_of_num_def : INR = (fun m : nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).
Proof.
  apply fun_ext. induction x.
  simpl INR. rewrite zero_eq. reflexivity.
  rewrite INR_eq, IHx, add_eq, one_morph_R.
  unfold mk_real. f_equal.
  rewrite real_of_R_of_real.
  clear IHx.
  unfold real_of_num.
  
  clear IHx. unfold treal_of_num, hreal_of_num, nadd_of_num.
  simpl.
  set (Nadd := {x0 : nat -> nat | is_nadd x0}).
  set (Hreal := {x0 : Nadd -> Prop | is_eq_class nadd nadd_eq x0}).
  unfold mk_nadd.
  
  cut (forall y, forall x, x < y -> INR x = mk_real (fun u : hreal * hreal => treal_eq (treal_of_num x) u)).
  intros h x. apply (h (S x)). lia.
  induction y; intros x hx.
  lia.
  destruct x as [|x]; simpl INR.
  rewrite zero_eq. reflexivity.
  destruct x as [|x].
  rewrite one_eq. reflexivity.
  rewrite <- IHy.
  rewrite IHy. 2: lia.
Qed.
