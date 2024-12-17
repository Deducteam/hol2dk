(*****************************************************************************)
(* Proof that Coq R is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Require Import HOLLight_Real.HOLLight_Real Rbase Rdefinitions Rbasic_fun.

Open Scope R_scope.

Definition R' := {| type := R; el := 0%R |}.

Canonical R'.

Require Import Coq.Logic.ClassicalEpsilon.

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

Require Import fourcolor.reals.real.
Import Real.
Require Import Coq.Init.Datatypes.

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
  generalize (k y); intro k'. rewrite not_conj_eq, <- imp_eq_disj in k'.
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

Lemma R_axioms : axioms R_struct.
Proof.
  apply Axioms.
  apply Rle_refl.
  apply Rle_trans.
  apply Rsup_upper_bound.
  apply Rsup_total.  
  apply Rplus_le_compat_l.
  intros x y. rewrite eq_R_struct. apply Rplus_comm.
  intros x y z. rewrite eq_R_struct. rewrite Rplus_assoc. reflexivity.
  intro x. rewrite eq_R_struct. apply Rplus_0_l.
  intro x. rewrite eq_R_struct. apply Rplus_opp_r.
  apply Rmult_le_compat_l.
  intros x y. rewrite eq_R_struct. apply Rmult_comm.
  intros x y z. rewrite eq_R_struct. rewrite Rmult_assoc. reflexivity.
  intros x y z. rewrite eq_R_struct. apply Rmult_plus_distr_l.
  intro x. rewrite eq_R_struct. apply Rmult_1_l.
  intro x. rewrite eq_R_struct. apply Rinv_r.
  rewrite eq_R_struct. apply R1_neq_R0.
Qed.

Definition R_model : model := {|
  model_structure := R_struct;
  model_axioms := R_axioms;
|}.

Lemma eq_R_model :
  @eq (model_structure R_model) = @Logic.eq (val (model_structure R_model)).
Proof. exact eq_R_struct. Qed.

Close Scope R_scope.

(*****************************************************************************)
(* Proof that real is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Require Import HOLLight_Real.terms.

Lemma real_add_of_num p q :
  real_of_num (p + q) = real_add (real_of_num p) (real_of_num q).
Proof.
  unfold real_of_num, real_add.
  f_equal. rewrite treal_add_of_num. apply fun_ext; intro x.
  apply prop_ext; intro h.

  exists (treal_of_num p). exists (treal_of_num q). split. exact h. split.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num p). reflexivity.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num q). reflexivity.

  destruct h as [p' [q' [h1 [h2 h3]]]].
  rewrite axiom_24_aux in h2. 2: exists (treal_of_num p); reflexivity.
  rewrite axiom_24_aux in h3. 2: exists (treal_of_num q); reflexivity.
  rewrite h2, h3. exact h1.
Qed.

Definition real_sup : (real -> Prop) -> real.
Proof.
  intro P. case (excluded_middle_informative (exists x, P x)); intro h.
  case (excluded_middle_informative (exists M, forall x, (P x) -> real_le x M)); intro i.
  set (Q := fun M => (forall x : real, P x -> real_le x M) /\
                    (forall M' : real, (forall x : real, P x -> real_le x M')
                                  -> real_le M M')).
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

Require Import HOLLight_Real.theorems.

Lemma real_sup_is_lub E :
  has_sup E -> ub E (real_sup E) /\ (forall b, ub E b -> real_le (real_sup E) b).
Proof.
  intros [i j]. unfold real_sup.
  destruct (excluded_middle_informative (exists x : real, E x)).
  destruct (excluded_middle_informative (exists M : real, forall x : real, E x -> real_le x M)).
  set (Q := fun M : real =>
              (forall x : real, E x -> real_le x M) /\
                (forall M' : real, (forall x : real, E x -> real_le x M') -> real_le M M')).
  assert (k: exists M : real, Q M). apply (thm_REAL_COMPLETE E (conj i j)).
  generalize (ε_spec k); intros [l m]. auto. contradiction. contradiction.
Qed.

Lemma real_sup_upper_bound E : has_sup E -> ub E (real_sup E).
Proof. intro h. apply (proj1 (real_sup_is_lub E h)). Qed.

Lemma real_sup_total E x : has_sup E -> down E x \/ real_le (real_sup E) x.
Proof.
  intro h. case (classic (down E x)); intro k. auto. right.
  generalize (real_sup_is_lub E h); intros [i j]. apply j.
  intros y hy.
  unfold down in k. rewrite ex2_eq, not_exists_eq in k.
  generalize (k y); intro k'. rewrite not_conj_eq, <- imp_eq_disj in k'.
  apply thm_REAL_LT_IMP_LE. apply k'. apply hy.
Qed.

Lemma eq_real_struct: @eq real_struct = @Logic.eq real.
Proof.
  apply fun_ext; intro x. apply fun_ext; intro y.
  unfold eq. rewrite thm_REAL_LE_ANTISYM. reflexivity.
Qed.

Lemma real_axioms : axioms real_struct.
Proof.
  apply Axioms.
  apply thm_REAL_LE_REFL.
  intros x y z xy yz; apply (thm_REAL_LE_TRANS x y z (conj xy yz)).
  apply real_sup_upper_bound.
  apply real_sup_total.
  intros x y z yz; rewrite thm_REAL_LE_LADD; exact yz.
  intros x y. rewrite eq_real_struct. apply thm_REAL_ADD_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_ASSOC.
  intro x. rewrite eq_real_struct. apply thm_REAL_ADD_LID.
  intro x. rewrite eq_real_struct. rewrite thm_REAL_ADD_SYM. apply thm_REAL_ADD_LINV.
  intros x y z hx yz. apply thm_REAL_LE_LMUL. auto.
  intros x y. rewrite eq_real_struct. apply thm_REAL_MUL_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_MUL_ASSOC.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_LDISTRIB.
  intro x. rewrite eq_real_struct. apply thm_REAL_MUL_LID.
  intro x. rewrite eq_real_struct. rewrite thm_REAL_MUL_SYM. apply thm_REAL_MUL_LINV.
  unfold one, zero. simpl. rewrite eq_real_struct, thm_REAL_OF_NUM_EQ. auto.
Qed.

Definition real_model : model := {|
  model_structure := real_struct;
  model_axioms := real_axioms;
|}.

Lemma eq_real_model:
  @eq (model_structure real_model) = @Logic.eq (val (model_structure real_model)).
Proof. exact eq_real_struct. Qed.

Require Import fourcolor.reals.realcategorical.

Definition R_of_real := @Rmorph_to real_model R_model.
Definition real_of_R := @Rmorph_to R_model real_model.

Lemma R_of_real_of_R r : R_of_real (real_of_R r) = r.
Proof. rewrite <- eq_R_model. apply (@Rmorph_to_inv R_model real_model). Qed.

Lemma real_of_R_of_real r : real_of_R (R_of_real r) = r.
Proof. rewrite <- eq_real_model. apply (@Rmorph_to_inv real_model R_model). Qed.

(*****************************************************************************)
(* Mapping of HOL-Light reals to Coq reals. *)
(*****************************************************************************)

Definition mk_real : ((prod hreal hreal) -> Prop) -> R := fun x => R_of_real (mk_real x).

Definition dest_real : R -> (prod hreal hreal) -> Prop := fun x => dest_real (real_of_R x).

Lemma axiom_23 : forall (a : R), (mk_real (dest_real a)) = a.
Proof. intro a. unfold mk_real, dest_real. rewrite axiom_23. apply R_of_real_of_R. Qed.

Lemma axiom_24_aux : forall r, (exists x, r = treal_eq x) -> dest_real (mk_real r) = r.
Proof.
  intros c [x h]. unfold dest_real, mk_real.
  rewrite real_of_R_of_real, <- axiom_24.
  exists x. exact h.
Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof.
  intro c. unfold dest_real, mk_real. rewrite real_of_R_of_real, <- axiom_24.
  reflexivity.  
Qed.

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
  symmetry. apply thm_REAL_INV_0.
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

Lemma INR_eq n : INR (S n) = (INR n + 1)%R.
Proof.
  induction n; simpl.
  rewrite Rplus_0_l. reflexivity.
  destruct n as [|n]. reflexivity. reflexivity.
Qed.

Require Import Lia.

Lemma real_of_num_def : INR = (fun m : nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).
Proof.
  change (INR = fun m : nat => R_of_real (real_of_num m)).  
  apply fun_ext. induction x.
  apply zero_eq.
  rewrite INR_eq, IHx. rewrite add_eq, real_of_R_of_real, one_morph_R.
  rewrite <- real_add_of_num. f_equal. f_equal. lia.
Qed.

Fixpoint Rpower_nat r n : R :=
  match n with
  | 0 => 1
  | S n => r * Rpower_nat r n
  end.

Lemma real_pow_def : Rpower_nat = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R) (fun real_pow' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R => forall _24085 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : R, (real_pow' _24085 x (NUMERAL 0)) = (INR (NUMERAL (BIT1 0)))) /\ (forall x : R, forall n : nat, (real_pow' _24085 x (S n)) = (Rmult x (real_pow' _24085 x n)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))).
Proof.
  generalize (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))); generalize (@prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Rpower_nat). split; simpl; intro x; reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction y; simpl. rewrite h0. reflexivity. rewrite hs, IHy. reflexivity.
Qed.

Require Import RIneq.

Open Scope R_scope.

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

(*****************************************************************************)
(* Mapping of integers. *)
(*****************************************************************************)

Definition Z' := {| type := Z; el := 0%Z |}.
Canonical Z'.

Definition int_of_real r := Z.pred (up r).

Lemma axiom_25 : forall (a : Z), (int_of_real (IZR a)) = a.
Proof.
  intro k. unfold int_of_real. generalize (archimed (IZR k)).
  generalize (up (IZR k)); intros l [h1 h2].
  apply lt_IZR in h1. rewrite <- minus_IZR in h2. apply le_IZR in h2. lia.  
Qed.

Definition integer : R -> Prop := fun _28588 : R => exists n : nat, (Rabs _28588) = (INR n).

Lemma integer_IZR r : integer r -> exists k, r = IZR k.
Proof.
  intros [n h]. rewrite INR_IZR_INZ in h.
  unfold Rabs in h. destruct (Rcase_abs r) in h.
  exists (- (Z.of_nat n))%Z. rewrite opp_IZR, <- h, Ropp_involutive. reflexivity.
  exists (Z.of_nat n). exact h.
Qed.

Lemma IZR_integer r : (exists k, r = IZR k) -> integer r.
Proof.
  intros [k h]. rewrite h. exists (Z.abs_nat k). rewrite Rabs_Zabs, INR_IZR_INZ.
  f_equal. rewrite Nat2Z.inj_abs_nat. reflexivity.
Qed.

Lemma axiom_26 : forall (r : R), ((fun x : R => integer x) r) = ((IZR (int_of_real r)) = r).
Proof.
  intro r. apply prop_ext; intro h.
  apply integer_IZR in h. destruct h as [k h]. subst r. apply f_equal.
  apply axiom_25.
  apply IZR_integer. exists (int_of_real r). symmetry. exact h.
Qed.

Close Scope R_scope.

(*****************************************************************************)
(* Sets. *)
(*****************************************************************************)

Definition IN {A : Type'} : A -> (A -> Prop) -> Prop := fun _32683 : A => fun _32684 : A -> Prop => _32684 _32683.

Definition EMPTY {A : Type'} : A -> Prop := fun x : A => False.

Definition INSERT {A : Type'} : A -> (A -> Prop) -> A -> Prop := fun _32739 : A => fun _32740 : A -> Prop => fun y : A => (@IN A y _32740) \/ (y = _32739).

Definition UNIV (A : Type') : A -> Prop := fun x : A => True.

Lemma UNIV_eq_INSERT A : UNIV A = INSERT (el A) (fun x => x <> el A).
Proof.
  apply fun_ext; intro x. unfold INSERT. apply prop_ext; intro h.
  2: exact Logic.I.
  destruct (classic (x = el A)) as [i|i]. right. exact i. left. exact i.
Qed.

Lemma IN_el_not_el A: IN (el A) (fun x => x <> el A) = False.
Proof. rewrite is_False. intro h. apply h. reflexivity. Qed.

Definition Incl {A:Type'} (s s': A -> Prop) := forall x, IN x s -> IN x s'.

Lemma IN_set_eq_INSERT {A:Type'} (a:A) s:
  IN a s -> s = INSERT a (fun x => IN x s /\ x <> a).
Proof.
  intro h. apply fun_ext; intro x. apply prop_ext; unfold INSERT, IN; intro i.
  destruct (classic (x = a)) as [j|j]; auto.
  destruct i as [[i j]|i]. exact i. subst x. exact h.
Qed.

(*****************************************************************************)
(* Finite sets. *)
(*****************************************************************************)

Definition FINITE {A : Type'} : (A -> Prop) -> Prop := fun a : A -> Prop => forall FINITE' : (A -> Prop) -> Prop, (forall a' : A -> Prop, ((a' = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a' = (@INSERT A x s)) /\ (FINITE' s))) -> FINITE' a') -> FINITE' a.

Inductive finite {A : Type'} : (A -> Prop) -> Prop :=
  finite_EMPTY: finite EMPTY
| finite_INSERT a s : finite s -> finite (INSERT a s).

Lemma FINITE_eq_finite (A:Type') (s:A -> Prop) : FINITE s = finite s.
Proof.
  apply prop_ext; intro h.

  apply h. intros P [i|[x [s' [i j]]]]; rewrite i.
  apply finite_EMPTY.
  apply finite_INSERT. exact j.
  
  induction h; intros P H; apply H.
  left. reflexivity.
  right. exists a. exists s. split. reflexivity. apply IHh. exact H.  
Qed.

Require Import List.

Lemma finite_list_NoDup {A:Type'} (s:A -> Prop):
  finite s = (exists l, NoDup l /\ s = fun x => In x l).
Proof.
  apply prop_ext; intro H.

  induction H.
  exists nil. split.
    apply NoDup_nil.
    apply fun_ext; intro x. apply prop_ext; intro h; contradiction.
  destruct IHfinite as [l [n e]]. subst s. destruct (classic (In a l)).
    exists l. split. exact n. apply fun_ext; intro x. unfold INSERT.
      apply prop_ext; intro h.
      destruct h as [h|h]. exact h. subst x. exact H0. left. exact h.
    exists (cons a l). split. apply NoDup_cons. exact H0. exact n.
      apply fun_ext; intro x. unfold INSERT. apply prop_ext; simpl; intro h.
      destruct h as [h|h]. right. exact h. left. symmetry; exact h.
      destruct h as [h|h]. right. symmetry; exact h. left. exact h.

  destruct H as [l e]. generalize e; clear e. generalize s; clear s.
  induction l; intros s [n e].
  subst s. apply finite_EMPTY.
  set (s' := fun x => In x l). assert (j: s = INSERT a s').
  apply fun_ext; intro x. rewrite e. unfold INSERT. simpl.
  apply prop_ext; intro h; firstorder.
  rewrite j. apply finite_INSERT. apply IHl. split.
  inversion n. assumption. reflexivity.
Qed.

Definition elements {A:Type'} (s:A -> Prop) := ε (fun l => NoDup l /\ s = fun x => In x l).

Lemma elements_spec {A:Type'} {s:A -> Prop} (h:finite s):
  NoDup (elements s) /\ s = fun x => In x (elements s).
Proof.
  unfold elements.
  match goal with [|- _ (ε ?x) /\ _] => set (Q := x) end.
  assert (i: exists l, Q l). rewrite finite_list_NoDup in h.
  destruct h as [l h]. exists l. exact h.
  generalize (ε_spec i). firstorder.
Qed.

Lemma In_elements {A:Type'} {s: A -> Prop} : finite s -> forall x, In x (elements s) = IN x s.
Proof.
  intro h. generalize (elements_spec h); intros [n e] x. rewrite e at 2.
  reflexivity.
Qed.

Lemma elements_EMPTY (A:Type') : elements (@EMPTY A) = nil.
Proof.
  generalize (elements_spec (@finite_EMPTY A)). intros [n e].
  destruct (elements EMPTY). reflexivity.
  apply False_rec. apply ext_fun with (x:=t) in e. unfold EMPTY in e.
  rewrite e. simpl. left. reflexivity.
Qed.

Require Import Permutation.

Lemma eq_mod_permut A (l: list A):
  forall l', (forall x, In x l = In x l') -> NoDup l -> NoDup l' -> Permutation l l'.
Proof.
  induction l; destruct l'.

  intros. apply perm_nil.

  intro e. generalize (e a). simpl. intro h. symmetry in h.
  apply False_rec. rewrite <- h. left. reflexivity.

  intro e. generalize (e a). simpl. intro h.
  apply False_rec. rewrite <- h. left. reflexivity.

  intros e n n'. inversion n; inversion n'; subst.
  destruct (classic (a = a0)).

  (* case a = a0 *)
  subst a0. apply perm_skip. apply IHl.

  intro x. apply prop_ext; intro h.
  assert (i: In x (a::l)). right. exact h.
  rewrite e in i. destruct i. subst x. contradiction. exact H.
  assert (i: In x (a::l')). right. exact h.
  rewrite <- e in i. destruct i. subst x. contradiction. exact H.
  assumption.
  assumption.

  (* case a <> a0 *)
  assert (i: In a (a0 :: l')). rewrite <- (e a). left. reflexivity.
  apply in_split in i. destruct i as [l1 [l2 i]]. rewrite i.
  rewrite <- Permutation_middle. apply perm_skip. apply IHl.
  2: assumption.
  2: apply NoDup_remove_1 with a; rewrite <- i; apply NoDup_cons; assumption.

  intro x. apply prop_ext; intro h.
  
  assert (j: In x (a::l)). right. exact h.
  rewrite e, i in j. apply in_elt_inv in j. destruct j as [j|j].
  subst x. contradiction. exact j.

  assert (j: In x (l1 ++ a :: l2)). apply in_or_app. apply in_app_or in h.
    destruct h as [h|h]. left. exact h. right. right. exact h.
  rewrite <- i, <- e in j. destruct j as [j|j].
  subst x. rewrite i in n'. apply NoDup_remove in n'. destruct n' as [h1 h2].
  contradiction. exact j.
Qed.

Lemma elements_INSERT {A:Type'} (a:A) {s} :
  finite s -> exists l', Permutation l' (a :: elements s) /\
                     elements (INSERT a s) = COND (IN a s) (elements s) l'.
Proof.
  intro h. assert (h': finite (INSERT a s)). apply finite_INSERT. exact h.
  destruct (prop_degen (IN a s)) as [e|e]; rewrite e.

  exists (a :: elements s). split. reflexivity.
  rewrite COND_True. f_equal. apply fun_ext; intro x.
  apply prop_ext; firstorder. subst x. rewrite is_True in e. exact e.
  exists (elements (INSERT a s)). split. 2: rewrite COND_False; reflexivity.

  apply eq_mod_permut. intro x. rewrite (In_elements h').
  unfold IN, INSERT, IN. simpl.
  apply prop_ext; intros [i|i]. right. rewrite (In_elements h). exact i.
  subst x. left. reflexivity. subst x. right. reflexivity.
  rewrite (In_elements h) in i. left. exact i.
  
  generalize (elements_spec h'); intros [n i]. exact n.
  apply NoDup_cons. rewrite (In_elements h), <- is_False. exact e.
  generalize (elements_spec h); intros [n i]. exact n.
Qed.

Definition permut_inv {A B:Type} (f:A -> B -> A) :=
  forall a y x, f (f a y) x = f (f a x) y.

Lemma eq_fold_left_permut {A B} {f:A -> B -> A}: permut_inv f ->
  forall l l', Permutation l l' -> forall a, fold_left f l a = fold_left f l' a.
Proof.
  intro H. induction 1; intro a; simpl.
  reflexivity.  
  apply IHPermutation. rewrite H. reflexivity.
  transitivity (fold_left f l' a). apply IHPermutation1. apply IHPermutation2.
Qed.

Lemma fold_left_eq_permut {A B} {f:A -> B -> A}: permut_inv f ->
  forall l a b, fold_left f l (f a b) = f (fold_left f l a) b.
Proof.
  intro H. induction l as [|x l]; intros a b; simpl.
  reflexivity.
  rewrite <- IHl. f_equal. apply H.
Qed.

Definition ITSET {A B : Type'} : (B -> A -> A) -> (B -> Prop) -> A -> A := fun f : B -> A -> A => fun s : B -> Prop => fun a : A => @ε ((B -> Prop) -> A) (fun g : (B -> Prop) -> A => ((g (@EMPTY B)) = a) /\ (forall x : B, forall s : B -> Prop, (@FINITE B s) -> (g (@INSERT B x s)) = (@COND A (@IN B x s) (g s) (f x (g s))))) s.

Definition itset {A B:Type'} : (B -> A -> A) -> (B -> Prop) -> A -> A := fun f : B -> A -> A => let F := fun a b => f b a in fun s : B -> Prop => fun a : A => fold_left F (elements s) a.

Lemma itset_EMPTY {A B:Type'} (f:B -> A -> A) a: itset f EMPTY a = a.
Proof.
  unfold itset. rewrite elements_EMPTY. simpl. reflexivity.  
Qed.

Definition permut_inv' {A B:Type} (f:B -> A -> A) :=
  forall a y x, f x (f y a) = f y (f x a).

Lemma itset_INSERT {A B:Type'} (f:B -> A -> A) a b s: permut_inv' f -> finite s ->
  itset f (INSERT b s) a = COND (IN b s) (itset f s a) (f b (itset f s a)).
Proof.
  intros H h. unfold itset. set (F := fun a b => f b a).
  assert (H': permut_inv F). exact H.
  destruct (elements_INSERT b h) as [l [p e]]. rewrite e.
  destruct (prop_degen (IN b s)) as [i|i]; rewrite i.
  rewrite !COND_True. reflexivity.
  rewrite !COND_False. transitivity (fold_left F (b :: elements s) a).
  apply (eq_fold_left_permut H). exact p.
  apply (fold_left_eq_permut H').
Qed.

Lemma exists_ITSET {A B:Type'} {f:B -> A -> A}: permut_inv' f ->
  forall a, let g := fun s => itset f s a in
      g EMPTY = a /\
        (forall (x : B) (s : B -> Prop),
            FINITE s -> g (INSERT x s) = COND (IN x s) (g s) (f x (g s))).
Proof.
  intros H a g. unfold g. split. apply itset_EMPTY. intros b s h.
  apply itset_INSERT. exact H. rewrite <- FINITE_eq_finite. exact h.
Qed.

Lemma ITSET_eq_itset (A B:Type') (f:B -> A -> A):
  permut_inv' f -> forall s, finite s -> forall a, ITSET f s a = itset f s a.
Proof.
  intros H s h a.
  unfold ITSET. match goal with [|- ε ?x _ = _] => set (Q := x) end.
  assert (i: exists g, Q g). exists (fun s => itset f s a). apply exists_ITSET. exact H.
  generalize (ε_spec i). intros [j k]. generalize s h. induction 1. 
  rewrite itset_EMPTY. exact j.
  rewrite k. unfold reverse_coercion in IHh0. rewrite IHh0, itset_INSERT.
  reflexivity. exact H. exact h0. rewrite FINITE_eq_finite. exact h0.
Qed.

Definition CARD {_99571 : Type'} : (_99571 -> Prop) -> nat := fun _44539 : _99571 -> Prop => @ITSET nat _99571 (fun x : _99571 => fun n : nat => S n) _44539 (NUMERAL 0).

Definition dimindex {A : Type'} : (A -> Prop) -> nat := fun _97595 : A -> Prop => @COND nat (@FINITE A (UNIV A)) (@CARD A (UNIV A)) (NUMERAL (BIT1 0)).

Lemma Incl_finite {A:Type'} (s: A -> Prop) : finite s -> forall s', Incl s' s -> finite s'.
Proof.
  induction 1.

  intros s i. assert (e: s = EMPTY). apply fun_ext; intro x.
    unfold EMPTY. rewrite is_False. intro h. apply (i x). exact h.
  rewrite e. apply finite_EMPTY.

  intros s' i. destruct (classic (Incl s' s)) as [h|h].
  apply IHfinite. exact h.
  
  assert (j: IN a s'). unfold Incl in h. rewrite not_forall_eq in h.
  destruct h as [x h]. rewrite imp_eq_disj, not_disj_eq in h.
  destruct h as [h1 h2]. apply NNPP in h1. generalize (i x h1).
  intros [j|j]. contradiction. subst x. exact h1.

  apply IN_set_eq_INSERT in j. rewrite j. apply finite_INSERT.
  apply IHfinite. intros x [h1 h2]. generalize (i x h1). intros [k|k].
  exact k. contradiction.
Qed.

Lemma dimindex_UNIV_gt_0 A : 0 < dimindex (UNIV A).
Proof.
  assert (p1: permut_inv' (fun (_ : A) (n : nat) => S n)).
  unfold permut_inv'. reflexivity.
  
  unfold dimindex. case (prop_degen (FINITE (UNIV A))); intro h; rewrite h.
  
  assert (p2: finite (UNIV A)). rewrite <- FINITE_eq_finite, h. exact Logic.I.
  assert (p3: finite (fun x : A => x <> el A)). apply (Incl_finite (UNIV A)). exact p2.
  intros x _. exact Logic.I.

  rewrite COND_True. unfold CARD.
  rewrite ITSET_eq_itset, UNIV_eq_INSERT, itset_INSERT, IN_el_not_el, COND_False; auto.
  lia.

  rewrite COND_False. unfold NUMERAL, BIT1. lia.
Qed.

(*****************************************************************************)
(* Cart.finite_image: natural numbers between 1 and the cardinal of A,
if A is finite, and 1 otherwise. *)
(*****************************************************************************)

Definition GSPEC {A : Type'} : (A -> Prop) -> A -> Prop := fun _32695 : A -> Prop => _32695.

Definition SETSPEC {_83031 : Type'} : _83031 -> Prop -> _83031 -> Prop := fun _32700 : _83031 => fun _32701 : Prop => fun _32702 : _83031 => _32701 /\ (_32700 = _32702).

Definition dotdot : nat -> nat -> nat -> Prop := fun _69692 : nat => fun _69693 : nat => @GSPEC nat (fun GEN_PVAR_229 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_229 ((Peano.le _69692 x) /\ (Peano.le x _69693)) x).

Definition finite_image_pred (A:Type') x :=
  @IN nat x (dotdot (NUMERAL (BIT1 0)) (@dimindex A (UNIV A))).

Lemma finite_image_pred1 (A:Type') : finite_image_pred A 1.
Proof.
  unfold finite_image_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A). lia.
Qed.

Definition finite_image : Type' -> Type' :=
  fun A => subtype (finite_image_pred1 A).

Definition finite_index : forall {A : Type'}, nat -> finite_image A :=
  fun A => mk (finite_image_pred1 A).

Definition dest_finite_image : forall {A : Type'}, (finite_image A) -> nat :=
  fun A => dest (finite_image_pred1 A).

Lemma axiom_27 : forall {A : Type'} (a : finite_image A), (@finite_index A (@dest_finite_image A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_28 : forall {A : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@dimindex A (UNIV A)))) r) = ((@dest_finite_image A (@finite_index A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Cart.cart A B is finite_image B -> A. *)
(*****************************************************************************)

Definition cart A B := finite_image B -> A.

Definition mk_cart : forall {A B : Type'}, ((finite_image B) -> A) -> cart A B :=
  fun A B f => f.

Definition dest_cart : forall {A B : Type'}, (cart A B) -> (finite_image B) -> A :=
  fun A B f => f.

Lemma axiom_29 : forall {A B : Type'} (a : cart A B), (@mk_cart A B (@dest_cart A B a)) = a.
Proof. reflexivity. Qed.

Lemma axiom_30 : forall {A B : Type'} (r : (finite_image B) -> A), ((fun f : (finite_image B) -> A => True) r) = ((@dest_cart A B (@mk_cart A B r)) = r).
Proof. intros A B r. apply prop_ext; intros _. reflexivity. exact Logic.I. Qed.

(*****************************************************************************)
(* Cart.finite_sum *)
(*****************************************************************************)

Definition finite_sum_pred (A B: Type') x := @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B)))).

Lemma finite_sum_pred1 (A B:Type') : finite_sum_pred A B 1.
Proof.
  unfold finite_sum_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A) (dimindex_UNIV_gt_0 B). lia.
Qed.

Definition finite_sum : Type' -> Type' -> Type' :=
  fun A B => subtype (finite_sum_pred1 A B).

Definition mk_finite_sum : forall {A B : Type'}, nat -> finite_sum A B :=
  fun A B => mk (finite_sum_pred1 A B).

Definition dest_finite_sum : forall {A B : Type'}, (finite_sum A B) -> nat :=
  fun A B => dest (finite_sum_pred1 A B).

Lemma axiom_31 : forall {A B : Type'} (a : finite_sum A B), (@mk_finite_sum A B (@dest_finite_sum A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_32 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B))))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Cart.finite_diff *)
(*****************************************************************************)

Definition finite_diff_pred (A B: Type') x := @IN nat x (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (Nat.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 0)))).

Lemma finite_diff_pred1 (A B:Type') : finite_diff_pred A B 1.
Proof.
  unfold finite_diff_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A) (dimindex_UNIV_gt_0 B); intros.
  case (prop_degen (dimindex (UNIV B) < dimindex (UNIV A))); intro h; rewrite h.
  rewrite COND_True. rewrite is_True in h. lia.
  rewrite COND_False. rewrite is_False in h. lia.
Qed.

Definition finite_diff : Type' -> Type' -> Type' :=
  fun A B => subtype (finite_diff_pred1 A B).

Definition mk_finite_diff : forall {A B : Type'}, nat -> finite_diff A B :=
  fun A B => mk (finite_diff_pred1 A B).

Definition dest_finite_diff : forall {A B : Type'}, (finite_diff A B) -> nat :=
  fun A B => dest (finite_diff_pred1 A B).

Lemma axiom_33 : forall {A B : Type'} (a : finite_diff A B), (@mk_finite_diff A B (@dest_finite_diff A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_34 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (Nat.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Cart.finite_prod *)
(*****************************************************************************)

Definition finite_prod_pred (A B: Type') x := @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B)))).

Lemma finite_prod_pred1 (A B:Type') : finite_prod_pred A B 1.
Proof.
  unfold finite_prod_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A) (dimindex_UNIV_gt_0 B); intros. lia.
Qed.

Definition finite_prod : Type' -> Type' -> Type' :=
  fun A B => subtype (finite_prod_pred1 A B).

Definition mk_finite_prod : forall {A B : Type'}, nat -> finite_prod A B :=
  fun A B => mk (finite_prod_pred1 A B).

Definition dest_finite_prod : forall {A B : Type'}, (finite_prod A B) -> nat :=
  fun A B => dest (finite_prod_pred1 A B).

Lemma axiom_35 : forall {A B : Type'} (a : finite_prod A B), (@mk_finite_prod A B (@dest_finite_prod A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_36 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Mapping of a subtype of recspace (non-recursive inductive type definition) *)
(*****************************************************************************)

Section non_recursive_inductive_type.

  Variable A : Type'.
  
  Definition nr_constr (a:A) : recspace A := CONSTR 0 a (fun n => BOTTOM).

  Definition nr_pred (r : recspace A) := exists a, r = nr_constr a.

  Lemma nr_pred1 : nr_pred (nr_constr (el A)).
  Proof. exists (el A). reflexivity. Qed.

  Definition nr_type := @subtype (recspace A) _ _ nr_pred1.

  Definition nr_mk : recspace A -> nr_type := @mk (recspace A) _ _ nr_pred1.

  Definition nr_dest : nr_type -> recspace A := @dest (recspace A) _ _ nr_pred1.

  Lemma nr_mk_dest : forall a : nr_type, (nr_mk (nr_dest a)) = a.
  Proof. intro a. apply mk_dest. Qed.

  Lemma nr_dest_mk : forall r : recspace A, (forall P : recspace A -> Prop, (forall r' : recspace A, nr_pred r' -> P r') -> P r) = (nr_dest (nr_mk r) = r).
  Proof.
    intro r. apply prop_ext; intro h.
    unfold nr_dest, nr_mk. rewrite <- dest_mk.
    apply h. intros r' [a H]. exists a. exact H.
    intros P H. apply H. rewrite <- h. destruct (nr_mk r) as [r' [a h']].
    exists a. unfold nr_dest, dest. simpl. exact h'.
  Qed.

End non_recursive_inductive_type.

(*****************************************************************************)
(* Cart.tybit0 *)
(*****************************************************************************)

Definition tybit0 A := nr_type (finite_sum A A).

Definition _mk_tybit0 : forall {A : Type'}, (recspace (finite_sum A A)) -> tybit0 A := fun A => nr_mk (finite_sum A A).

Definition _dest_tybit0 : forall {A : Type'}, (tybit0 A) -> recspace (finite_sum A A) := fun A => nr_dest (finite_sum A A).

Lemma axiom_37 : forall {A : Type'} (a : tybit0 A), (@_mk_tybit0 A (@_dest_tybit0 A a)) = a.
Proof. intro A. apply nr_mk_dest. Qed.

Lemma axiom_38 : forall {A : Type'} (r : recspace (finite_sum A A)), ((fun a : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a''' (fun n : nat => @BOTTOM (finite_sum A A))) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A (@_mk_tybit0 A r)) = r).
Proof. intro A. apply nr_dest_mk. Qed.

(*****************************************************************************)
(* Cart.tybit1 *)
(*****************************************************************************)

Definition tybit1 A := nr_type (finite_sum (finite_sum A A) unit).

Definition _mk_tybit1 : forall {A : Type'}, (recspace (finite_sum (finite_sum A A) unit)) -> tybit1 A := fun A => nr_mk (finite_sum (finite_sum A A) unit).

Definition _dest_tybit1 : forall {A : Type'}, (tybit1 A) -> recspace (finite_sum (finite_sum A A) unit) := fun A => nr_dest (finite_sum (finite_sum A A) unit).

Lemma axiom_39 : forall {A : Type'} (a : tybit1 A), (@_mk_tybit1 A (@_dest_tybit1 A a)) = a.
Proof. intro A. apply nr_mk_dest. Qed.

Lemma axiom_40 : forall {A : Type'} (r : recspace (finite_sum (finite_sum A A) unit)), ((fun a : recspace (finite_sum (finite_sum A A) unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) unit), (exists a'' : finite_sum (finite_sum A A) unit, a' = ((fun a''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a''' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A (@_mk_tybit1 A r)) = r).
Proof. intro A. apply nr_dest_mk. Qed.
