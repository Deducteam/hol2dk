Require Import HOLLight_Real_With_N.mappings.

(*****************************************************************************)
(* Proof that Coq R is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Require Import Coq.Reals.Reals.

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

(*****************************************************************************)
(* Proof that real is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Require Import HOLLight_Real_With_N.terms.

Lemma real_add_of_num p q :
  real_of_num (p + q)%N = real_add (real_of_num p) (real_of_num q).
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

Require Import HOLLight_Real_With_N.theorems.

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

Require Import Coq.micromega.Lia.

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
  unfold one, zero. simpl. rewrite eq_real_struct, thm_REAL_OF_NUM_EQ. lia.
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

Lemma R_of_real_morph : morphism R_of_real.
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
  change (@Logic.eq (type real) (real_of_num 0) (real_inv (real_of_num 0))).
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

Definition R_of_N n :=
  match n with
  | N0 => 0
  | N.pos p => IPR p
  end.

Require Import Coq.micromega.Lra.

Lemma R_of_N_succ n : R_of_N (N.succ n) = R_of_N n + 1.
Proof.
  destruct n; simpl. unfold IPR. lra. rewrite Rplus_comm. apply succ_IPR.
Qed.

Lemma R_of_N_add p q : R_of_N (p + q)%N = R_of_N p + R_of_N q.
Proof.
  destruct p; destruct q; simpl. lra. unfold IPR. lra. unfold IPR. lra.
  apply plus_IPR.
Qed.

Lemma Npos_succ p : N.pos (Pos.succ p) = (N.pos p + 1)%N.
Proof. lia. Qed.

Lemma treal_eq_of_num_add m n :
  treal_eq (treal_of_num (m + n))
  = treal_eq (treal_add (treal_of_num m) (treal_of_num n)).
Proof.
  apply eq_class_intro. apply treal_eq_sym. apply treal_eq_trans.
  symmetry. apply thm_TREAL_OF_NUM_ADD.
Qed.

Lemma mk_real_treal_eq_add p q :
  mk_real (treal_eq (treal_add (treal_of_num p) (treal_of_num q)))
  = (mk_real (treal_eq (treal_of_num p)) + mk_real (treal_eq (treal_of_num q)))%R.
Proof.
  rewrite add_eq. unfold mk_real. f_equal. rewrite !real_of_R_of_real.
  rewrite <- treal_eq_of_num_add.
  change (real_of_num (p + q) = add (real_of_num p) (real_of_num q)).
  rewrite real_add_of_num. reflexivity.
Qed.

Lemma IPR_eq_mk_real p : IPR p = mk_real (treal_eq (treal_of_num (N.pos p))).
Proof.
  pattern p; revert p; apply Pos.peano_ind.
  apply one_eq.
  intros p hp. rewrite succ_IPR, Rplus_comm.
  assert (e: IPR 1 = mk_real (treal_eq (treal_of_num 1))). apply one_eq.
  rewrite hp, e, Npos_succ, <- mk_real_treal_eq_add, <- treal_eq_of_num_add.
  reflexivity.
Qed.

Lemma real_of_num_def : R_of_N = (fun m : N => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).
Proof.
  apply fun_ext; intro n.
  change (R_of_N n = mk_real (treal_eq (treal_of_num n))).
  destruct n; simpl. apply zero_eq. apply IPR_eq_mk_real.
Qed.

Lemma R_of_N0 : R_of_N 0 = 0%R.
Proof. reflexivity. Qed.

Lemma R_of_N1 : R_of_N 1 = 1%R.
Proof. reflexivity. Qed.

Lemma Rnot_le x y : (~ x <= y) = (x > y).
Proof.
  apply prop_ext; intro h.
  apply Rnot_le_gt. exact h.
  apply Rgt_not_le. exact h.
Qed.

Lemma real_abs_def :
  Rabs = (fun y0 : R => @COND R (Rle (R_of_N (NUMERAL 0)) y0) y0 (Ropp y0)).
Proof.
  apply fun_ext; intro r. unfold Rabs. destruct (Rcase_abs r).
  assert (h: (R_of_N (NUMERAL 0) <= r) = False). rewrite is_False, Rnot_le.
  unfold NUMERAL. rewrite R_of_N0. exact r0.
  rewrite h, COND_False. reflexivity.
  assert (h: (R_of_N (NUMERAL 0) <= r) = True). rewrite is_True. apply Rge_le.
  unfold NUMERAL. rewrite R_of_N0. exact r0.
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

Definition Rpow (r : R) n : R := powerRZ r (Z.of_N n).

Lemma real_pow_def : Rpow = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R) (fun real_pow' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R => forall _24085 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : R, (real_pow' _24085 x (NUMERAL 0%N)) = (R_of_N (NUMERAL (BIT1 0%N)))) /\ (forall x : R, forall n : N, (real_pow' _24085 x (N.succ n)) = (Rmult x (real_pow' _24085 x n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0%N)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))))))))))).
Proof.
  cbn.
  align_ε.
  { cbn. split. 1: reflexivity.
    intros x n.
    unfold Rpow. rewrite <- !N_nat_Z.
    rewrite <- !Rfunctions.pow_powerRZ.
    rewrite Nnat.N2Nat.inj_succ. reflexivity.
  }
  cbn. intros pow' [h0 hS].
  ext r n.
  rewrite <- (Nnat.N2Nat.id n).
  unfold Rpow. rewrite nat_N_Z.
  generalize (N.to_nat n) as m. clear n. intro n.
  rewrite <- Rfunctions.pow_powerRZ.
  induction n as [| n ih].
  - cbn. rewrite h0. reflexivity.
  - rewrite Nnat.Nat2N.inj_succ. cbn.
    rewrite hS. rewrite ih.
    reflexivity.
Qed.

Definition Rsgn r := r / Rabs r.

Lemma Rsgn_0 : Rsgn 0 = 0.
Proof. unfold Rsgn. lra. Qed.

Lemma Rsgn_pos r : r > 0 -> Rsgn r = 1.
Proof.
  intro h.
  unfold Rsgn.
  rewrite Rabs_pos_eq. 2: lra.
  rewrite Rdiv_diag. 2: lra.
  reflexivity.
Qed.

Lemma Rsgn_neg r : r < 0 -> Rsgn r = -1.
Proof.
  intro h.
  unfold Rsgn.
  rewrite Rabs_left. 2: assumption.
  rewrite Rdiv_opp_r.
  rewrite Rdiv_diag. 2: lra.
  reflexivity.
Qed.

Lemma real_sgn_def : Rsgn = (fun _26598 : R => @COND R (Rlt (R_of_N (NUMERAL 0%N)) _26598) (R_of_N (NUMERAL (BIT1 0%N))) (@COND R (Rlt _26598 (R_of_N (NUMERAL 0%N))) (Ropp (R_of_N (NUMERAL (BIT1 0%N)))) (R_of_N (NUMERAL 0%N)))).
Proof.
  unfold Rsgn.
  ext r. cbn.
  rewrite thm_COND_ELIM_THM. split.
  - apply Rsgn_pos.
  - intro h. rewrite thm_COND_ELIM_THM. split.
    + apply Rsgn_neg.
    + intro h'. assert (r = 0) as -> by lra.
      lra.
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

Definition integer : R -> Prop := fun _28588 : R => exists n : N, (Rabs _28588) = (R_of_N n).

Lemma integer_def : integer = (fun _28715 : R => exists n : N, (Rabs _28715) = (R_of_N n)).
Proof. reflexivity. Qed.

Lemma minus_eq_minus x y : -x = y -> x = - y.
Proof. intro e. subst y. symmetry. apply Ropp_involutive. Qed.

Lemma integer_IZR r : integer r -> exists k, r = IZR k.
Proof.
  intros [n h]. destruct (Rcase_abs r) as [i|i].

  rewrite (Rabs_left _ i) in h. apply minus_eq_minus in h. subst r. clear i.
  pattern n; revert n; apply N.peano_ind.
  exists 0%Z. rewrite R_of_N0. ring.
  intros n [k hk]. rewrite R_of_N_succ.
  exists (k - 1)%Z. rewrite minus_IZR, <- hk. ring.

  rewrite (Rabs_right _ i) in h. subst r. clear i.
  pattern n; revert n; apply N.peano_ind.
  exists 0%Z. rewrite R_of_N0. reflexivity.
  intros n [k hk]. rewrite R_of_N_succ.
  exists (k + 1)%Z. rewrite plus_IZR, <- hk. reflexivity.
Qed.

Definition Zabs (z:Z): N :=
  match z with
  | Z0 => N0
  | Zpos p => N.pos p
  | Zneg p => N.pos p
  end.

Lemma pos_succ p : N.pos (Pos.succ p) = N.succ (N.pos p).
Proof. induction p; simpl; reflexivity. Qed.

Lemma IZR_pos_eq_R_of_N_pos p: IZR (Z.pos p) = R_of_N (N.pos p).
Proof.
  pattern p; revert p; apply Pos.peano_ind.
  rewrite R_of_N1. reflexivity.
  intros p hp. rewrite Pos2Z.inj_succ, succ_IZR, pos_succ, R_of_N_succ, hp.
  reflexivity.
Qed.

Lemma IZR_integer r : (exists k, r = IZR k) -> integer r.
Proof.
  intros [k h]. subst r. exists (Zabs k). rewrite <- abs_IZR. destruct k; simpl.
  rewrite <- R_of_N0. reflexivity. apply IZR_pos_eq_R_of_N_pos.
  apply IZR_pos_eq_R_of_N_pos.
Qed.

Lemma axiom_26 : forall (r : R), ((fun x : R => integer x) r) = ((IZR (int_of_real r)) = r).
Proof.
  intro r. apply prop_ext; intro h.
  apply integer_IZR in h. destruct h as [k h]. subst r. apply f_equal.
  apply axiom_25.
  apply IZR_integer. exists (int_of_real r). symmetry. exact h.
Qed.

Definition Z_of_N (n:N): Z :=
  match n with
  | N0 => Z0
  | N.pos p => Z.pos p
  end.

Lemma Z_of_N_succ n : Z_of_N (N.succ n) = (Z_of_N n + 1)%Z.
Proof.
  destruct n. reflexivity.
  pattern p; revert p; apply Pos.peano_ind.
  reflexivity.
  intro p. simpl. lia.
Qed.

Require Import Coq.Reals.R_Ifp.

Lemma up_IZR z : up (IZR z) = (z + 1)%Z.
Proof. symmetry; apply tech_up; rewrite plus_IZR; lra.
Qed.

Lemma up_shiftz r z : up (r + IZR z)%R = (up r + z)%Z.
Proof. assert (H := archimed r). symmetry; apply tech_up; rewrite plus_IZR; lra. Qed.

Lemma up0 : up 0 = 1%Z.
Proof. apply up_IZR. Qed.

Lemma up_succ r : up (r + 1) = (up r + 1)%Z.
Proof. apply up_shiftz. Qed.

Lemma int_of_num_def : Z_of_N = (fun _28789 : N => int_of_real (R_of_N _28789)).
Proof.
  apply fun_ext; intro n; pattern n; revert n; apply N.peano_ind; unfold int_of_real.
  rewrite R_of_N0, up0. reflexivity.
  intro n. unfold int_of_real. rewrite Z_of_N_succ, R_of_N_succ, up_succ. lia.
Qed.

Lemma int_le_def :
  Z.le = (fun _28741 : Z => fun _28742 : Z => Rle (IZR _28741) (IZR _28742)).
Proof.
  apply fun_ext. intro n.
  apply fun_ext. intro m.
  apply prop_ext.
  - apply IZR_le.
  - apply le_IZR.
Qed.

Lemma int_lt_def :
  Z.lt = (fun _28753 : Z => fun _28754 : Z => Rlt (IZR _28753) (IZR _28754)).
Proof.
  apply fun_ext. intro n.
  apply fun_ext. intro m.
  apply prop_ext.
  - apply IZR_lt.
  - apply lt_IZR.
Qed.

Lemma int_ge_def :
  Z.ge = (fun _28765 : Z => fun _28766 : Z => Rge (IZR _28765) (IZR _28766)).
Proof.
  rewrite real_ge_def.
  ext n m. apply prop_ext.
  - intros h%Z.ge_le. apply IZR_le. assumption.
  - intros h. apply Z.le_ge. apply le_IZR. assumption.
Qed.

Lemma int_gt_def :
  Z.gt = (fun _28777 : Z => fun _28778 : Z => Rgt (IZR _28777) (IZR _28778)).
Proof.
  rewrite real_gt_def.
  ext n m. apply prop_ext.
  - intros h%Z.gt_lt. apply IZR_lt. assumption.
  - intros h. apply Z.lt_gt. apply lt_IZR. assumption.
Qed.

Lemma int_neg_def :
  Z.opp = (fun _28794 : Z => int_of_real (Ropp (IZR _28794))).
Proof.
  ext n.
  rewrite <- opp_IZR. rewrite axiom_25.
  reflexivity.
Qed.

Lemma int_add_def :
  Z.add = (fun _28803 : Z => fun _28804 : Z => int_of_real (Rplus (IZR _28803) (IZR _28804))).
Proof.
  apply fun_ext. intro n.
  apply fun_ext. intro m.
  rewrite <- plus_IZR. rewrite axiom_25.
  reflexivity.
Qed.

Lemma int_sub_def :
  Z.sub = (fun _28835 : Z => fun _28836 : Z => int_of_real (Rminus (IZR _28835) (IZR _28836))).
Proof.
  ext n m.
  rewrite <- minus_IZR. rewrite axiom_25.
  reflexivity.
Qed.

Lemma int_mul_def :
  Z.mul =
  (fun _28847 : Z => fun _28848 : Z => int_of_real (Rmult (IZR _28847) (IZR _28848))).
Proof.
  apply fun_ext. intro n.
  apply fun_ext. intro m.
  rewrite <- mult_IZR. rewrite axiom_25.
  reflexivity.
Qed.

Lemma int_abs_def :
  Z.abs = (fun _28867 : Z => int_of_real (Rabs (IZR _28867))).
Proof.
  apply fun_ext. intro n.
  rewrite Rabs_Zabs. rewrite axiom_25.
  reflexivity.
Qed.

Lemma int_sgn_def :
  Z.sgn = (fun _28878 : Z => int_of_real (Rsgn (IZR _28878))).
Proof.
  ext z.
  destruct z. all: cbn.
  - rewrite Rsgn_0. rewrite axiom_25. reflexivity.
  - rewrite Rsgn_pos.
    2:{ apply IZR_lt. lia. }
    rewrite axiom_25. reflexivity.
  - rewrite Rsgn_neg.
    2:{ apply IZR_lt. lia. }
    rewrite axiom_25. reflexivity.
Qed.

Lemma int_max_def :
  Z.max = (fun _28938 : Z => fun _28939 : Z => int_of_real (Rmax (IZR _28938) (IZR _28939))).
Proof.
  ext n m.
  eapply Rmax_case_strong. all: intro h. all: apply le_IZR in h.
  - rewrite Z.max_l. 2: lia.
    rewrite axiom_25. reflexivity.
  - rewrite Z.max_r. 2: lia.
    rewrite axiom_25. reflexivity.
Qed.

Lemma int_min_def :
  Z.min = (fun _28956 : Z => fun _28957 : Z => int_of_real (Rmin (IZR _28956) (IZR _28957))).
Proof.
  ext n m.
  eapply Rmin_case_strong. all: intro h. all: apply le_IZR in h.
  - rewrite Z.min_l. 2: lia.
    rewrite axiom_25. reflexivity.
  - rewrite Z.min_r. 2: lia.
    rewrite axiom_25. reflexivity.
Qed.

Definition Zpow n m := (n ^ Z.of_N m)%Z.

Lemma int_pow_def :
  Zpow = (fun _28974 : Z => fun _28975 : N => int_of_real (Rpow (IZR _28974) _28975)).
Proof.
  ext n m.
  rewrite <- (Nnat.N2Nat.id m).
  generalize (N.to_nat m) as k. clear m. intro m.
  unfold Zpow, Rpow.
  rewrite nat_N_Z.
  rewrite <- Rfunctions.pow_powerRZ.
  rewrite <- axiom_25 at 1. f_equal.
  induction m as [| m ih].
  - cbn. reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2: lia.
    rewrite mult_IZR. rewrite ih. reflexivity.
Qed.

Definition Zdiv a b := (Z.sgn b * (a / Z.abs b))%Z.
(* = Coq.ZArith.Zeuclid.ZEuclid.div but Coq.ZArith.Zeuclid is deprecated *)

Definition Zrem a b := (a mod Z.abs b)%Z.
(* = Coq.ZArith.Zeuclid.ZEuclid.modulo but Coq.ZArith.Zeuclid is deprecated *)

Lemma div_def :
  Zdiv = (@ε ((prod N (prod N N)) -> Z -> Z -> Z) (fun q : (prod N (prod N N)) -> Z -> Z -> Z => forall _29326 : prod N (prod N N), exists r : Z -> Z -> Z, forall m : Z, forall n : Z, @COND Prop (n = (Z_of_N (NUMERAL 0%N))) (((q _29326 m n) = (Z_of_N (NUMERAL 0%N))) /\ ((r m n) = m)) ((Z.le (Z_of_N (NUMERAL 0%N)) (r m n)) /\ ((Z.lt (r m n) (Z.abs n)) /\ (m = (Z.add (Z.mul (q _29326 m n) n) (r m n)))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0%N))))))))))).
Proof.
  align_ε.
  { exists Zrem. unfold Zdiv, Zrem. cbn. intros m n.
    apply prove_COND.
    - intros ->. cbn. split.
      + reflexivity.
      + apply Zdiv.Zmod_0_r.
    - intros hnz.
      assert (han : (0 < Z.abs n)%Z).
      { pose proof (Z.abs_nonneg n). lia. }
      split. 2: split.
      + apply Z.mod_pos_bound. assumption.
      + apply Z.mod_pos_bound. assumption.
      + pose proof (Z.div_mod m (Z.abs n)). lia.
  }
  cbn. intros div' [rem h].
  ext m n. specialize (h m n).
  eapply COND_elim with (1 := h) ; clear.
  - unfold Zdiv. intros -> [-> e].
    cbn. reflexivity.
  - intros hnz [h1 [h2 h3]].
    assert (Z.sgn n * div' m n = m / Z.abs n)%Z as e.
    { apply Z.div_unique_pos with (rem m n). all: lia. }
    unfold Zdiv. lia.
Qed.

Lemma rem_def :
  Zrem = (@ε ((prod N (prod N N)) -> Z -> Z -> Z) (fun r : (prod N (prod N N)) -> Z -> Z -> Z => forall _29327 : prod N (prod N N), forall m : Z, forall n : Z, @COND Prop (n = (Z_of_N (NUMERAL 0%N))) (((Zdiv m n) = (Z_of_N (NUMERAL 0%N))) /\ ((r _29327 m n) = m)) ((Z.le (Z_of_N (NUMERAL 0%N)) (r _29327 m n)) /\ ((Z.lt (r _29327 m n) (Z.abs n)) /\ (m = (Z.add (Z.mul (Zdiv m n) n) (r _29327 m n)))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N))))))))))).
Proof.
  align_ε.
  { unfold Zdiv, Zrem. intros m n.
    apply prove_COND.
    - intros ->. cbn. split.
      + reflexivity.
      + apply Zdiv.Zmod_0_r.
    - cbn. intros hnz.
      assert (han : (0 < Z.abs n)%Z).
      { pose proof (Z.abs_nonneg n). lia. }
      split. 2: split.
      + apply Z.mod_pos_bound. assumption.
      + apply Z.mod_pos_bound. assumption.
      + pose proof (Z.div_mod m (Z.abs n)). lia.
  }
  cbn. intros rem' h.
  ext m n. specialize (h m n).
  eapply COND_elim with (1 := h) ; clear.
  - unfold Zdiv, Zrem. intros -> [e ->].
    cbn. apply Zdiv.Zmod_0_r.
  - unfold Zdiv, Zrem. intros hnz [h1 [h2 h3]].
    pose proof (Z.div_mod m (Z.abs n)) as e.
    rewrite <- Z.sgn_abs in e at 1.
    lia.
Qed.

Lemma Zdiv_pos a b : (0 < b)%Z -> Zdiv a b = Z.div a b.
Proof.
  intro h. unfold Zdiv. rewrite Z.sgn_pos. 2: assumption.
  rewrite Z.abs_eq. 2: lia. lia.
Qed.

Definition Rmod_eq (a b c : R) := exists k, b - c = IZR k * a.

Lemma real_mod_def :
  Rmod_eq = (fun _29623 : R => fun _29624 : R => fun _29625 : R => exists q : R, (integer q) /\ ((Rminus _29624 _29625) = (Rmult q _29623))).
Proof.
  ext a b c. unfold Rmod_eq. apply prop_ext.
  - intros [k e]. exists (IZR k). split.
    + apply IZR_integer. eexists. reflexivity.
    + assumption.
  - intros [q [hq e]].
    apply integer_IZR in hq as [k ->].
    exists k. assumption.
Qed.

(** TODO Replace by [PreOmega.Z.divide_alt] once Coq 8.19 support is dropped **)
Lemma divide_alt x y : Z.divide x y -> exists z, y = (x * z)%Z.
Proof.
  intros [z ->]. exists z. apply Z.mul_comm.
Qed.

Lemma int_divides_def :
  Z.divide = (fun _29644 : Z => fun _29645 : Z => exists x : Z, _29645 = (Z.mul _29644 x)).
Proof.
  ext a b. apply prop_ext.
  - apply divide_alt.
  - intros [c e]. eapply Znumtheory.Zdivide_intro with c. lia.
Qed.

Definition int_coprime '(a,b) := exists x y, (a * x + b * y = 1)%Z.

Lemma int_coprime_def :
  int_coprime = (fun _29691 : prod Z Z => exists x : Z, exists y : Z, (Z.add (Z.mul (@fst Z Z _29691) x) (Z.mul (@snd Z Z _29691) y)) = (Z_of_N (NUMERAL (BIT1 0%N)))).
Proof.
  ext p. destruct p as [a b].
  cbn. reflexivity.
Qed.

Definition int_gcd '(a,b) := Z.gcd a b.

Lemma int_gcd_def :
  int_gcd = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod Z Z) -> Z) (fun d : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod Z Z) -> Z => forall _30960 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall a : Z, forall b : Z, (Z.le (Z_of_N (NUMERAL 0%N)) (d _30960 (@pair Z Z a b))) /\ ((Z.divide (d _30960 (@pair Z Z a b)) a) /\ ((Z.divide (d _30960 (@pair Z Z a b)) b) /\ (exists x : Z, exists y : Z, (d _30960 (@pair Z Z a b)) = (Z.add (Z.mul a x) (Z.mul b y)))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0%N)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0%N)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 0%N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0%N))))))))))))))).
Proof.
  cbn. align_ε. unfold int_gcd.
  - intros a b. split. 2: split. 3: split.
    + apply Z.gcd_nonneg.
    + apply Z.gcd_divide_l.
    + apply Z.gcd_divide_r.
    + pose proof (Z.gcd_bezout a b (Z.gcd a b) eq_refl) as [x [y h]].
      exists x, y. lia.
  - intros gcd' h.
    ext p. destruct p as [a b].
    specialize (h a b) as [hnn [hdl [hdr [x [y e]]]]].
    apply Z.gcd_unique. 1-3: assumption.
    intros q ha hb. rewrite e.
    apply Z.divide_add_r.
    + apply Z.divide_mul_l. assumption.
    + apply Z.divide_mul_l. assumption.
Qed.

Definition int_lcm '(a,b) := Z.lcm a b.

Lemma int_lcm_def :
  int_lcm = (fun y0 : prod Z Z => @COND Z ((Z.mul (@fst Z Z y0) (@snd Z Z y0)) = (Z_of_N (NUMERAL 0%N))) (Z_of_N (NUMERAL 0%N)) (Zdiv (Z.abs (Z.mul (@fst Z Z y0) (@snd Z Z y0))) (int_gcd (@pair Z Z (@fst Z Z y0) (@snd Z Z y0))))).
Proof.
  unfold int_lcm, int_gcd. cbn.
  ext p. destruct p as [a b]. cbn.
  rewrite thm_COND_ELIM_THM. split.
  - intro e. rewrite Z.lcm_eq_0. lia.
  - intro hn.
    set (m := Z.lcm a b).
    set (d := (Z.abs(a * b) / m)%Z).
    assert (hmnz : m <> 0%Z).
    { pose proof (Z.lcm_eq_0 a b).
      lia.
    }
    assert (hmab : (Z.abs (a * b) mod m)%Z = 0%Z).
    { apply Znumtheory.Zdivide_mod.
      rewrite Z.divide_abs_r.
      apply Z.lcm_least.
      - apply Z.divide_mul_l. reflexivity.
      - apply Z.divide_mul_r. reflexivity.
    }
    assert (h : Z.gcd a b = d).
    { apply Z.gcd_unique.
      - apply Zdiv.Z_div_nonneg_nonneg.
        + lia.
        + apply Z.lcm_nonneg.
      - unfold d.
        assert (h : (b | m)%Z).
        { apply Z.divide_lcm_r. }
        apply Z.mul_divide_mono_l with (p := a) in h.
        apply Z.divide_abs_l in h.
        apply Z.divide_div with (a := m) in h.
        2: assumption.
        2:{ apply Z.mod_divide. all: assumption. }
        rewrite Znumtheory.Zdivide_Zdiv_eq_2 in h.
        2:{ pose proof (Z.lcm_nonneg a b). lia. }
        2: reflexivity.
        rewrite Z.div_same in h. 2: assumption.
        replace (a * 1)%Z with a in h by lia.
        assumption.
      - unfold d.
        assert (h : (a | m)%Z).
        { apply Z.divide_lcm_l. }
        apply Z.mul_divide_mono_r with (p := b) in h.
        apply Z.divide_abs_l in h.
        apply Z.divide_div with (a := m) in h.
        2: assumption.
        2:{ apply Z.mod_divide. all: assumption. }
        replace (m * b)%Z with (b * m)%Z in h by lia.
        rewrite Znumtheory.Zdivide_Zdiv_eq_2 in h.
        2:{ pose proof (Z.lcm_nonneg a b). lia. }
        2: reflexivity.
        rewrite Z.div_same in h. 2: assumption.
        replace (b * 1)%Z with b in h by lia.
        assumption.
      - intros n ha hb.
        assert (hnnz : n <> 0%Z).
        { destruct ha as [k e]. lia. }
        assert (hndm : (n | m)%Z).
        { transitivity b. 1: assumption. apply Z.divide_lcm_r. }
        replace n with (m * n / m)%Z.
        2:{ rewrite Z.mul_comm. apply Z.div_mul. assumption. }
        replace d with (m * d / m)%Z.
        2:{ rewrite Z.mul_comm. apply Z.div_mul. assumption. }
        apply Z.divide_div.
        1: assumption. 1:{ apply Z.divide_mul_l. reflexivity. }
        replace (m * d)%Z with (((m * d) / n) * n)%Z.
        2:{
          replace (m * d)%Z with (d * m)%Z by lia.
          rewrite Z.divide_div_mul_exact. 2,3: assumption.
          rewrite <- Z.mul_assoc.
          rewrite Z.mul_comm.
          replace ((m / n) * n)%Z with (n * (m / n))%Z by lia.
          rewrite <- Zdiv.Z_div_exact_full_2. 2: assumption.
          2:{ apply Znumtheory.Zdivide_mod. assumption. }
          lia.
        }
        apply Z.mul_divide_mono_r.
        replace (m * d / n)%Z with (Z.abs (a * b) / n)%Z.
        2:{
          unfold d.
          rewrite <- Zdiv.Z_div_exact_full_2. 2,3: assumption.
          lia.
        }
        apply Z.lcm_least.
        + replace a with ((n * a) / n)%Z at 1.
          2:{
            rewrite Z.divide_div_mul_exact. 2,3: assumption.
            rewrite <- Zdiv.Z_div_exact_full_2. 2: assumption.
            2:{ apply Znumtheory.Zdivide_mod. assumption. }
            reflexivity.
          }
          apply Z.divide_div. 1: assumption.
          1:{ apply Z.divide_mul_l. reflexivity. }
          rewrite Z.divide_abs_r.
          rewrite Z.mul_comm.
          apply Z.mul_divide_mono_l.
          assumption.
        + replace b with ((n * b) / n)%Z at 1.
          2:{
            rewrite Z.divide_div_mul_exact. 2,3: assumption.
            rewrite <- Zdiv.Z_div_exact_full_2. 2: assumption.
            2:{ apply Znumtheory.Zdivide_mod. assumption. }
            reflexivity.
          }
          apply Z.divide_div. 1: assumption.
          1:{ apply Z.divide_mul_l. reflexivity. }
          rewrite Z.divide_abs_r.
          apply Z.mul_divide_mono_r.
          assumption.
    }
    unfold d in h.
    apply (f_equal (Z.mul m)) in h as e.
    rewrite <- Zdiv.Z_div_exact_full_2 in e. 2,3: assumption.
    apply (f_equal (fun x => (x / Z.gcd a b)%Z)) in e.
    assert (hgcd : Z.gcd a b <> 0%Z).
    { pose proof (Z.gcd_divide_r a b) as []. lia. }
    rewrite Z.divide_div_mul_exact in e. 2: assumption. 2: reflexivity.
    rewrite Z.div_same in e. 2: assumption.
    rewrite Zdiv_pos.
    2:{ pose proof (Z.gcd_nonneg a b). lia. }
    lia.
Qed.

Close Scope R_scope.

(*****************************************************************************)
(* Sets. *)
(*****************************************************************************)

Definition IN {A : Type'} : A -> (A -> Prop) -> Prop := fun _32683 : A => fun _32684 : A -> Prop => _32684 _32683.

Lemma IN_def {A : Type'} : (@IN A) = (fun _32317 : A => fun _32318 : A -> Prop => _32318 _32317).
Proof. exact (eq_refl (@IN A)). Qed.

Definition EMPTY {A : Type'} : A -> Prop := fun x : A => False.

Lemma EMPTY_def {A : Type'} : (@EMPTY A) = (fun x : A => False).
Proof. exact (eq_refl (@EMPTY A)). Qed.

Definition INSERT {A : Type'} : A -> (A -> Prop) -> A -> Prop := fun _32739 : A => fun _32740 : A -> Prop => fun y : A => (@IN A y _32740) \/ (y = _32739).

Lemma INSERT_def {A : Type'} : (@INSERT A) = (fun _32373 : A => fun _32374 : A -> Prop => fun y : A => (@IN A y _32374) \/ (y = _32373)).
Proof. exact (eq_refl (@INSERT A)). Qed.

Definition UNIV (A : Type') : A -> Prop := fun x : A => True.

Lemma UNIV_def {A : Type'} : (@UNIV A) = (fun x : A => True).
Proof. exact (eq_refl (@UNIV A)). Qed.

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

Definition GSPEC {A : Type'} : (A -> Prop) -> A -> Prop := fun _32695 : A -> Prop => _32695.

Lemma GSPEC_def {A : Type'} : (@GSPEC A) = (fun _32329 : A -> Prop => _32329).
Proof. exact (eq_refl (@GSPEC A)). Qed.

Definition SETSPEC {_83031 : Type'} : _83031 -> Prop -> _83031 -> Prop := fun _32700 : _83031 => fun _32701 : Prop => fun _32702 : _83031 => _32701 /\ (_32700 = _32702).

Lemma SETSPEC_def {A : Type'} : (@SETSPEC A) = (fun _32334 : A => fun _32335 : Prop => fun _32336 : A => _32335 /\ (_32334 = _32336)).
Proof. exact (eq_refl (@SETSPEC A)). Qed.

Definition SUBSET {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun s : A -> Prop => fun t : A -> Prop => forall x : A, (@IN A x s) -> @IN A x t.

Lemma SUBSET_def {A : Type'} : (@SUBSET A) = (fun _32443 : A -> Prop => fun _32444 : A -> Prop => forall x : A, (@IN A x _32443) -> @IN A x _32444).
Proof. exact (eq_refl (@SUBSET A)). Qed.

Definition INTER {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun s : A -> Prop => fun t : A -> Prop => @GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x s) /\ (@IN A x t)) x).

Lemma INTER_def {A : Type'} : (@INTER A) = (fun _32402 : A -> Prop => fun _32403 : A -> Prop => @GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x _32402) /\ (@IN A x _32403)) x)).
Proof. exact (eq_refl (@INTER A)). Qed.

Definition UNIONS {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun U : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u U) /\ (@IN A x u)) x).

Lemma UNIONS_def {A : Type'} : (@UNIONS A) = (fun _32397 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u _32397) /\ (@IN A x u)) x)).
Proof. exact (eq_refl (@UNIONS A)). Qed.

(*****************************************************************************)
(* Finite sets. *)
(*****************************************************************************)

Definition FINITE {A : Type'} : (A -> Prop) -> Prop := fun a : A -> Prop => forall FINITE' : (A -> Prop) -> Prop, (forall a' : A -> Prop, ((a' = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a' = (@INSERT A x s)) /\ (FINITE' s))) -> FINITE' a') -> FINITE' a.

Lemma FINITE_def {A : Type'} : (@FINITE A) = (fun a : A -> Prop => forall FINITE' : (A -> Prop) -> Prop, (forall a' : A -> Prop, ((a' = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a' = (@INSERT A x s)) /\ (FINITE' s))) -> FINITE' a') -> FINITE' a).
Proof. exact (eq_refl (@FINITE A)). Qed.

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

Require Import Coq.Lists.List.

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

Require Import Coq.Sorting.Permutation.

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

(*Definition ITSET {A B : Type'} : (B -> A -> A) -> (B -> Prop) -> A -> A := fun f : B -> A -> A => fun s : B -> Prop => fun a : A => @ε ((B -> Prop) -> A) (fun g : (B -> Prop) -> A => ((g (@EMPTY B)) = a) /\ (forall x : B, forall s : B -> Prop, (@FINITE B s) -> (g (@INSERT B x s)) = (@COND A (@IN B x s) (g s) (f x (g s))))) s.*)

Definition ITSET {A B : Type'} : (A -> B -> B) -> (A -> Prop) -> B -> B := fun _43025 : A -> B -> B => fun _43026 : A -> Prop => fun _43027 : B => @ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@EMPTY A)) = _43027) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (_43025 x (g s))))) _43026.

Lemma ITSET_def {A B : Type'} : (@ITSET A B) = (fun _43025 : A -> B -> B => fun _43026 : A -> Prop => fun _43027 : B => @ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@EMPTY A)) = _43027) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (_43025 x (g s))))) _43026).
Proof. exact (eq_refl (@ITSET A B)). Qed.

Definition itset {A B:Type'} : (B -> A -> A) -> (B -> Prop) -> A -> A := fun f : B -> A -> A => let F := fun a b => f b a in fun s : B -> Prop => fun a : A => fold_left F (elements s) a.

Lemma itset_EMPTY {A B:Type'} (f:B -> A -> A) a: itset f EMPTY a = a.
Proof. unfold itset. rewrite elements_EMPTY. simpl. reflexivity. Qed.

Definition permut_inv' {A B:Type} (f:B -> A -> A) := forall a y x, f x (f y a) = f y (f x a).

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

(*Definition CARD {A : Type'} : (A -> Prop) -> N := fun s => @ITSET N A (fun x : A => fun n : N => N.succ n) s (NUMERAL 0).*)

Definition CARD {A : Type'} : (A -> Prop) -> N := fun _43228 : A -> Prop => @ITSET A N (fun x : A => fun n : N => N.succ n) _43228 (NUMERAL N0).

Lemma CARD_def {A : Type'} : (@CARD A) = (fun _43228 : A -> Prop => @ITSET A N (fun x : A => fun n : N => N.succ n) _43228 (NUMERAL N0)).
Proof. exact (eq_refl (@CARD A)). Qed.

Definition dimindex {A : Type'} : (A -> Prop) -> N := fun _ => @COND N (@FINITE A (UNIV A)) (@CARD A (UNIV A)) (NUMERAL (BIT1 0)).

Lemma dimindex_def {A : Type'} : (@dimindex A) = (fun _94156 : A -> Prop => @COND N (@FINITE A (@UNIV A)) (@CARD A (@UNIV A)) (NUMERAL (BIT1 N0))).
Proof. exact (eq_refl (@dimindex A)). Qed.

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
  assert (p1: permut_inv' (fun (_ : A) (n : N) => N.succ n)). unfold permut_inv'. reflexivity.

  unfold dimindex. case (prop_degen (FINITE (UNIV A))); intro h; rewrite h.

  assert (p2: finite (UNIV A)). rewrite <- FINITE_eq_finite, h. exact Logic.I.
  assert (p3: finite (fun x : A => x <> el A)).
    apply (Incl_finite (UNIV A)). exact p2. intros x _. exact Logic.I.

  rewrite COND_True. unfold CARD.
  rewrite ITSET_eq_itset, UNIV_eq_INSERT, itset_INSERT, IN_el_not_el, COND_False; auto.
  lia.

  rewrite COND_False. unfold NUMERAL, BIT1. lia.
Qed.

Lemma CARD_ge_1 {A : Type'} : FINITE (UNIV A) -> 1 <= CARD (UNIV A).
Proof.
  rewrite FINITE_eq_finite. intro p2.
  assert (p1: permut_inv' (fun (_ : A) (n : N) => N.succ n)). unfold permut_inv'. reflexivity.
  assert (p3: finite (fun x : A => x <> el A)).
  apply (Incl_finite (UNIV A)). exact p2. intros x _. exact Logic.I.
  rewrite UNIV_eq_INSERT. unfold CARD.
  rewrite ITSET_eq_itset. 2: exact p1. 2: rewrite UNIV_eq_INSERT in p2; exact p2.
  rewrite itset_INSERT, IN_el_not_el, COND_False. lia. exact p1. exact p3.
Qed.

(*****************************************************************************)
(* Cart.finite_image: natural numbers between 1 and the cardinal of A,
if A is finite, and 1 otherwise. *)
(*****************************************************************************)

Definition dotdot : N -> N -> N -> Prop := fun _69692 : N => fun _69693 : N => @GSPEC N (fun GEN_PVAR_229 : N => exists x : N, @SETSPEC N GEN_PVAR_229 ((N.le _69692 x) /\ (N.le x _69693)) x).

Axiom dotdot_def : dotdot = (fun _66922 : N => fun _66923 : N => @GSPEC N (fun GEN_PVAR_231 : N => exists x : N, @SETSPEC N GEN_PVAR_231 ((N.le _66922 x) /\ (N.le x _66923)) x)).

Definition finite_image_pred (A:Type') x :=
  @IN N x (dotdot (NUMERAL (BIT1 0)) (@dimindex A (UNIV A))).

Lemma finite_image_pred1 (A:Type') : finite_image_pred A 1.
Proof.
  unfold finite_image_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A). lia.
Qed.

Definition finite_image : Type' -> Type' :=
  fun A => subtype (finite_image_pred1 A).

Definition finite_index : forall {A : Type'}, N -> finite_image A :=
  fun A => mk (finite_image_pred1 A).

Definition dest_finite_image : forall {A : Type'}, (finite_image A) -> N :=
  fun A => dest (finite_image_pred1 A).

Lemma axiom_27 : forall {A : Type'} (a : finite_image A), (@finite_index A (@dest_finite_image A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_28 : forall {A : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 0)) (@dimindex A (UNIV A)))) r) = ((@dest_finite_image A (@finite_index A r)) = r).
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

Definition finite_sum_pred (A B: Type') x := @IN N x (dotdot (NUMERAL (BIT1 0)) (N.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B)))).

Lemma finite_sum_pred1 (A B:Type') : finite_sum_pred A B 1.
Proof.
  unfold finite_sum_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A) (dimindex_UNIV_gt_0 B). lia.
Qed.

Definition finite_sum : Type' -> Type' -> Type' :=
  fun A B => subtype (finite_sum_pred1 A B).

Definition mk_finite_sum : forall {A B : Type'}, N -> finite_sum A B :=
  fun A B => mk (finite_sum_pred1 A B).

Definition dest_finite_sum : forall {A B : Type'}, (finite_sum A B) -> N :=
  fun A B => dest (finite_sum_pred1 A B).

Lemma axiom_31 : forall {A B : Type'} (a : finite_sum A B), (@mk_finite_sum A B (@dest_finite_sum A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_32 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 0)) (N.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B))))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Cart.finite_diff *)
(*****************************************************************************)

Definition finite_diff_pred (A B: Type') x := @IN N x (dotdot (NUMERAL (BIT1 0)) (@COND N (N.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (N.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 0)))).

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

Definition mk_finite_diff : forall {A B : Type'}, N -> finite_diff A B :=
  fun A B => mk (finite_diff_pred1 A B).

Definition dest_finite_diff : forall {A B : Type'}, (finite_diff A B) -> N :=
  fun A B => dest (finite_diff_pred1 A B).

Lemma axiom_33 : forall {A B : Type'} (a : finite_diff A B), (@mk_finite_diff A B (@dest_finite_diff A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_34 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 0)) (@COND N (N.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (N.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Cart.finite_prod *)
(*****************************************************************************)

Definition finite_prod_pred (A B: Type') x := @IN N x (dotdot (NUMERAL (BIT1 0)) (N.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B)))).

Lemma finite_prod_pred1 (A B:Type') : finite_prod_pred A B 1.
Proof.
  unfold finite_prod_pred, IN, dotdot, GSPEC, SETSPEC, NUMERAL, BIT1, BIT0.
  exists 1. generalize (dimindex_UNIV_gt_0 A) (dimindex_UNIV_gt_0 B); intros. lia.
Qed.

Definition finite_prod : Type' -> Type' -> Type' :=
  fun A B => subtype (finite_prod_pred1 A B).

Definition mk_finite_prod : forall {A B : Type'}, N -> finite_prod A B :=
  fun A B => mk (finite_prod_pred1 A B).

Definition dest_finite_prod : forall {A B : Type'}, (finite_prod A B) -> N :=
  fun A B => dest (finite_prod_pred1 A B).

Lemma axiom_35 : forall {A B : Type'} (a : finite_prod A B), (@mk_finite_prod A B (@dest_finite_prod A B a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_36 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 0)) (N.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r).
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

Lemma axiom_38 : forall {A : Type'} (r : recspace (finite_sum A A)), ((fun a : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a''' (fun n : N => @BOTTOM (finite_sum A A))) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A (@_mk_tybit0 A r)) = r).
Proof. intro A. apply nr_dest_mk. Qed.

(*****************************************************************************)
(* Cart.tybit1 *)
(*****************************************************************************)

Definition tybit1 A := nr_type (finite_sum (finite_sum A A) unit).

Definition _mk_tybit1 : forall {A : Type'}, (recspace (finite_sum (finite_sum A A) unit)) -> tybit1 A := fun A => nr_mk (finite_sum (finite_sum A A) unit).

Definition _dest_tybit1 : forall {A : Type'}, (tybit1 A) -> recspace (finite_sum (finite_sum A A) unit) := fun A => nr_dest (finite_sum (finite_sum A A) unit).

Lemma axiom_39 : forall {A : Type'} (a : tybit1 A), (@_mk_tybit1 A (@_dest_tybit1 A a)) = a.
Proof. intro A. apply nr_mk_dest. Qed.

Lemma axiom_40 : forall {A : Type'} (r : recspace (finite_sum (finite_sum A A) unit)), ((fun a : recspace (finite_sum (finite_sum A A) unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) unit), (exists a'' : finite_sum (finite_sum A A) unit, a' = ((fun a''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a''' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A (@_mk_tybit1 A r)) = r).
Proof. intro A. apply nr_dest_mk. Qed.

(*****************************************************************************)
(* Library.Frag.frag (free Abelian group) *)
(*****************************************************************************)

Definition is_frag {A:Type'} (f:A -> Z) := @FINITE A (@GSPEC A (fun GEN_PVAR_709 : A => exists x : A, @SETSPEC A GEN_PVAR_709 (~ ((f x) = (Z_of_N (NUMERAL 0%N)))) x)).

Lemma is_frag0 (A:Type') : is_frag (fun _:A => 0%Z).
Proof.
  unfold is_frag, GSPEC, SETSPEC. rewrite FINITE_eq_finite, finite_list_NoDup.
  exists nil. split. apply NoDup_nil.
  apply fun_ext; intro a. apply prop_ext.
  intros [a' [h1 h2]]. apply False_rec. apply h1. reflexivity.
  intro h. apply False_rec. apply h.
Qed.

Definition frag A := subtype (is_frag0 A).

Definition mk_frag : forall {A : Type'}, (A -> Z) -> frag A := fun A => mk (is_frag0 A).

Definition dest_frag : forall {A : Type'}, (frag A) -> A -> Z := fun A => dest (is_frag0 A).

Lemma axiom_41 : forall {A : Type'} (a : frag A), (@mk_frag A (@dest_frag A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_42 : forall {A : Type'} (r : A -> Z), ((fun f : A -> Z => @FINITE A (@GSPEC A (fun GEN_PVAR_709 : A => exists x : A, @SETSPEC A GEN_PVAR_709 (~ ((f x) = (Z_of_N (NUMERAL 0%N)))) x))) r) = ((@dest_frag A (@mk_frag A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Library.grouptheory.group *)
(*****************************************************************************)

Definition Grp (A:Type') := prod (A -> Prop) (prod A (prod (A -> A) (A -> A -> A))).
Definition Gcar {A:Type'} (G: Grp A) := fst G.
Definition G0 {A:Type'} (G:Grp A) := fst (snd G).
Definition Gop {A:Type'} (G:Grp A) := snd (snd (snd G)).
Definition Ginv {A:Type'} (G:Grp A) := fst (snd (snd G)).

Definition is_group {A:Type'} (r:Grp A) := IN (G0 r) (Gcar r)
/\ ((forall x, IN x (Gcar r) -> IN (Ginv r x) (Gcar r))
/\ ((forall x y, (IN x (Gcar r) /\ (IN y (Gcar r))) -> IN (Gop r x y) (Gcar r))
/\ ((forall x y z, (IN x (Gcar r) /\ (IN y (Gcar r) /\ IN z (Gcar r))) ->
Gop r x (Gop r y z) = Gop r (Gop r x y) z)
/\ ((forall x, IN x (Gcar r) -> (Gop r (G0 r) x = x) /\ (Gop r x (G0 r) = x))
/\ (forall x, IN x (Gcar r) -> (Gop r (Ginv r x) x = G0 r) /\ (Gop r x (Ginv r x) = G0 r)))))).

Definition g0 (A:Type') : Grp A := pair (fun x => x = el A) (pair (el A) (pair (fun _ => el A) (fun _ _ => el A))).

Lemma is_group0 (A:Type') : is_group (g0 A).
Proof. firstorder. Qed.

Definition Group (A:Type') := subtype (is_group0 A).

Definition group : forall {A : Type'}, Grp A -> Group A := fun A => mk (is_group0 A).
Definition group_operations : forall {A : Type'}, (Group A) -> Grp A := fun A => dest (is_group0 A).

Lemma axiom_43 : forall {A : Type'} (a : Group A), (@group A (@group_operations A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_44 : forall {A : Type'} (r : Grp A), is_group r = (group_operations (group r) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Library.Matroids.matroid *)
(*****************************************************************************)

Definition is_matroid {A:Type'} m := (forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A s (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall t : A -> Prop, ((@SUBSET A s t) /\ (@SUBSET A t (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m))) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m t)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) = (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall x : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s))) -> exists s' : A -> Prop, (@FINITE A s') /\ ((@SUBSET A s' s) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s')))) /\ (forall s : A -> Prop, forall x : A, forall y : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A x (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A x s))) /\ (~ (@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)))))) -> @IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A y s))))))).

Lemma is_matroid_def {A:Type'} m : is_matroid m = ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A s (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall t : A -> Prop, ((@SUBSET A s t) /\ (@SUBSET A t (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m))) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m t)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) = (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall x : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s))) -> exists s' : A -> Prop, (@FINITE A s') /\ ((@SUBSET A s' s) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s')))) /\ (forall s : A -> Prop, forall x : A, forall y : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A x (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A x s))) /\ (~ (@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)))))) -> @IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A y s)))))))).
Proof. reflexivity. Qed.

Lemma is_matroid0 (A:Type') : is_matroid (pair (fun _:A => False) (fun x => x)).
Proof. firstorder. Qed.

Definition Matroid (A:Type') := subtype (is_matroid0 A).

Definition matroid : forall {A : Type'}, (prod (A -> Prop) ((A -> Prop) -> A -> Prop)) -> Matroid A := fun A => mk (is_matroid0 A).

Definition dest_matroid : forall {A : Type'}, (Matroid A) -> prod (A -> Prop) ((A -> Prop) -> A -> Prop) := fun A => dest (is_matroid0 A).

Lemma axiom_45 : forall {A : Type'} (a : Matroid A), (@matroid A (@dest_matroid A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_46 : forall {A : Type'} (r : prod (A -> Prop) ((A -> Prop) -> A -> Prop)), (is_matroid r) = ((@dest_matroid A (@matroid A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Library.Analysis.topology *)
(*****************************************************************************)

Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop :=
  fun U => (IN EMPTY U)
        /\ ((forall s t, ((IN s U) /\ (IN t U)) -> IN (INTER s t) U)
           /\ (forall k, SUBSET k U -> IN (UNIONS k) U)).

Lemma istopology_def {A : Type'} : (@istopology A) = (fun U : (A -> Prop) -> Prop => (@IN (A -> Prop) (@EMPTY A) U) /\ ((forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s U) /\ (@IN (A -> Prop) t U)) -> @IN (A -> Prop) (@INTER A s t) U) /\ (forall k : (A -> Prop) -> Prop, (@SUBSET (A -> Prop) k U) -> @IN (A -> Prop) (@UNIONS A k) U))).
Proof. exact (eq_refl (@istopology A)). Qed.

Lemma istopology0 (A:Type') : @istopology A (fun _ => True).
Proof. firstorder. Qed.

Definition Topology (A:Type') := subtype (istopology0 A).

Definition topology : forall {A : Type'}, ((A -> Prop) -> Prop) -> Topology A := fun A => mk (istopology0 A).

Definition open_in : forall {A : Type'}, (Topology A) -> (A -> Prop) -> Prop := fun A => dest (istopology0 A).

Lemma axiom_47 : forall {A : Type'} (a : Topology A), (@topology A (@open_in A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_48 : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@open_in A (@topology A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Multivariate.Metric.net *)
(*****************************************************************************)

Definition is_net {A:Type'} (g: prod ((A -> Prop) -> Prop) (A -> Prop)) :=
  forall s t, ((IN s (fst g)) /\ (IN t (fst g))) -> IN (INTER s t) (fst g).

Lemma is_net_def {A:Type'} g : is_net g = forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s (@fst ((A -> Prop) -> Prop) (A -> Prop) g)) /\ (@IN (A -> Prop) t (@fst ((A -> Prop) -> Prop) (A -> Prop) g))) -> @IN (A -> Prop) (@INTER A s t) (@fst ((A -> Prop) -> Prop) (A -> Prop) g).
Proof. reflexivity. Qed.

Lemma is_net0 (A:Type') : @is_net A (pair (fun _ => True) (el _)).
Proof. firstorder. Qed.

Definition net (A:Type') := subtype (is_net0 A).

Definition mk_net : forall {A : Type'}, (prod ((A -> Prop) -> Prop) (A -> Prop)) -> net A := fun A => mk (is_net0 A).

Definition dest_net : forall {A : Type'}, (net A) -> prod ((A -> Prop) -> Prop) (A -> Prop) := fun A => dest (is_net0 A).

Lemma axiom_49 : forall {A : Type'} (a : net A), (@mk_net A (@dest_net A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_50 : forall {A : Type'} (r : prod ((A -> Prop) -> Prop) (A -> Prop)), is_net r = ((@dest_net A (@mk_net A r)) = r).
Proof. intros A a. apply dest_mk. Qed.

(*****************************************************************************)
(* Multivariate.Metric.metric *)
(*****************************************************************************)

Definition MS (A:Type') := prod (A -> Prop) ((prod A A) -> R).

Definition Mcar {A:Type'} : MS A -> A -> Prop := fst.
Definition Mdist {A:Type'} : MS A -> prod A A -> R := snd.

Definition is_metric_space {A : Type'} : MS A -> Prop :=
  fun M => (forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                Rle (R_of_N (NUMERAL 0%N)) (Mdist M (@pair A A x y)))
        /\ ((forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                   ((Mdist M (pair x y)) = (R_of_N (NUMERAL 0%N))) = (x = y))
           /\ ((forall x y, ((IN x (Mcar M)) /\ (IN y (Mcar M))) ->
                      (Mdist M (pair x y)) = (Mdist M (pair y x)))
              /\ (forall x y z, ((IN x (Mcar M)) /\ ((IN y (Mcar M)) /\ (IN z (Mcar M)))) ->
                          Rle (Mdist M (pair x z)) (Rplus (Mdist M (pair x y)) (Mdist M (pair y z)))))).

Lemma is_metric_space_def {A : Type'} : (@is_metric_space A) = (fun M : prod (A -> Prop) ((prod A A) -> R) => (forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> Rle (R_of_N (NUMERAL 0%N)) (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y))) /\ ((forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> ((@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) = (R_of_N (NUMERAL 0%N))) = (x = y)) /\ ((forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) = (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A y x))) /\ (forall x : A, forall y : A, forall z : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ ((@IN A y (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A z (@fst (A -> Prop) ((prod A A) -> R) M)))) -> Rle (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x z)) (Rplus (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A y z))))))).
Proof. exact (eq_refl (@is_metric_space A)). Qed.

Lemma is_metric_space0 (A:Type') : @is_metric_space A (pair (fun _ => False) (fun _ => 0%R)).
Proof.
  split; unfold Mcar, Mdist, fst, snd, IN, NUMERAL; rewrite R_of_N0. reflexivity.
  split. tauto. split. reflexivity. tauto.
Qed.

Definition Metric (A:Type') := subtype (is_metric_space0 A).

Definition metric : forall {A : Type'}, (prod (A -> Prop) ((prod A A) -> R)) -> Metric A := fun A => mk (is_metric_space0 A).
Definition dest_metric : forall {A : Type'}, (Metric A) -> prod (A -> Prop) ((prod A A) -> R) := fun A => dest (is_metric_space0 A).

Lemma axiom_51 : forall {A : Type'} (a : Metric A), (@metric A (@dest_metric A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_52 : forall {A : Type'} (r : prod (A -> Prop) ((prod A A) -> R)), ((fun m : prod (A -> Prop) ((prod A A) -> R) => @is_metric_space A m) r) = ((@dest_metric A (@metric A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

(*****************************************************************************)
(* Multivariate.Clifford.multivector *)
(*****************************************************************************)

Definition is_multivector (A:Type') (s:N -> Prop) := SUBSET s (dotdot 1 (dimindex (@UNIV A))).

Lemma is_multivector0 (A:Type') : is_multivector A (fun n => n = 1).
Proof.
  unfold is_multivector, SUBSET, dotdot, dimindex, IN, GSPEC, SETSPEC.
  intros x e. subst x. exists 1%N. split. 2: reflexivity. split. reflexivity.
  destruct (prop_degen (FINITE (@UNIV A))); rewrite H.
  rewrite COND_True. apply CARD_ge_1. rewrite H. exact Logic.I.
  rewrite COND_False. unfold NUMERAL, BIT1. lia.
Qed.

Definition Multivector (A:Type') := subtype (is_multivector0 A).

Definition mk_multivector : forall {N' : Type'}, (N -> Prop) -> Multivector N' := fun A => mk (is_multivector0 A).

Definition dest_multivector : forall {N' : Type'}, (Multivector N') -> N -> Prop := fun A => dest (is_multivector0 A).

Lemma axiom_53 : forall {N' : Type'} (a : Multivector N'), (@mk_multivector N' (@dest_multivector N' a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Lemma axiom_54 : forall {N' : Type'} (r : N -> Prop), ((fun s : N -> Prop => @SUBSET N s (dotdot (NUMERAL (BIT1 0%N)) (@dimindex N' (@UNIV N')))) r) = ((@dest_multivector N' (@mk_multivector N' r)) = r).
Proof. intros A r. apply dest_mk. Qed.
