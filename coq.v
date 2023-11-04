(****************************************************************************)
(* Coq theory for encoding HOL-Light proofs. *)
(****************************************************************************)

Lemma ext_fun {A B} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof. intros fg x. rewrite fg. reflexivity. Qed.

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

Record Type' := { type :> Type; el : type }.

Definition Prop' : Type' := {| type := Prop; el := True |}.
Canonical Prop'.

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

(****************************************************************************)
(* Curryfied versions of some Coq connectives. *)
(****************************************************************************)

Definition imp (p q : Prop) : Prop := p -> q.

Definition ex1 : forall {A : Type'}, (A -> Prop) -> Prop := fun A P => exists! x, P x.

(****************************************************************************)
(* Proof of some HOL-Light rules. *)
(****************************************************************************)

Lemma MK_COMB {a b : Type} {s t : a -> b} {u v : a} (h1 : s = t) (h2 : u = v) : (s u) = (t v).
Proof. rewrite h1, h2. reflexivity. Qed.

Lemma EQ_MP {p q : Prop} (e : p = q) (h : p) : q.
Proof. rewrite <- e. apply h. Qed.

(****************************************************************************)
(* Proof of some natural deduction rules. *)
(****************************************************************************)

Lemma or_intro1 {p:Prop} (h : p) (q:Prop) : p \/ q.
Proof. exact (@or_introl p q h). Qed.

Lemma or_intro2 (p:Prop) {q:Prop} (h : q) : p \/ q.
Proof. exact (@or_intror p q h). Qed.

Lemma or_elim {p q : Prop} (h : p \/ q) {r : Prop} (h1: p -> r) (h2: q -> r) : r.
Proof. exact (@or_ind p q r h1 h2 h). Qed.

Lemma ex_elim {a} {p : a -> Prop} (h1 : exists x, p x) {r : Prop} (h2 : forall x : a, (p x) -> r) : r.
Proof. exact (@ex_ind a p r h2 h1). Qed.

(****************************************************************************)
(* Coq axioms necessary to handle HOL-Light proofs. *)
(****************************************************************************)

Require Import Coq.Logic.ClassicalEpsilon.

Definition ε : forall {A : Type'}, (type A -> Prop) -> type A := fun A P => epsilon (inhabits (el A)) P.

Lemma ε_spec {A : Type'} (P : type A -> Prop) : (exists x, P x) -> P (ε P).
Proof. intro h. unfold ε. apply epsilon_spec. exact h. Qed.

Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.

Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.

Require Import ClassicalFacts.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  apply prop_ext_em_degen.
  unfold prop_extensionality. intros A B [AB BA]. apply prop_ext. exact AB. exact BA.
  intro P. apply classic.
Qed.

Require Import PropExtensionalityFacts.

Lemma is_True P : (P = True) = P.
Proof.
  apply prop_ext.
  intro e. rewrite e. exact I.
  apply PropExt_imp_ProvPropExt.
  intros a b [ab ba]. apply prop_ext. apply ab. apply ba.
Qed.

Lemma is_False P : (P = False) = ~ P.
Proof.
  apply prop_ext; intro h. rewrite h. intro i. exact i.
  apply prop_ext; intro i. apply h. apply i. apply False_rec. exact i.
Qed.

Lemma refl_is_True {A} (x:A) : (x = x) = True.
Proof. rewrite is_True. reflexivity. Qed.

Lemma sym {A} (x y : A) : (x = y) = (y = x).
Proof. apply prop_ext; intro e; symmetry; exact e. Qed.

Lemma True_and_True : (True /\ True) = True.
Proof. rewrite is_True. tauto. Qed.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. reflexivity. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof. intros A P x h. apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h)). Qed.

(****************************************************************************)
(* Proof of mappings from HOL-Light connectives to Coq connectives. *)
(****************************************************************************)

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  intro A. unfold ex1. apply fun_ext; intro P. unfold unique. apply prop_ext.

  intros [x [px u]]. split. apply (ex_intro P x px). intros a b [ha hb].
  transitivity x. symmetry. apply u. exact ha. apply u. exact hb.

  intros [[x px] u]. apply (ex_intro _ x). split. exact px. intros y py. apply u. split.
  exact px. exact py.
Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof. apply prop_ext. intros b p. apply (False_rec p b). intro h. exact (h False). Qed.

Lemma not_def : not = (fun p : Prop => p -> False).
Proof. reflexivity. Qed.

Lemma or_def : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Proof.
  apply fun_ext; intro p; apply fun_ext; intro q. apply prop_ext.
  intros pq r pr qr. destruct pq. apply (pr H). apply (qr H).
  intro h. apply h. intro hp. left. exact hp. intro hq. right. exact hq.
Qed.

Lemma ex_def : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intros [x px] q pq. eapply pq. apply px.
  intro h. apply h. intros x px. apply (ex_intro p x px).
Qed.

Lemma all_def : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Proof.
  intro A. apply fun_ext; intro p. apply prop_ext.
  intro h. apply fun_ext; intro x. apply prop_ext.
  intros _. exact I. intros _. exact (h x).
  intros e x. rewrite e. exact I.
Qed.

Lemma imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Proof.
  apply fun_ext; intro p. apply fun_ext; intro q. apply prop_ext.
  intro pq. apply prop_ext. intros [hp _]. exact hp. intro hp. split. exact hp. apply pq. exact hp.
  intro e. rewrite <- e. intros [_ hq]. exact hq.
Qed.

Lemma and_def : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Proof.
  apply fun_ext; intro p. apply fun_ext; intro q. apply prop_ext.

  intros [hp hq]. apply fun_ext; intro f.
  case (prop_degen p); intro e; subst p.
  case (prop_degen q); intro e; subst q.
  reflexivity.
  exfalso. exact hq.
  exfalso. exact hp.

  intro e. generalize (ext_fun e); clear e; intro e. split.
  rewrite (e (fun p _ => p)). exact I.
  rewrite (e (fun _ q => q)). exact I.
Qed.

Lemma T_def : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Proof. apply prop_ext. reflexivity. intros _; exact I. Qed.

(****************************************************************************)
(* Mapping of HOL-Light type 1 to Coq type unit. *)
(****************************************************************************)

Definition unit' := {| type := unit; el := tt |}.
Canonical unit'.

Definition one_ABS : Prop -> unit := fun _ => tt.

Definition one_REP : unit -> Prop := fun _ => True.

Lemma axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a.
Proof. intro a. destruct a. reflexivity. Qed.

Lemma axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).
Proof. intro r. compute. rewrite (sym True r), is_True. reflexivity. Qed.

Lemma one_def : tt = ε one_REP.
Proof. generalize (ε one_REP). destruct t. reflexivity. Qed.

(****************************************************************************)
(* Mapping of HOL-Light type prod to Coq type prod. *)
(****************************************************************************)

Definition prod' (a b : Type') := {| type := a * b; el := pair (el a) (el b) |}.
Canonical prod'.

Definition mk_pair {A B : Type'} := fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y).

Lemma mk_pair_inj (A B : Type') (x x' : A) (y y' : B) : mk_pair x y = mk_pair x' y' -> x = x' /\ y = y'.
Proof.
  intro e; generalize (ext_fun e); clear e; intro e. generalize (ext_fun (e x)); clear e; intro e.
  generalize (e y); clear e. unfold mk_pair.
  rewrite refl_is_True, refl_is_True, True_and_True, sym, is_True. intro h; exact h.
Qed.

Definition ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B := fun A B f => ε (fun p => f = mk_pair (fst p) (snd p)).

Lemma ABS_prod_mk_pair (A B : Type') (x : A) (y : B) : ABS_prod (mk_pair x y) = (x,y).
Proof.
  unfold ABS_prod. match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  rewrite (surjective_pairing q).
  assert (i : exists q, Q q). exists (x,y). reflexivity.
  generalize (ε_spec Q i); fold q; unfold Q; intro h.
  apply mk_pair_inj in h. destruct h as [h1 h2]. rewrite h1, h2. reflexivity.
Qed.

Lemma ABS_prod_mk_pair_eta (A B : Type') (x : A) (y : B) : ABS_prod (fun a b => mk_pair x y a b) = (x,y).
Proof.
  unfold ABS_prod. match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  rewrite (surjective_pairing q).
  assert (i : exists q, Q q). exists (x,y). reflexivity.
  generalize (ε_spec Q i); fold q; unfold Q; intro h.
  apply mk_pair_inj in h. destruct h as [h1 h2]. rewrite h1, h2. reflexivity.
Qed.

Definition REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop := fun A B p a b => mk_pair (fst p) (snd p) a b.

Lemma pair_def {A B : Type'} : (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Proof. apply fun_ext; intro x; apply fun_ext; intro y. symmetry. apply ABS_prod_mk_pair. Qed.

Lemma FST_def {A B : Type'} : (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Proof.
  apply fun_ext; intros [x y]. simpl.
  match goal with [|- _ = ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i : exists x, Q x). exists x. exists y. reflexivity.
  generalize (ε_spec Q i); fold q; intros [x' h']. inversion h'. reflexivity.
Qed.

Lemma SND_def {A B : Type'} : (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Proof.
  apply fun_ext; intros [x y]. simpl.
  match goal with [|- _ = ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i : exists x, Q x). exists y. exists x. reflexivity.
  generalize (ε_spec Q i); fold q; intros [x' h]. inversion h. reflexivity.
Qed.

Lemma axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.
Proof. intros A B [a b]. apply ABS_prod_mk_pair_eta. Qed.

Lemma axiom_5 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).
Proof.
  intros A B f. simpl. apply prop_ext.
  intros [a [b e]]. subst. rewrite ABS_prod_mk_pair. reflexivity.
  generalize (ABS_prod f); intros [a b] e. subst. exists a. exists b. reflexivity.
Qed.

(****************************************************************************)
(* HOL-Light type ind. *)
(****************************************************************************)

Definition nat' := {| type := nat; el := 0 |}.
Canonical nat'.

Definition ind : Type' := nat'.

Definition ONE_ONE {A B : Type'} := fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2.

Definition ONTO {A B : Type'} := fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x).

Lemma axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Proof. exists S. split. exact eq_add_S. intro h. generalize (h 0). intros [x hx]. discriminate. Qed.

Definition IND_SUC_pred := fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).

Definition IND_SUC := ε IND_SUC_pred.

Lemma not_forall_eq A (P : A -> Prop) : (~ forall x, P x) = exists x, ~ (P x).
Proof. apply prop_ext; intro h. apply not_all_ex_not. exact h. apply ex_not_not_all. exact h. Qed.

Lemma not_exists_eq A (P : A -> Prop) : (~ exists x, P x) = forall x, ~ (P x).
Proof. apply prop_ext; intro h. apply not_ex_all_not. exact h. apply all_not_not_ex. exact h. Qed.

Lemma IND_SUC_ex : exists f, IND_SUC_pred f.
Proof.
  destruct axiom_6 as [f [h1 h2]]. exists f.
  unfold ONTO in h2. rewrite not_forall_eq in h2. destruct h2 as [z h2]. exists z. split.
  intros x y. apply prop_ext. apply h1. intro e. rewrite e. reflexivity.
  rewrite not_exists_eq in h2. intros x e. apply (h2 x). symmetry. exact e.
Qed.

Lemma IND_SUC_prop : IND_SUC_pred IND_SUC.
Proof. unfold IND_SUC. apply ε_spec. apply IND_SUC_ex. Qed.

Lemma IND_SUC_inj : ONE_ONE IND_SUC.
Proof. generalize IND_SUC_prop. intros [z [h1 h2]]. intros x y e. rewrite <- h1. exact e. Qed.

Definition IND_0_pred := fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)).

Definition IND_0 := ε IND_0_pred.

Lemma IND_0_ex : exists z, IND_0_pred z.
Proof. generalize IND_SUC_prop. intros [z [h1 h2]]. exists z. split. exact h1. exact h2. Qed.

Lemma IND_0_prop : IND_0_pred IND_0.
Proof. unfold IND_0. apply ε_spec. apply IND_0_ex. Qed.

Lemma IND_SUC_neq_0 i : IND_SUC i <> IND_0.
Proof. generalize IND_0_prop. intros [h1 h2]. apply h2. Qed.

(****************************************************************************)
(* Mapping of HOL-Light type num to Coq type nat. *)
(****************************************************************************)

Fixpoint dest_num n :=
  match n with
  | 0 => IND_0
  | S p => IND_SUC (dest_num p)
  end.

Lemma dest_num_inj : ONE_ONE dest_num.
Proof.
  intro x. induction x; intro y; destruct y; simpl.
  reflexivity.
  intro e. apply False_ind. eapply IND_SUC_neq_0. symmetry. exact e.
  intro e. apply False_ind. eapply IND_SUC_neq_0. exact e.
  intro e. apply f_equal. apply IHx. apply IND_SUC_inj. exact e.
Qed.

Definition NUM_REP := fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a.

Definition NUM_REP' := fun a : ind => forall P : ind -> Prop, (P IND_0 /\ forall i, P i -> P (IND_SUC i)) -> P a.

Lemma NUM_REP_eq : NUM_REP = NUM_REP'.
Proof.
  apply fun_ext; intro a. apply prop_ext; intros h P.
  intros [p0 ps]. apply h. intros a' [i|i].
    subst a'. exact p0.
    destruct i as [b [e i]]. subst a'. apply ps. exact i.
  intro i. apply h. split.
    apply i. left. reflexivity.
    intros b pb. apply i. right. exists b. split. reflexivity. exact pb.
Qed.

Lemma NUM_REP_0 : NUM_REP IND_0.
Proof. rewrite NUM_REP_eq. intros P [h _]. exact h. Qed.

Lemma NUM_REP_S i : NUM_REP i -> NUM_REP (IND_SUC i).
Proof. rewrite NUM_REP_eq. intros hi P [h0 hS]. apply hS. apply hi. split. exact h0. exact hS. Qed.

Inductive NUM_REP_ID : ind -> Prop :=
  | NUM_REP_ID_0 : NUM_REP_ID IND_0
  | NUM_REP_ID_S i : NUM_REP_ID i -> NUM_REP_ID (IND_SUC i).

Lemma NUM_REP_eq_ID : NUM_REP = NUM_REP_ID.
Proof.
  apply fun_ext; intro i. apply prop_ext.
  rewrite NUM_REP_eq. intro h. apply h. split.
    apply NUM_REP_ID_0.
    intros j hj. apply NUM_REP_ID_S. exact hj.
  induction 1. apply NUM_REP_0. apply NUM_REP_S. assumption.
Qed.

Definition dest_num_img i := exists n, i = dest_num n.

Lemma NUM_REP_eq_dest_num_img : NUM_REP = dest_num_img.
Proof.
  apply fun_ext; intro i. apply prop_ext.
  rewrite NUM_REP_eq_ID. revert i. induction 1.
    exists 0. reflexivity.
    destruct IHNUM_REP_ID as [n hn]. rewrite hn. exists (S n). reflexivity.
  intros [n hn]. subst. induction n. apply NUM_REP_0. apply NUM_REP_S. assumption.
Qed.

Lemma NUM_REP_dest_num k : NUM_REP (dest_num k).
Proof. induction k. apply NUM_REP_0. simpl. apply NUM_REP_S. assumption. Qed.

Definition mk_num_pred i n := i = dest_num n.

Definition mk_num i := ε (mk_num_pred i).

Lemma mk_num_ex i : NUM_REP i -> exists n, mk_num_pred i n.
Proof.
  rewrite NUM_REP_eq_ID. induction 1.
  exists 0. reflexivity.
  destruct IHNUM_REP_ID as [n hn]. exists (S n). unfold mk_num_pred. rewrite hn. reflexivity.
Qed.

Lemma mk_num_prop i : NUM_REP i -> dest_num (mk_num i) = i.
Proof. intro hi. symmetry. apply (ε_spec (mk_num_pred i) (mk_num_ex i hi)). Qed.

Notation dest_num_mk_num := mk_num_prop.

Lemma mk_num_dest_num k : mk_num (dest_num k) = k.
Proof. apply dest_num_inj. apply dest_num_mk_num. apply NUM_REP_dest_num. Qed.

Lemma axiom_7 : forall (a : nat), (mk_num (dest_num a)) = a.
Proof. exact mk_num_dest_num. Qed.

Lemma axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
Proof. intro r. apply prop_ext. apply dest_num_mk_num. intro h. rewrite <- h. apply NUM_REP_dest_num. Qed.

Lemma mk_num_0 : mk_num IND_0 = 0.
Proof.
  unfold mk_num. set (P := mk_num_pred IND_0).
  assert (h: exists n, P n). exists 0. reflexivity.
  generalize (ε_spec P h). set (i := ε P). unfold P, mk_num_pred. intro e.
  apply dest_num_inj. simpl. symmetry. exact e.
Qed.

Lemma _0_def : 0 = (mk_num IND_0).
Proof. symmetry. exact mk_num_0. Qed.

Lemma mk_num_S : forall i, NUM_REP i -> mk_num (IND_SUC i) = S (mk_num i).
Proof.
  intros i hi. rewrite NUM_REP_eq_dest_num_img in hi. destruct hi as [n hn]. rewrite hn, mk_num_dest_num.
  change (mk_num (dest_num (S n)) = S n). apply mk_num_dest_num. 
Qed.

Lemma SUC_def : S = (fun _2104 : nat => mk_num (IND_SUC (dest_num _2104))).
Proof.
  symmetry. apply fun_ext; intro x. rewrite mk_num_S. 2: apply NUM_REP_dest_num.
  apply f_equal. apply axiom_7.
Qed.

(****************************************************************************)
(* Mapping of usual mathematical functions on natural numbers. *)
(****************************************************************************)

Fixpoint BIT0 n :=
  match n with
  | 0 => 0
  | S n => S (S (BIT0 n))
  end.

Lemma BIT0_def : BIT0 =
         (@ε (arr nat nat')
            (fun fn : forall _ : nat, nat =>
               and (@eq nat (fn O) O) (forall n : nat, @eq nat (fn (S n)) (S (S (fn n)))))).
Proof.
  match goal with [|- _ = ε ?x] => set (Q := x) end.
  assert (i : exists q, Q q). exists BIT0. split; reflexivity.
  generalize (ε_spec Q i). intros [h0 hs].
  apply fun_ext; intro n. induction n; simpl.
  rewrite h0. reflexivity. rewrite hs, IHn. reflexivity.
Qed.

Lemma BIT0_is_double : BIT0 = Nat.double.
Proof.
  apply fun_ext; intro n. induction n; simpl. reflexivity. rewrite IHn. unfold Nat.double. simpl.
  rewrite PeanoNat.Nat.add_succ_r. reflexivity.
Qed.

Definition BIT1 := fun _2143 : nat => S (BIT0 _2143).

Lemma PRE_def : pred = (@ε (arr (prod nat (prod nat nat)) (arr nat nat')) (fun PRE' : (prod nat (prod nat nat)) -> nat -> nat' => forall _2151 : prod nat (prod nat nat), ((PRE' _2151 ( 0)) = ( 0)) /\ (forall n : nat, (PRE' _2151 (S n)) = n)) (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ( (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ( (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
  generalize (prod nat (prod nat nat)).
  intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => pred). split; reflexivity.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro n. induction n; simpl.
  rewrite h0. reflexivity. rewrite hs. reflexivity.
Qed.

Lemma add_def : Nat.add = (@ε (arr nat (arr nat (arr nat nat'))) (fun add' : nat -> nat -> nat -> nat => forall _2155 : nat, (forall n : nat, (add' _2155 ( 0) n) = n) /\ (forall m : nat, forall n : nat, (add' _2155 (S m) n) = (S (add' _2155 m n)))) ( (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  generalize ( (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))). intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.add). split; reflexivity.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction x; simpl. rewrite h0. reflexivity. rewrite hs, IHx. reflexivity.
Qed.

Lemma mul_def : Nat.mul = (@ε (arr nat (arr nat (arr nat nat'))) (fun mul' : nat -> nat -> nat -> nat => forall _2186 : nat, (forall n : nat, (mul' _2186 ( 0) n) = ( 0)) /\ (forall m : nat, forall n : nat, (mul' _2186 (S m) n) = (Nat.add (mul' _2186 m n) n))) ( (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  generalize ( (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))). intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.mul). split; simpl. reflexivity.
  intros m n. rewrite PeanoNat.Nat.add_comm. reflexivity.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction x; simpl. rewrite h0. reflexivity. rewrite hs, IHx, PeanoNat.Nat.add_comm. reflexivity.
Qed.

Lemma EXP_def : Nat.pow = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat'))) (fun EXP' : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _2224 : prod nat (prod nat nat), (forall m : nat, EXP' _2224 m 0 = BIT1 0) /\ (forall m : nat, forall n : nat, (EXP' _2224 m (S n)) = (Nat.mul m (EXP' _2224 m n)))) (@pair nat (prod nat nat) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))) (@pair nat nat (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof.
  generalize (@pair nat (prod nat nat) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))) (@pair nat nat (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))); generalize (@prod nat (prod nat nat)); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.pow). split; simpl; intro x; reflexivity.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction y; simpl. rewrite h0. reflexivity. rewrite hs, IHy. reflexivity.
Qed.

Require Import Lia.

Lemma le_def : le = (@ε (arr (prod nat nat) (arr nat (arr nat Prop'))) (fun le' : (prod nat nat) -> nat -> nat -> Prop => forall _2241 : prod nat nat, (forall m : nat, (le' _2241 m ( 0)) = (m = ( 0))) /\ (forall m : nat, forall n : nat, (le' _2241 m (S n)) = ((m = (S n)) \/ (le' _2241 m n)))) (@pair nat nat ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))))).
Proof.
  generalize (@pair nat nat ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))); generalize (prod nat nat); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => le). split; simpl; intro x.
  apply prop_ext; intro h.
    symmetry. apply Arith_prebase.le_n_0_eq_stt. exact h.
    rewrite h. reflexivity.
  intro n. apply prop_ext; lia.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  apply prop_ext.
  induction 1.
    induction x. rewrite h0. reflexivity. rewrite hs. left. reflexivity.
    rewrite hs. right. assumption.
  induction y.
    rewrite h0. intro h. rewrite h. reflexivity.
    rewrite hs. intros [h|h]. rewrite h. reflexivity. apply le_S. apply IHy. exact h.
Qed.

Lemma le_eq_lt x y : x <= y -> x = y \/ x < y.
Proof. lia. Qed.

Lemma lt_def : lt = (@ε (arr nat (arr nat (arr nat Prop'))) (fun lt : nat -> nat -> nat -> Prop => forall _2248 : nat, (forall m : nat, (lt _2248 m ( 0)) = False) /\ (forall m : nat, forall n : nat, (lt _2248 m (S n)) = ((m = n) \/ (lt _2248 m n)))) ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))).
Proof.
  generalize ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))); intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => lt). split; intro x. apply prop_ext; lia. intro n. apply prop_ext; lia.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  apply prop_ext.
    induction y. lia. rewrite hs. intro h. apply le_S_n in h. apply le_eq_lt in h. destruct h as [h|h].
    left. exact h. right. apply IHy. exact h.
  induction y.
    rewrite h0. lia.
    rewrite hs. intros [h|h]. rewrite h. unfold lt. reflexivity. generalize (IHy h). lia.
Qed.

Lemma ge_def : ge = (fun _2249 : nat => fun _2250 : nat => le _2250 _2249).
Proof. apply fun_ext; intro x. apply fun_ext; intro y. reflexivity. Qed.

Lemma gt_def : gt = (fun _2261 : nat => fun _2262 : nat => lt _2262 _2261).
Proof. apply fun_ext; intro x. apply fun_ext; intro y. reflexivity. Qed.

Definition COND {A : Type'} := fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2)).

Lemma COND_True (A : Type') (x y : A) : COND True x y = x.
Proof.
  unfold COND. match goal with [|- ε ?x = _] => set (Q := x) end.
  assert (i : exists q, Q q). exists x. split; intro h. reflexivity. apply False_rec. rewrite <- h. exact I.
  generalize (ε_spec Q i). intros [h1 h2]. apply h1. reflexivity.
Qed.

Lemma COND_False (A : Type') (x y : A) : COND False x y = y.
Proof.
  unfold COND. match goal with [|- ε ?x = _] => set (Q := x) end.
  assert (i : exists q, Q q). exists y. split; intro h. apply False_rec. rewrite h. exact I. reflexivity.
  generalize (ε_spec Q i). intros [h1 h2]. apply h2. reflexivity.
Qed.

Lemma _0_le_nat_is_True y : (0 <= y) = True.
Proof. apply prop_ext; intro h. exact I. lia. Qed.

Lemma S_le_0_is_False y : (S y <= 0) = False.
Proof. apply prop_ext; lia. Qed.

Lemma S_eq_0_is_False y : (S y = 0) = False.
Proof. apply prop_ext; lia. Qed.

Lemma S_le_S x y : (S x <= S y) = (x <= y).
Proof. apply prop_ext; lia. Qed.

Lemma MAX_def : max = (fun _2273 : nat => fun _2274 : nat => @COND nat (le _2273 _2274) _2274 _2273).
Proof.
  apply fun_ext; intro x. apply fun_ext. induction x; intro y; induction y.
  rewrite _0_le_nat_is_True, COND_True. reflexivity.
  simpl. rewrite _0_le_nat_is_True, COND_True. reflexivity.
  rewrite S_le_0_is_False, COND_False. reflexivity.
  simpl. rewrite IHx, S_le_S. destruct (prop_degen (x <= y)) as [h|h]; rewrite h.
  rewrite! COND_True. reflexivity. rewrite! COND_False. reflexivity.
Qed.

Lemma MIN_def : min = (fun _2285 : nat => fun _2286 : nat => @COND nat (le _2285 _2286) _2285 _2286).
Proof.
  apply fun_ext; intro x. apply fun_ext. induction x; intro y; induction y.
  rewrite _0_le_nat_is_True, COND_True. reflexivity.
  simpl. rewrite _0_le_nat_is_True, COND_True. reflexivity.
  rewrite S_le_0_is_False, COND_False. reflexivity.
  simpl. rewrite IHx, S_le_S. destruct (prop_degen (x <= y)) as [h|h]; rewrite h.
  rewrite! COND_True. reflexivity. rewrite! COND_False. reflexivity.
Qed.

Lemma minus_def : Nat.sub = (@ε (arr nat (arr nat (arr nat nat'))) (fun pair' : nat -> nat -> nat -> nat => forall _2766 : nat, (forall m : nat, (pair' _2766 m ( 0)) = m) /\ (forall m : nat, forall n : nat, (pair' _2766 m (S n)) = (Nat.pred (pair' _2766 m n)))) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  generalize ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))); intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => minus). split; lia.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext. induction x.
  intro y. induction y; simpl.
  rewrite h0. reflexivity. rewrite hs, <- IHy. reflexivity.
  intro y. induction y. rewrite h0. reflexivity. rewrite hs, <- IHy. lia.
Qed.

Lemma FACT_def : Factorial.fact = (@ε (arr (prod nat (prod nat (prod nat nat))) (arr nat nat')) (fun FACT' : (prod nat (prod nat (prod nat nat))) -> nat -> nat => forall _2944 : prod nat (prod nat (prod nat nat)), ((FACT' _2944 ( 0)) = ( (BIT1 0))) /\ (forall n : nat, (FACT' _2944 (S n)) = (Nat.mul (S n) (FACT' _2944 n)))) (@pair nat (prod nat (prod nat nat)) ( (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ( (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Proof.
  generalize (@pair nat (prod nat (prod nat nat)) ( (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ( (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))); generalize (prod nat (prod nat (prod nat nat))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Factorial.fact). split; reflexivity.
  generalize (ε_spec Q i a). intros [h0 hs].
  apply fun_ext; intro x. induction x. rewrite h0. reflexivity. rewrite hs, <- IHx. reflexivity.
Qed.

Lemma add_sub a b : a + b - a = b.
Proof. lia. Qed.

Lemma swap_add_sub a a' b : a' <= a -> a + b - a' = a - a' + b.
Proof. lia. Qed.

Lemma divmod_unicity k k' q r r' : r < q -> r' < q -> k * q + r = k' * q + r' -> k = k' /\ r = r'.
Proof.
  intros h h' e.
  destruct (Compare_dec.lt_eq_lt_dec k k') as [[i|i]|i].
  apply False_rec.
  assert (e2 : k * q + r - k * q = k' * q + r' - k * q). lia.
  rewrite add_sub, swap_add_sub, <- PeanoNat.Nat.mul_sub_distr_r in e2. nia. nia. lia.
  apply False_rec.
  assert (e2 : k * q + r - k' * q = k' * q + r' - k' * q). lia.
  rewrite add_sub, swap_add_sub, <- PeanoNat.Nat.mul_sub_distr_r in e2. nia. nia.
Qed.

Lemma DIV_def : Nat.div = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat'))) (fun q : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3086 : prod nat (prod nat nat), exists r : nat -> nat -> nat, forall m : nat, forall n : nat, @COND Prop (n = ( 0)) (((q _3086 m n) = ( 0)) /\ ((r m n) = m)) ((m = (Nat.add (Nat.mul (q _3086 m n) n) (r m n))) /\ (lt (r m n) n))) (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))); generalize (prod nat (prod nat (prod nat nat))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.div). intro x. exists Nat.modulo. intros m n.
  destruct (prop_degen (n=0)) as [h|h]; rewrite h.
  rewrite COND_True. rewrite is_True in h. rewrite h. simpl. split; reflexivity.
  rewrite COND_False. rewrite (PeanoNat.Nat.div_mod_eq m n) at 1. split. lia.
  rewrite is_False in h. apply PeanoNat.Nat.mod_bound_pos. lia. lia.
  generalize (ε_spec Q i a). intros [mod h].
  apply fun_ext; intro x. apply fun_ext; intro y.
  revert x. induction y.
  intro x. generalize (h x 0). rewrite refl_is_True, COND_True. intros [h1 h2].
  rewrite h1. reflexivity.
  intro x. generalize (h x (S y)). rewrite S_eq_0_is_False, COND_False. intros [h1 h2].
  simpl. generalize (Coq.Arith.PeanoNat.Nat.divmod_spec x y 0 y (le_n y)).
  destruct (Nat.divmod x y 0 y) as [q r]. simpl.
  rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_r, !PeanoNat.Nat.add_0_r. rewrite h1 at 1.
  intros [i1 i2]. assert (h3 : y - r < S y). lia.
  assert (e : q * S y = q + y * q). lia. rewrite <- e in i1.
  generalize (divmod_unicity (ε Q a x (S y)) q (S y) (mod x (S y)) (y - r) h2 h3 i1).
  intros [j1 j2]. symmetry. exact j1.
Qed.

Lemma MOD_def : Nat.modulo = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat'))) (fun r : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3087 : prod nat (prod nat nat), forall m : nat, forall n : nat, @COND Prop (n = ( 0)) (((Nat.div m n) = ( 0)) /\ ((r _3087 m n) = m)) ((m = (Nat.add (Nat.mul (Nat.div m n) n) (r _3087 m n))) /\ (lt (r _3087 m n) n))) (@pair nat (prod nat nat) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (@pair nat (prod nat nat) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ( (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))); generalize (prod nat (prod nat (prod nat nat))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.modulo). intros x m n. destruct n.
  rewrite refl_is_True, COND_True. split; reflexivity.
  rewrite S_eq_0_is_False, COND_False. split.
  rewrite PeanoNat.Nat.mul_comm. apply Coq.Arith.PeanoNat.Nat.div_mod_eq.
  apply PeanoNat.Nat.mod_bound_pos. lia. lia.
  generalize (ε_spec Q i a). intro h.
  apply fun_ext; intro x. apply fun_ext; intro y.
  revert x. induction y.
  intro x. generalize (h x 0). rewrite refl_is_True, COND_True. intros [h1 h2]. symmetry. exact h2.
  intro x. generalize (h x (S y)). rewrite S_eq_0_is_False, COND_False. intros [h1 h2].
  generalize (Coq.Arith.PeanoNat.Nat.divmod_spec x y 0 y (le_n y)).
  unfold Nat.modulo. destruct (Nat.divmod x y 0 y) as [q r].
  rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_r, !PeanoNat.Nat.add_0_r. rewrite h1 at 1.
  intros [i1 i2]. assert (h3 : y - r < S y). lia.
  rewrite (PeanoNat.Nat.mul_comm (S y) q) in i1.
  generalize (divmod_unicity (Nat.div x (S y)) q (S y) (ε Q a x (S y)) (y - r) h2 h3 i1).
  intros [j1 j2]. symmetry. exact j2.
Qed.

Import PeanoNat.Nat Private_Parity.

Lemma Even_or_Odd x : Even x \/ Odd x.
Proof.
  rewrite (div_mod_eq x 2). assert (h1: 0 <= x). lia. assert (h2: 0 < 2). lia.
  generalize (mod_bound_pos x 2 h1 h2). generalize (x mod 2). intro n. destruct n; intro h.
  left. exists (x / 2). lia. destruct n. right. exists (x / 2). reflexivity. lia.
Qed.

Lemma not_Even_is_Odd x : (~Even x) = Odd x.
Proof.
  apply prop_ext; intro h; generalize (Even_or_Odd x); intros [i|i].
  apply False_rec. exact (h i). exact i. destruct h as [k hk]. destruct i as [l hl]. lia.
  intros [k hk]. destruct i as [l hl]. lia.
Qed.

Lemma not_Odd_is_Even x : (~Odd x) = Even x.
Proof.
  apply prop_ext; intro h; generalize (Even_or_Odd x); intros [i|i].
  exact i. apply False_rec. exact (h i). destruct h as [k hk]. intro j. destruct j as [l hl]. lia.
  intros [k hk]. destruct h as [l hl]. lia.
Qed.

Lemma Even_S x : Even (S x) = Odd x.
Proof.
  apply prop_ext; intros [k hk].
  rewrite <- not_Even_is_Odd. intros [l hl]. lia.
  rewrite <- not_Odd_is_Even. intros [l hl]. lia.
Qed.

Lemma Odd_S x : Odd (S x) = Even x.
Proof.
  apply prop_ext; intros [k hk].
  rewrite <- not_Odd_is_Even. intros [l hl]. lia.
  rewrite <- not_Even_is_Odd. intros [l hl]. lia.
Qed.

Lemma EVEN_def : Even = (@ε (arr (prod nat (prod nat (prod nat nat))) (arr nat Prop')) (fun EVEN' : (prod nat (prod nat (prod nat nat))) -> nat -> Prop => forall _2603 : prod nat (prod nat (prod nat nat)), ((EVEN' _2603 (0)) = True) /\ (forall n : nat, (EVEN' _2603 (S n)) = (~ (EVEN' _2603 n)))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))).
Proof.
  generalize (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))); generalize (prod nat (prod nat (prod nat nat))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Even). intro x. split.
  rewrite is_True. exact Even_0. intro n. rewrite not_Even_is_Odd. apply Even_S.
  generalize (ε_spec Q i a). intros [h1 h2].
  apply fun_ext; intro x. induction x.
  apply prop_ext; intro h. rewrite h1. exact I. exact Even_0.
  rewrite h2, <- IHx, not_Even_is_Odd. apply Even_S.
Qed.

Lemma ODD_def : Odd = (@ε (arr (prod nat (prod nat nat)) (arr nat Prop')) (fun ODD' : (prod nat (prod nat nat)) -> nat -> Prop => forall _2607 : prod nat (prod nat nat), ((ODD' _2607 (0)) = False) /\ (forall n : nat, (ODD' _2607 (S n)) = (~ (ODD' _2607 n)))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))); generalize (prod nat (prod nat (prod nat nat))); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Odd). intro x. split.
  rewrite is_False. exact Odd_0. intro n. rewrite not_Odd_is_Even. apply Odd_S.
  generalize (ε_spec Q i a). intros [h1 h2].
  apply fun_ext; intro x. induction x.
  apply prop_ext; intro h. rewrite h1. apply Odd_0. exact h.
  apply False_rec. rewrite <- h1. exact h.
  rewrite h2, <- IHx, not_Odd_is_Even. apply Odd_S.
Qed.
