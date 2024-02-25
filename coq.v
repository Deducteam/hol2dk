(****************************************************************************)
(* Coq theory for encoding HOL-Light proofs. *)
(****************************************************************************)

Lemma ext_fun {A B} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof. intros fg x. rewrite fg. reflexivity. Qed.

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

Record Type' := { type :> Type; el : type }.

Definition bool' := {| type := bool; el := true |}.
Canonical bool'.

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

Lemma MK_COMB {a b : Type} {s t : a -> b} {u v : a} (h1 : s = t) (h2 : u = v)
  : (s u) = (t v).
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

Lemma ex_elim {a} {p : a -> Prop}
  (h1 : exists x, p x) {r : Prop} (h2 : forall x : a, (p x) -> r) : r.
Proof. exact (@ex_ind a p r h2 h1). Qed.

(****************************************************************************)
(* Coq axioms necessary to handle HOL-Light proofs. *)
(****************************************************************************)

Require Import Coq.Logic.ClassicalEpsilon.

Definition ε : forall {A : Type'}, (type A -> Prop) -> type A :=
  fun A P => epsilon (inhabits (el A)) P.

Lemma ε_spec {A : Type'} {P : type A -> Prop} : (exists x, P x) -> P (ε P).
Proof. intro h. unfold ε. apply epsilon_spec. exact h. Qed.

Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.

Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.

Require Import ClassicalFacts.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  apply prop_ext_em_degen. unfold prop_extensionality. intros A B [AB BA].
  apply prop_ext. exact AB. exact BA.
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

Lemma not_forall_eq A (P : A -> Prop) : (~ forall x, P x) = exists x, ~ (P x).
Proof.
  apply prop_ext; intro h. apply not_all_ex_not. exact h.
  apply ex_not_not_all. exact h.
Qed.

Lemma not_exists_eq A (P : A -> Prop) : (~ exists x, P x) = forall x, ~ (P x).
Proof.
  apply prop_ext; intro h. apply not_ex_all_not. exact h.
  apply all_not_not_ex. exact h.
Qed.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. reflexivity. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof.
  intros A P x h. apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h)).
Qed.

(****************************************************************************)
(* Proof of mappings from HOL-Light connectives to Coq connectives. *)
(****************************************************************************)

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  intro A. unfold ex1. apply fun_ext; intro P. unfold unique. apply prop_ext.

  intros [x [px u]]. split. apply (ex_intro P x px). intros a b [ha hb].
  transitivity x. symmetry. apply u. exact ha. apply u. exact hb.

  intros [[x px] u]. apply (ex_intro _ x). split. exact px. intros y py.
  apply u. split. exact px. exact py.
Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof.
  apply prop_ext. intros b p. apply (False_rec p b). intro h. exact (h False).
Qed.

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
  intro pq. apply prop_ext. intros [hp _]. exact hp. intro hp.
  split. exact hp. apply pq. exact hp.
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

Definition mk_pair {A B : Type'} :=
  fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y).

Lemma mk_pair_inj (A B : Type') (x x' : A) (y y' : B) :
  mk_pair x y = mk_pair x' y' -> x = x' /\ y = y'.
Proof.
  intro e; generalize (ext_fun e); clear e; intro e.
  generalize (ext_fun (e x)); clear e; intro e.
  generalize (e y); clear e. unfold mk_pair.
  rewrite refl_is_True, refl_is_True, True_and_True, sym, is_True.
  intro h; exact h.
Qed.

Definition ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B :=
  fun A B f => ε (fun p => f = mk_pair (fst p) (snd p)).

Lemma ABS_prod_mk_pair (A B : Type') (x : A) (y : B) :
  ABS_prod (mk_pair x y) = (x,y).
Proof.
  unfold ABS_prod.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  rewrite (surjective_pairing q).
  assert (i : exists q, Q q). exists (x,y). reflexivity.
  generalize (ε_spec i); fold q; unfold Q; intro h.
  apply mk_pair_inj in h. destruct h as [h1 h2]. rewrite h1, h2. reflexivity.
Qed.

Lemma ABS_prod_mk_pair_eta (A B : Type') (x : A) (y : B) :
  ABS_prod (fun a b => mk_pair x y a b) = (x,y).
Proof.
  unfold ABS_prod.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  rewrite (surjective_pairing q).
  assert (i : exists q, Q q). exists (x,y). reflexivity.
  generalize (ε_spec i); fold q; unfold Q; intro h.
  apply mk_pair_inj in h. destruct h as [h1 h2]. rewrite h1, h2. reflexivity.
Qed.

Definition REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop :=
  fun A B p a b => mk_pair (fst p) (snd p) a b.

Lemma pair_def {A B : Type'} : (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Proof.
  apply fun_ext; intro x; apply fun_ext; intro y. symmetry.
  apply ABS_prod_mk_pair.
Qed.

Lemma FST_def {A B : Type'} : (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Proof.
  apply fun_ext; intros [x y]. simpl.
  match goal with [|- _ = ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i : exists x, Q x). exists x. exists y. reflexivity.
  generalize (ε_spec i); fold q; intros [x' h']. inversion h'. reflexivity.
Qed.

Lemma SND_def {A B : Type'} : (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Proof.
  apply fun_ext; intros [x y]. simpl.
  match goal with [|- _ = ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i : exists x, Q x). exists y. exists x. reflexivity.
  generalize (ε_spec i); fold q; intros [x' h]. inversion h. reflexivity.
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
(* HOL-Light infinite type ind. *)
(****************************************************************************)

Definition nat' := {| type := nat; el := 0 |}.
Canonical nat'.

Definition ind : Type' := nat'.

Definition ONE_ONE {A B : Type'} := fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2.

Definition ONTO {A B : Type'} := fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x).

Lemma axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Proof.
  exists S. split. exact eq_add_S. intro h. generalize (h 0). intros [x hx].
  discriminate.
Qed.

Definition IND_SUC_pred := fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).

Definition IND_SUC := ε IND_SUC_pred.

Lemma IND_SUC_ex : exists f, IND_SUC_pred f.
Proof.
  destruct axiom_6 as [f [h1 h2]]. exists f.
  unfold ONTO in h2. rewrite not_forall_eq in h2. destruct h2 as [z h2]. exists z.
  split.
  intros x y. apply prop_ext. apply h1. intro e. rewrite e. reflexivity.
  rewrite not_exists_eq in h2. intros x e. apply (h2 x). symmetry. exact e.
Qed.

Lemma IND_SUC_prop : IND_SUC_pred IND_SUC.
Proof. unfold IND_SUC. apply ε_spec. apply IND_SUC_ex. Qed.

Lemma IND_SUC_inj : ONE_ONE IND_SUC.
Proof.
  generalize IND_SUC_prop. intros [z [h1 h2]]. intros x y e. rewrite <- h1.
  exact e.
Qed.

Definition IND_0_pred := fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)).

Definition IND_0 := ε IND_0_pred.

Lemma IND_0_ex : exists z, IND_0_pred z.
Proof.
  generalize IND_SUC_prop. intros [z [h1 h2]]. exists z. split. exact h1. exact h2.
Qed.

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
Proof.
  rewrite NUM_REP_eq. intros hi P [h0 hS]. apply hS. apply hi.
  split. exact h0. exact hS.
Qed.

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
  intros [n hn]. subst. induction n. apply NUM_REP_0. apply NUM_REP_S.
    assumption.
Qed.

Lemma NUM_REP_dest_num k : NUM_REP (dest_num k).
Proof. induction k. apply NUM_REP_0. simpl. apply NUM_REP_S. assumption. Qed.

Definition mk_num_pred i n := i = dest_num n.

Definition mk_num i := ε (mk_num_pred i).

Lemma mk_num_ex i : NUM_REP i -> exists n, mk_num_pred i n.
Proof.
  rewrite NUM_REP_eq_ID. induction 1.
  exists 0. reflexivity.
  destruct IHNUM_REP_ID as [n hn]. exists (S n). unfold mk_num_pred. rewrite hn.
  reflexivity.
Qed.

Lemma mk_num_prop i : NUM_REP i -> dest_num (mk_num i) = i.
Proof. intro hi. symmetry. apply (ε_spec (mk_num_ex i hi)). Qed.

Notation dest_num_mk_num := mk_num_prop.

Lemma mk_num_dest_num k : mk_num (dest_num k) = k.
Proof. apply dest_num_inj. apply dest_num_mk_num. apply NUM_REP_dest_num. Qed.

Lemma axiom_7 : forall (a : nat), (mk_num (dest_num a)) = a.
Proof. exact mk_num_dest_num. Qed.

Lemma axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
Proof.
  intro r. apply prop_ext. apply dest_num_mk_num. intro h. rewrite <- h.
  apply NUM_REP_dest_num.
Qed.

Lemma mk_num_0 : mk_num IND_0 = 0.
Proof.
  unfold mk_num. set (P := mk_num_pred IND_0).
  assert (h: exists n, P n). exists 0. reflexivity.
  generalize (ε_spec h). set (i := ε P). unfold P, mk_num_pred. intro e.
  apply dest_num_inj. simpl. symmetry. exact e.
Qed.

Lemma _0_def : 0 = (mk_num IND_0).
Proof. symmetry. exact mk_num_0. Qed.

Lemma mk_num_S : forall i, NUM_REP i -> mk_num (IND_SUC i) = S (mk_num i).
Proof.
  intros i hi. rewrite NUM_REP_eq_dest_num_img in hi. destruct hi as [n hn].
  rewrite hn, mk_num_dest_num.
  change (mk_num (dest_num (S n)) = S n). apply mk_num_dest_num. 
Qed.

Lemma SUC_def : S = (fun _2104 : nat => mk_num (IND_SUC (dest_num _2104))).
Proof.
  symmetry. apply fun_ext; intro x. rewrite mk_num_S. 2: apply NUM_REP_dest_num.
  apply f_equal. apply axiom_7.
Qed.

(****************************************************************************)
(* Useful lemmas on booleans and natural numbers. *)
(****************************************************************************)

Require Import Lia PeanoNat. Import Nat.

Lemma eq_false_negb_true b : b = false -> negb b = true.
Proof. intro e. subst. reflexivity. Qed.

Lemma plus_1_minus_1 x : x + 1 - 1 = x.
Proof. lia. Qed.

Lemma S_minus_1 x : S x - 1 = x.
Proof. lia. Qed.

Lemma add_sub a b : a + b - a = b.
Proof. lia. Qed.

Lemma swap_add_sub a a' b : a' <= a -> a + b - a' = a - a' + b.
Proof. lia. Qed.

Lemma le_eq_lt x y : x <= y -> x = y \/ x < y.
Proof. lia. Qed.

Lemma ge_is_add {a b} : a >= b -> exists c, a = b + c.
Proof. intro h. exists (a - b). lia. Qed.

Lemma _0_le_nat_is_True y : (0 <= y) = True.
Proof. apply prop_ext; intro h. exact I. lia. Qed.

Lemma S_le_0_is_False y : (S y <= 0) = False.
Proof. apply prop_ext; lia. Qed.

Lemma S_eq_0_is_False y : (S y = 0) = False.
Proof. apply prop_ext; lia. Qed.

Lemma S_le_S x y : (S x <= S y) = (x <= y).
Proof. apply prop_ext; lia. Qed.

Lemma DIV_MULT m n : m <> 0 -> (m * n) / m = n.
Proof. (*thm_170547*) intro h. rewrite mul_comm. apply div_mul. exact h. Qed.

Lemma divmod_unicity k k' q r r' :
  r < q -> r' < q -> k * q + r = k' * q + r' -> k = k' /\ r = r'.
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

Lemma pow_add {x y z} : x ^ (y + z) = (x ^ y) * (x ^ z).
Proof. induction y. simpl. lia. simpl. rewrite IHy. lia. Qed.

(****************************************************************************)
(* Mapping of usual mathematical functions on natural numbers. *)
(****************************************************************************)

Definition NUMERAL (x : nat) := x.

Fixpoint BIT0 n :=
  match n with
  | 0 => 0
  | S n => S (S (BIT0 n))
  end.

Lemma BIT0_def : BIT0 =
         (@ε (arr nat nat')
            (fun fn : forall _ : nat, nat =>
               and (@Logic.eq nat (fn O) O)
                 (forall n : nat, @Logic.eq nat (fn (S n)) (S (S (fn n)))))).
Proof.
  match goal with [|- _ = ε ?x] => set (Q := x) end.
  assert (i : exists q, Q q). exists BIT0. split; reflexivity.
  generalize (ε_spec i). intros [h0 hs].
  apply fun_ext; intro n. induction n; simpl.
  rewrite h0. reflexivity. rewrite hs, IHn. reflexivity.
Qed.

Lemma BIT0_is_double : BIT0 = Nat.double.
Proof.
  apply fun_ext; intro n. induction n; simpl. reflexivity. rewrite IHn.
  unfold Nat.double. simpl. rewrite PeanoNat.Nat.add_succ_r. reflexivity.
Qed.

Definition BIT1 := fun _2143 : nat => S (BIT0 _2143).

Lemma PRE_def : pred = (@ε (arr (prod nat (prod nat nat)) (arr nat nat')) (fun PRE' : (prod nat (prod nat nat)) -> nat -> nat' => forall _2151 : prod nat (prod nat nat), ((PRE' _2151 ( 0)) = ( 0)) /\ (forall n : nat, (PRE' _2151 (S n)) = n)) (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ( (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (@pair nat (prod nat nat) ( (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ( (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ( (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))).
  generalize (prod nat (prod nat nat)).
  intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => pred). split; reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro n. induction n; simpl.
  rewrite h0. reflexivity. rewrite hs. reflexivity.
Qed.

Lemma add_def : Nat.add = (@ε (arr nat (arr nat (arr nat nat'))) (fun add' : nat -> nat -> nat -> nat => forall _2155 : nat, (forall n : nat, (add' _2155 ( 0) n) = n) /\ (forall m : nat, forall n : nat, (add' _2155 (S m) n) = (S (add' _2155 m n)))) ( (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  generalize ( (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))). intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.add). split; reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction x; simpl. rewrite h0. reflexivity. rewrite hs, IHx. reflexivity.
Qed.

Lemma mul_def : Nat.mul = (@ε (arr nat (arr nat (arr nat nat'))) (fun mul' : nat -> nat -> nat -> nat => forall _2186 : nat, (forall n : nat, (mul' _2186 ( 0) n) = ( 0)) /\ (forall m : nat, forall n : nat, (mul' _2186 (S m) n) = (Nat.add (mul' _2186 m n) n))) ( (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  generalize ( (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))). intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.mul). split; simpl. reflexivity.
  intros m n. rewrite PeanoNat.Nat.add_comm. reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction x; simpl. rewrite h0. reflexivity. rewrite hs, IHx, PeanoNat.Nat.add_comm. reflexivity.
Qed.

Lemma EXP_def : Nat.pow = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat'))) (fun EXP' : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _2224 : prod nat (prod nat nat), (forall m : nat, EXP' _2224 m 0 = BIT1 0) /\ (forall m : nat, forall n : nat, (EXP' _2224 m (S n)) = (Nat.mul m (EXP' _2224 m n)))) (@pair nat (prod nat nat) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))) (@pair nat nat (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof.
  generalize (@pair nat (prod nat nat) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))) (@pair nat nat (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))); generalize (@prod nat (prod nat nat)); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => Nat.pow). split; simpl; intro x; reflexivity.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  induction y; simpl. rewrite h0. reflexivity. rewrite hs, IHy. reflexivity.
Qed.

Lemma le_def : le = (@ε (arr (prod nat nat) (arr nat (arr nat Prop'))) (fun le' : (prod nat nat) -> nat -> nat -> Prop => forall _2241 : prod nat nat, (forall m : nat, (le' _2241 m ( 0)) = (m = ( 0))) /\ (forall m : nat, forall n : nat, (le' _2241 m (S n)) = ((m = (S n)) \/ (le' _2241 m n)))) (@pair nat nat ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))))).
Proof.
  generalize (@pair nat nat ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) ( (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))); generalize (prod nat nat); intros A a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => le). split; simpl; intro x.
  apply prop_ext; intro h.
    symmetry. apply Arith_base.le_n_0_eq_stt. exact h.
    rewrite h. reflexivity.
  intro n. apply prop_ext; lia.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  apply prop_ext.
  induction 1.
    induction x. rewrite h0. reflexivity. rewrite hs. left. reflexivity.
    rewrite hs. right. assumption.
  induction y.
    rewrite h0. intro h. rewrite h. reflexivity.
    rewrite hs. intros [h|h]. rewrite h. reflexivity. apply le_S. apply IHy.
    exact h.
Qed.

Lemma lt_def : lt = (@ε (arr nat (arr nat (arr nat Prop'))) (fun lt : nat -> nat -> nat -> Prop => forall _2248 : nat, (forall m : nat, (lt _2248 m ( 0)) = False) /\ (forall m : nat, forall n : nat, (lt _2248 m (S n)) = ((m = n) \/ (lt _2248 m n)))) ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))).
Proof.
  generalize ( (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))); intro a.
  match goal with [|- _ = ε ?x _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => lt). split; intro x. apply prop_ext; lia. intro n. apply prop_ext; lia.
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. apply fun_ext; intro y.
  apply prop_ext.
  induction y. lia. rewrite hs. intro h. apply le_S_n in h.
    apply le_eq_lt in h. destruct h as [h|h].
    left. exact h. right. apply IHy. exact h.
  induction y.
    rewrite h0. lia.
    rewrite hs. intros [h|h]. rewrite h. unfold lt. lia. generalize (IHy h).
    lia.
Qed.

Lemma ge_def : ge = (fun _2249 : nat => fun _2250 : nat => le _2250 _2249).
Proof. apply fun_ext; intro x. apply fun_ext; intro y. reflexivity. Qed.

Lemma gt_def : gt = (fun _2261 : nat => fun _2262 : nat => lt _2262 _2261).
Proof. apply fun_ext; intro x. apply fun_ext; intro y. reflexivity. Qed.

Definition COND {A : Type'} := fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2)).

Lemma COND_True (A : Type') (x y : A) : COND True x y = x.
Proof.
  unfold COND. match goal with [|- ε ?x = _] => set (Q := x) end.
  assert (i : exists q, Q q). exists x. split; intro h.
  reflexivity. apply False_rec. rewrite <- h. exact I.
  generalize (ε_spec i). intros [h1 h2]. apply h1. reflexivity.
Qed.

Lemma COND_False (A : Type') (x y : A) : COND False x y = y.
Proof.
  unfold COND. match goal with [|- ε ?x = _] => set (Q := x) end.
  assert (i : exists q, Q q). exists y. split; intro h. apply False_rec.
  rewrite h. exact I. reflexivity.
  generalize (ε_spec i). intros [h1 h2]. apply h2. reflexivity.
Qed.

Lemma MAX_def : max = (fun _2273 : nat => fun _2274 : nat => @COND nat (Peano.le _2273 _2274) _2274 _2273).
Proof.
  apply fun_ext; intro x. apply fun_ext. induction x; intro y; induction y.
  rewrite _0_le_nat_is_True, COND_True. reflexivity.
  simpl. rewrite _0_le_nat_is_True, COND_True. reflexivity.
  rewrite S_le_0_is_False, COND_False. reflexivity.
  simpl. rewrite IHx, S_le_S. destruct (prop_degen (x <= y)) as [h|h]; rewrite h.
  rewrite! COND_True. reflexivity. rewrite! COND_False. reflexivity.
Qed.

Lemma MIN_def : min = (fun _2285 : nat => fun _2286 : nat => @COND nat (Peano.le _2285 _2286) _2285 _2286).
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
  generalize (ε_spec i a). intros [h0 hs].
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
  generalize (ε_spec i a). intros [h0 hs].
  apply fun_ext; intro x. induction x. rewrite h0. reflexivity. rewrite hs, <- IHx. reflexivity.
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
  generalize (ε_spec i a). intros [mod' h].
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
  generalize (divmod_unicity (ε Q a x (S y)) q (S y) (mod' x (S y)) (y - r) h2 h3 i1).
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
  generalize (ε_spec i a). intro h.
  apply fun_ext; intro x. apply fun_ext; intro y.
  revert x. induction y.
  intro x. generalize (h x 0). rewrite refl_is_True, COND_True. intros [h1 h2].
  symmetry. exact h2.
  intro x. generalize (h x (S y)). rewrite S_eq_0_is_False, COND_False.
  intros [h1 h2].
  generalize (Coq.Arith.PeanoNat.Nat.divmod_spec x y 0 y (le_n y)).
  unfold Nat.modulo. destruct (Nat.divmod x y 0 y) as [q r].
  rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_r, !PeanoNat.Nat.add_0_r.
  rewrite h1 at 1.
  intros [i1 i2]. assert (h3 : y - r < S y). lia.
  rewrite (PeanoNat.Nat.mul_comm (S y) q) in i1.
  generalize (divmod_unicity (Nat.div x (S y)) q (S y) (ε Q a x (S y)) (y - r) h2 h3 i1).
  intros [j1 j2]. symmetry. exact j2.
Qed.

(****************************************************************************)
(* Mapping of the Even and Odd predicates. *)
(****************************************************************************)

Import PeanoNat.Nat Private_Parity.

Lemma odd_double n : odd (2 * n) = false.
Proof. rewrite odd_mul, odd_2. reflexivity. Qed.

Lemma even_double n : even (2 * n) = true.
Proof. rewrite even_spec. exists n. reflexivity. Qed.

Lemma Even_or_Odd x : Even x \/ Odd x.
Proof.
  rewrite (div_mod_eq x 2). assert (h1: 0 <= x). lia. assert (h2: 0 < 2). lia.
  generalize (mod_bound_pos x 2 h1 h2). generalize (x mod 2). intro n.
  destruct n; intro h.
  left. exists (x / 2). lia. destruct n. right. exists (x / 2). reflexivity. lia.
Qed.

Lemma not_Even_is_Odd x : (~Even x) = Odd x.
Proof.
  apply prop_ext; intro h; generalize (Even_or_Odd x); intros [i|i].
  apply False_rec. exact (h i). exact i. destruct h as [k hk].
  destruct i as [l hl]. lia.
  intros [k hk]. destruct i as [l hl]. lia.
Qed.

Lemma not_Odd_is_Even x : (~Odd x) = Even x.
Proof.
  apply prop_ext; intro h; generalize (Even_or_Odd x); intros [i|i].
  exact i. apply False_rec. exact (h i). destruct h as [k hk]. intro j.
  destruct j as [l hl]. lia.
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
  generalize (ε_spec i a). intros [h1 h2].
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
  generalize (ε_spec i a). intros [h1 h2].
  apply fun_ext; intro x. induction x.
  apply prop_ext; intro h. rewrite h1. apply Odd_0. exact h.
  apply False_rec. rewrite <- h1. exact h.
  rewrite h2, <- IHx, not_Odd_is_Even. apply Odd_S.
Qed.

(****************************************************************************)
(* NUMPAIR(x,y) = 2^x(2y+1): bijection between N² and N-{0}. *)
(****************************************************************************)

Definition NUMPAIR := fun _17324 : nat => fun _17325 : nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) _17324) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) _17325) (NUMERAL (BIT1 0))).

Lemma NUMPAIR_INJ : forall x1 : nat, forall y1 : nat, forall x2 : nat, forall y2 : nat, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Proof. (*thm_1052244*)
  intros x1 y1 x2 y2. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  unfold NUMPAIR, NUMERAL, BIT1, BIT0. intro e.
  
  destruct (Compare_dec.lt_eq_lt_dec x1 x2) as [[h|h]|h].
  apply False_rec. destruct (ge_is_add h) as [k hk]. subst x2.  
  generalize (f_equal (fun x => div x (2 ^ x1)) e).
  rewrite DIV_MULT, pow_add, pow_succ_r, (mul_comm 2 (2 ^ x1)), <- !mul_assoc,
    DIV_MULT. lia.
  apply pow_nonzero. lia.
  lia.
  apply pow_nonzero. lia.

  subst x2. split. reflexivity.
  generalize (f_equal (fun x => div x (2 ^ x1)) e). rewrite !DIV_MULT. lia.
  apply pow_nonzero. lia.
  apply pow_nonzero. lia.
  
  apply False_rec. destruct (ge_is_add h) as [k hk]. subst x1.  
  generalize (f_equal (fun x => div x (2 ^ x2)) e).
  rewrite DIV_MULT, pow_add, pow_succ_r, (mul_comm 2 (2 ^ x2)), <- !mul_assoc,
    DIV_MULT. lia.
  apply pow_nonzero. lia.
  lia.
  apply pow_nonzero. lia.
Qed.

Lemma NUMPAIR_nonzero x y : NUMPAIR x y <> 0.
Proof.
  unfold NUMPAIR, NUMERAL, BIT1, BIT0. rewrite mul_add_distr_l, mul_1_r.
  assert (h: 2 ^ x <> 0). apply pow_nonzero. lia. lia.
Qed.

(****************************************************************************)
(* Definition of the inverse of NUMPAIR like in HOL-Light. *)
(****************************************************************************)

Lemma INJ_INVERSE2 {A B C : Type'} : forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Proof. (*thm_1046684*)
  intros f h.
  exists (fun c => ε (fun a => exists b, f a b = c)).
  exists (fun c => ε (fun b => exists a, f a b = c)).
  intros a b. split.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  assert (i : exists a, Q a). exists a. exists b. reflexivity.
  generalize (ε_spec i). fold q. unfold Q. intros [b' j]. rewrite h in j.
  destruct j as [j1 j2]. auto.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  assert (i : exists b, Q b). exists b. exists a. reflexivity.
  generalize (ε_spec i). fold q. unfold Q. intros [a' j]. rewrite h in j.
  destruct j as [j1 j2]. auto.
Qed.

Definition NUMFST0_pred :=  fun X : nat -> nat => exists Y : nat -> nat, forall x : nat, forall y : nat, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMFST0 := ε NUMFST0_pred.

Lemma NUMFST0_NUMPAIR x y : NUMFST0 (NUMPAIR x y) = x.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists q, NUMFST0_pred q). exists fst. exists snd. assumption.
  generalize (ε_spec i). fold NUMFST0. unfold NUMFST0_pred.
  intros [snd' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMSND0_pred :=  fun Y : nat -> nat => exists X : nat -> nat, forall x : nat, forall y : nat, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND0 := ε NUMSND0_pred.

Lemma NUMSND0_NUMPAIR x y : NUMSND0 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND0_pred x). exists snd. exists fst. assumption.
  generalize (ε_spec i). fold NUMSND0. unfold NUMSND0_pred.
  intros [fst' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMFST := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17340 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), exists Y : nat -> nat, forall x : nat, forall y : nat, ((X _17340 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).

Lemma NUMFST_NUMPAIR x y : NUMFST (NUMPAIR x y) = x.
Proof.
  unfold NUMFST.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
          NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
  generalize (prod nat (prod nat (prod nat (prod nat (prod nat nat))))); intros A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (fst := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMFST0). unfold Q. intros _. exists NUMSND0.
  intros x' y'. rewrite NUMFST0_NUMPAIR, NUMSND0_NUMPAIR. auto.
  generalize (ε_spec i). change (Q fst -> fst a (NUMPAIR x y) = x). intro h.
  destruct (h a) as [snd j]. destruct (j x y) as [j1 j2]. exact j1.
Qed.

Definition NUMSND1_pred :=  fun Y : nat -> nat => forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND1 := ε NUMSND1_pred.

Lemma NUMSND1_NUMPAIR x y : NUMSND1 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND1_pred x). exists snd. unfold NUMSND1_pred.
  intros x' y'. rewrite NUMFST_NUMPAIR. destruct (h x' y') as [h1 h2]. auto.
  generalize (ε_spec i). fold NUMSND1. unfold NUMSND1_pred. intro j.
  destruct (j x y) as [j1 j2]. exact j2.
Qed.

Definition NUMSND := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17341 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17341 (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).

Lemma NUMSND_NUMPAIR x y : NUMSND (NUMPAIR x y) = y.
Proof.
  unfold NUMSND.
  generalize  (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
         NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))).
  generalize (prod nat (prod nat (prod nat (prod nat (prod nat nat))))); intros A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (snd := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMSND1). unfold Q. intros _.
  intros x' y'. rewrite NUMFST_NUMPAIR, NUMSND1_NUMPAIR. auto.
  generalize (ε_spec i). change (Q snd -> snd a (NUMPAIR x y) = y). intro h.
  destruct (h a x y) as [h1 h2]. exact h2.
Qed.

(****************************************************************************)
(* Explicit definition of the inverse of NUMSUM. *)
(****************************************************************************)

Definition NUMSUM := fun _17342 : Prop => fun _17343 : nat => @COND nat _17342 (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) _17343)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) _17343).

Definition NUMLEFT n := if even n then False else True.

Definition NUMRIGHT n := if even n then n / 2 else (n - 1) / 2.

Lemma NUMLEFT_NUMSUM b n : NUMLEFT (NUMSUM b n) = b.
Proof.
  unfold NUMSUM, NUMERAL, BIT1, BIT0, NUMLEFT. destruct (prop_degen b); subst.
  rewrite COND_True, even_succ, odd_mul, odd_2. reflexivity.
  rewrite COND_False, even_double. reflexivity.
Qed.

Lemma NUMRIGHT_NUMSUM b n : NUMRIGHT (NUMSUM b n) = n.
Proof.
  unfold NUMSUM, NUMERAL, BIT1, BIT0, NUMRIGHT. destruct (prop_degen b); subst.
  rewrite COND_True, even_succ, odd_mul, odd_2, S_minus_1, DIV_MULT.
  reflexivity. lia.
  rewrite COND_False, even_double, DIV_MULT. reflexivity. lia.
Qed.

Lemma NUMSUM_surjective n : exists b x, n = NUMSUM b x.
Proof.
  exists (NUMLEFT n). exists (NUMRIGHT n). unfold NUMSUM, NUMLEFT, NUMRIGHT, NUMERAL, BIT1, BIT0.
  case_eq (even n); intro h.
  rewrite COND_False. rewrite even_spec in h. destruct h as [k h]. subst n.
  rewrite DIV_MULT. reflexivity. lia.
  rewrite COND_True. apply eq_false_negb_true in h. change (odd n = true) in h.
  rewrite odd_spec in h. destruct h as [k h]. subst. rewrite plus_1_minus_1.
  rewrite DIV_MULT. lia. lia.
Qed.

Lemma NUMLEFT_def : NUMLEFT = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop => forall _17372 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), exists Y : nat -> nat, forall x : Prop, forall y : nat, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
         (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
           NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).
  generalize (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))); intros A a.
  match goal with |- _ = ε ?x _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => NUMLEFT). intros _. exists NUMRIGHT.
  intros b x. rewrite NUMLEFT_NUMSUM, NUMRIGHT_NUMSUM. auto.
  generalize (ε_spec i); intro h. destruct (h a) as [snd j].
  apply fun_ext; intro n. destruct (NUMSUM_surjective n) as [b [x k]]. subst.
  rewrite NUMLEFT_NUMSUM. destruct (j b x) as [j1 j2]. auto.
Qed.

Lemma NUMRIGHT_def : NUMRIGHT = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat => forall _17373 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), forall x : Prop, forall y : nat, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
         (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
          (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
           NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
  generalize (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))));
    intros A a.
  match goal with |- _ = ε ?x _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => NUMRIGHT). intros _ b x.
  rewrite NUMLEFT_NUMSUM, NUMRIGHT_NUMSUM. auto.
  generalize (ε_spec i); intro h.
  apply fun_ext; intro n. destruct (NUMSUM_surjective n) as [b [x k]]. subst.
  rewrite NUMRIGHT_NUMSUM. destruct (h a b x) as [j1 j2]. auto.
Qed.

(****************************************************************************)
(* Alignment of ZRECSPACE. *)
(****************************************************************************)

Definition INJN {A : Type'} := fun _17374 : nat => fun n : nat => fun a : A => n = _17374.

Definition INJA {A : Type'} := fun _17379 : A => fun n : nat => fun b : A => b = _17379.

Definition INJF {A : Type'} := fun _17386 : nat -> nat -> A -> Prop => fun n : nat => _17386 (NUMFST n) (NUMSND n).

Definition INJP {A : Type'} := fun _17391 : nat -> A -> Prop => fun _17392 : nat -> A -> Prop => fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (_17391 (NUMRIGHT n) a) (_17392 (NUMRIGHT n) a).

Definition ZCONSTR {A : Type'} := fun _17403 : nat => fun _17404 : A => fun _17405 : nat -> nat -> A -> Prop => @INJP A (@INJN A (S _17403)) (@INJP A (@INJA A _17404) (@INJF A _17405)).

Definition ZBOT {A : Type'} := @INJP A (@INJN A (NUMERAL 0)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True)).

Inductive ZRECSPACE {A : Type'} : (nat -> A -> Prop) -> Prop :=
| ZRECSPACE0 : ZRECSPACE ZBOT
| ZRECSPACE1 c i r : (forall n, ZRECSPACE (r n)) -> ZRECSPACE (ZCONSTR c i r).

Lemma ZRECSPACE_def {A : Type'} : (@ZRECSPACE A) = (fun a : nat -> A -> Prop => forall ZRECSPACE' : (nat -> A -> Prop) -> Prop, (forall a' : nat -> A -> Prop, ((a' = (@ZBOT A)) \/ (exists c : nat, exists i : A, exists r : nat -> nat -> A -> Prop, (a' = (@ZCONSTR A c i r)) /\ (forall n : nat, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a).
Proof.
  apply fun_ext; intro a. apply prop_ext.
  induction 1; intros a h; apply h. left. reflexivity.
  right. exists c. exists i. exists r. split. reflexivity. intro n. apply (H0 n a h).
  intro h. apply h. intros a' [e|[c [i [r [e j]]]]]; subst.
  apply ZRECSPACE0. apply ZRECSPACE1. exact j.
Qed.

(****************************************************************************)
(* Alignment of recspace (uses proof irrelevance). *)
(****************************************************************************)

Require Import ProofIrrelevance.

Definition recspace' : Type' -> Type := fun A => {f : nat -> A -> Prop | ZRECSPACE f}.

Definition ZBOT' {A : Type'} : recspace' A := exist _ _ ZRECSPACE0.

Definition recspace : Type' -> Type' := fun A => {| type := recspace' A; el := ZBOT' |}.
Canonical recspace.

Definition _dest_rec : forall {A : Type'}, (recspace A) -> nat -> A -> Prop :=
  fun A r => proj1_sig r.

Definition _mk_rec_pred {A : Type'} (f : nat -> A -> Prop) (g : recspace A) :=
  _dest_rec g = f.

Definition _mk_rec : forall {A : Type'}, (nat -> A -> Prop) -> recspace A :=
  fun A f => ε (_mk_rec_pred f).

Lemma eq_recspace {A : Type'} :
  forall (f g : recspace A), _dest_rec f = _dest_rec g -> f = g.
Proof.
  intros [f hf] [g hg]. simpl. intro e. subst g. apply subset_eq_compat.
  reflexivity.
Qed.

Lemma axiom_10 : forall {A : Type'} (r : nat -> A -> Prop), (@ZRECSPACE A r) = ((@_dest_rec A (@_mk_rec A r)) = r).
Proof.
  intros A f. apply prop_ext.
  intro h. apply (@ε_spec _ (_mk_rec_pred f)). exists (exist _ _ h). reflexivity.
  intro e. rewrite <- e. destruct (_mk_rec f) as [g h]. simpl. exact h.
Qed.

Lemma axiom_9 : forall {A : Type'} (a : recspace A), (@_mk_rec A (@_dest_rec A a)) = a.
Proof.
  intros A [f h]. simpl. apply eq_recspace. simpl. rewrite <- axiom_10. exact h.
Qed.

Definition BOTTOM {A : Type'} := @_mk_rec A (@ZBOT A).

Definition CONSTR {A : Type'} := fun _17428 : nat => fun _17429 : A => fun _17430 : nat -> recspace A => @_mk_rec A (@ZCONSTR A _17428 _17429 (fun n : nat => @_dest_rec A (_17430 n))).

Lemma NUMSUM_INJ : forall b1 : Prop, forall x1 : nat, forall b2 : Prop, forall x2 : nat, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Proof. (*thm_1054531*)
  intros b1 x1 b2 x2. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  unfold NUMSUM. unfold NUMERAL, BIT1, BIT0.
  destruct (prop_degen b1); destruct (prop_degen b2); subst; try rewrite !COND_True; try rewrite !COND_False; intro e.
  split. auto. lia.
  apply False_rec. lia.
  apply False_rec. lia.
  split. auto. lia.
Qed.

Lemma INJN_INJ {A : Type'} : forall n1 : nat, forall n2 : nat, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof. (*thm_1055675*)
  intros n1 n2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. generalize (ext_fun e n1); clear e; intro e.
  generalize (ext_fun e (el A)); clear e. unfold INJN.
  rewrite refl_is_True, sym, is_True. auto.
Qed.

Lemma INJA_INJ {A : Type'} : forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof. (*thm_1056246*)
  intros a1 a2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. generalize (ext_fun e 0); clear e; intro e.
  generalize (ext_fun e a2); clear e. unfold INJA.
  rewrite refl_is_True, is_True. auto.
Qed.

Lemma INJF_INJ {A : Type'} : forall f1 : nat -> nat -> A -> Prop, forall f2 : nat -> nat -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof. (*thm_1056768*)
  intros f1 f2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. apply fun_ext; intro x. apply fun_ext; intro y.
  apply fun_ext; intro a.
  generalize (ext_fun e (NUMPAIR x y)); clear e; intro e.
  generalize (ext_fun e a); clear e. unfold INJF.
  rewrite NUMFST_NUMPAIR, NUMSND_NUMPAIR. auto.
Qed.

Lemma INJP_INJ {A : Type'} : forall f1 : nat -> A -> Prop, forall f1' : nat -> A -> Prop, forall f2 : nat -> A -> Prop, forall f2' : nat -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Proof. (*thm_1057673*)
  intros f1 f1' f2 f2'. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  intro e.
  assert (e1: forall x a, INJP f1 f2 x a = INJP f1' f2' x a).
  intros x a. rewrite e. reflexivity.
  split; apply fun_ext; intro x; apply fun_ext; intro a.
  generalize (e1 (S (2 * x)) a). unfold INJP, NUMLEFT, NUMRIGHT.
  rewrite even_succ, odd_double, !COND_True, S_minus_1, DIV_MULT. auto. lia.
  generalize (e1 (2 * x) a). unfold INJP, NUMLEFT, NUMRIGHT.
  rewrite even_double, !COND_False, DIV_MULT. auto. lia.
Qed.

Lemma ZCONSTR_INJ {A : Type'} c1 i1 r1 c2 i2 r2 : @ZCONSTR A c1 i1 r1 = ZCONSTR c2 i2 r2 -> c1 = c2 /\ i1 = i2 /\ r1 = r2.
Proof.
  unfold ZCONSTR. intro e.
  rewrite INJP_INJ in e. destruct e as [e1 e2].
  rewrite INJN_INJ in e1. rewrite INJP_INJ in e2. destruct e2 as [e2 e3].
  rewrite INJA_INJ in e2. rewrite INJF_INJ in e3. auto.
Qed.

Lemma MK_REC_INJ {A : Type'} : forall x : nat -> A -> Prop, forall y : nat -> A -> Prop, ((@_mk_rec A x) = (@_mk_rec A y)) -> ((@ZRECSPACE A x) /\ (@ZRECSPACE A y)) -> x = y.
Proof. (*thm_1059803*)
  intros x y e [hx hy]. rewrite axiom_10 in hx. rewrite axiom_10 in hy.
  rewrite <- hx, <- hy, e. reflexivity.
Qed.

Lemma CONSTR_INJ : forall {A : Type'}, forall c1 : nat, forall i1 : A, forall r1 : nat -> recspace A, forall c2 : nat, forall i2 : A, forall r2 : nat -> recspace A, ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Proof. (*thm_1060744*)
  intros A c1 i1 r1 c2 i2 r2. apply prop_ext.
  2: intros [e1 [e2 e3]]; subst; reflexivity.
  unfold CONSTR. intro e. apply MK_REC_INJ in e. apply ZCONSTR_INJ in e.
  destruct e as [e1 [e2 e3]]. split. auto. split. auto. apply fun_ext; intro x.
  apply eq_recspace. generalize (ext_fun e3 x). auto.
  split; apply ZRECSPACE1; intro n. destruct (r1 n). auto. destruct (r2 n). auto.
Qed.

(****************************************************************************)
(* Mapping of Sum. *)
(****************************************************************************)

Definition sum' (A B : Type') : Type' := {| type:= sum A B; el := inl (el A)|}.

Canonical sum'.

Definition _dest_sum : forall {A B : Type'}, sum A B -> recspace (prod A B) :=
fun A B p => match p with 
| inl a => CONSTR (NUMERAL 0) (a , ε (fun _ => True)) (fun _ => BOTTOM)
| inr b => CONSTR (S (NUMERAL 0)) (ε (fun _ => True) , b) (fun _ => BOTTOM)
end.

Definition _mk_sum : forall {A B : Type'}, recspace (prod A B) -> sum A B :=
  fun A B f => ε (fun p => f = _dest_sum p).

Lemma _dest_sum_inj :
  forall {A B : Type'} (f g : sum A B), _dest_sum f = _dest_sum g -> f = g.
Proof.
  intros.
  induction f; induction g; unfold _dest_sum in H; rewrite (@CONSTR_INJ (prod A B)) in H; destruct H. destruct H0.
  apply pair_equal_spec in H0. destruct H0. rewrite H0. reflexivity.
  discriminate. discriminate. 
  destruct H0. apply pair_equal_spec in H0. destruct H0. rewrite H2. reflexivity.
Qed.

Lemma axiom_11 : forall {A B : Type'} (a : sum A B), (@_mk_sum A B (@_dest_sum A B a)) = a.
Proof.
  intros. unfold _mk_sum. apply _dest_sum_inj.
  rewrite sym. apply (@ε_spec (sum A B)). exists a. reflexivity.
Qed.

Lemma axiom_12 : forall {A B : Type'} (r : recspace (prod A B)), ((fun a : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = ((fun a''' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a''' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a'')) \/ (exists a'' : B, a' = ((fun a''' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a''') (fun n : nat => @BOTTOM (prod A B))) a''))) -> sum' a') -> sum' a) r) = ((@_dest_sum A B (@_mk_sum A B r)) = r).
Proof.
  intros. apply prop_ext.
  intro h. unfold _mk_sum. rewrite sym. apply (@ε_spec (sum' A B)).
  apply (h (fun r : recspace (prod A B) => exists x : sum' A B, r = _dest_sum x)).
  intros. destruct H. destruct H. exists (inl(x)). simpl. exact H.

  destruct H. exists (inr(x)). simpl. exact H. 

  intro e. rewrite <- e. intros P h. apply h. destruct (_mk_sum r).
  simpl. left. exists t0. reflexivity. right. exists t0. reflexivity.
Qed.

Lemma INL_def {A B : Type'} : (@inl A B) = (fun a : A => @_mk_sum A B ((fun a' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a)).
Proof.
  apply fun_ext. intro a. apply _dest_sum_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite sym. rewrite <- axiom_12. doesn't work *)
  unfold _mk_sum. assert (h: exists p, r = _dest_sum p).
  exists (inl a). simpl. reflexivity.
  generalize (ε_spec h). set (o := ε (fun p : sum' A B => _dest_sum p = r)).
  auto. 
Qed.

Lemma INR_def {A B : Type'} : (@inr A B) = (fun a : B => @_mk_sum A B ((fun a' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : nat => @BOTTOM (prod A B))) a)).
Proof.
  apply fun_ext. intro b. apply _dest_sum_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end. 
  (* rewrite sym. rewrite <- axiom_12. doesn't work *)
  unfold _mk_sum. assert (h: exists p, r = _dest_sum p).
  exists (inr(b)). simpl. reflexivity.
  generalize (ε_spec h). set (o := ε (fun p : sum' A B => _dest_sum p = r)).
  auto. 
Qed.

(****************************************************************************)
(* Alignement of the option type. *)
(****************************************************************************)

Definition option' (A : Type') := {| type := option A; el := None |}.

Canonical option'.

Definition _dest_option : forall {A : Type'}, option A -> recspace A :=
  fun A o =>
    match o with
    | None => @CONSTR A (NUMERAL 0) (@ε A (fun v => True)) (fun _ => @BOTTOM A)
    | Some a => (fun a' : A => @CONSTR A (S (NUMERAL 0)) a' (fun _ => @BOTTOM A)) a
    end.

Lemma _dest_option_inj {A : Type'} (o1 o2 : option A) :
  _dest_option o1 = _dest_option o2 -> o1 = o2.
Proof.
  induction o1; induction o2; simpl; rewrite (@CONSTR_INJ A); intros [e1 [e2 e3]].
  rewrite e2. reflexivity. discriminate. discriminate. reflexivity.
Qed.

Definition _mk_option_pred {A : Type'} (r : recspace A) : option A -> Prop :=
  fun o => _dest_option o = r.

Definition _mk_option : forall {A : Type'}, (recspace A) -> option A :=
  fun A r => ε (_mk_option_pred r).

(* axiom_13 is equivalent to _dest_option being injective. *)
Lemma axiom_13 : forall {A : Type'} (a : option A), (@_mk_option A (@_dest_option A a)) = a.
Proof.
  intros A o. unfold _mk_option.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  assert (i : exists q, Q q). exists o. reflexivity.
  generalize (ε_spec i). fold q. unfold Q, _mk_option_pred. apply _dest_option_inj.
Qed.

Definition option_pred {A : Type'} (r : recspace A) :=
  forall option' : recspace A -> Prop,
      (forall a' : recspace A,
       a' = CONSTR (NUMERAL 0) (ε (fun _ : A => True)) (fun _ : nat => BOTTOM) \/
       (exists a'' : A, a' = CONSTR (S (NUMERAL 0)) a'' (fun _ : nat => BOTTOM)) ->
       option' a') -> option' r.

Inductive option_ind {A : Type'} : recspace A -> Prop :=
| option_ind0 : option_ind (CONSTR (NUMERAL 0) (ε (fun _ : A => True)) (fun _ : nat => BOTTOM))
| option_ind1 a'' : option_ind (CONSTR (S (NUMERAL 0)) a'' (fun _ : nat => BOTTOM)).

Lemma option_eq {A : Type'} : @option_pred A = @option_ind A.
Proof.
  apply fun_ext; intro r. apply prop_ext.
  intro h. apply h. intros r' [i|[a'' i]]; subst. apply option_ind0. apply option_ind1.
  induction 1; unfold option_pred; intros r h; apply h.
  left. reflexivity. right. exists a''. reflexivity.
Qed.

Lemma axiom_14' : forall {A : Type'} (r : recspace A), (option_pred r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof.
  intros A r. apply prop_ext.
  
  intro h. apply (@ε_spec _ (_mk_option_pred r)).
  rewrite option_eq in h. induction h.
  exists None. reflexivity. exists (Some a''). reflexivity.

  intro e. rewrite <- e. intros P h. apply h. destruct (_mk_option r); simpl.
  right. exists t0. reflexivity. left. reflexivity.
Qed.

Lemma axiom_14 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (S (NUMERAL 0)) a''' (fun n : nat => @BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof. intros A r. apply axiom_14'. Qed.

Lemma NONE_def {A : Type'} : (@None A) = (@_mk_option A (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))).
Proof.
  apply _dest_option_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite <- axiom_14'. doesn't work *)
  unfold _mk_option.
  assert (h: exists o, @_mk_option_pred A r o). exists None. reflexivity.
  generalize (ε_spec h).
  set (o := ε (_mk_option_pred r)). unfold _mk_option_pred. auto.
Qed.

Lemma SOME_def {A : Type'} : (@Some A) = (fun a : A => @_mk_option A ((fun a' : A => @CONSTR A (S (NUMERAL 0)) a' (fun n : nat => @BOTTOM A)) a)).
Proof.
  apply fun_ext; intro a. apply _dest_option_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite <- axiom_14'. doesn't work *)
  unfold _mk_option.
  assert (h: exists o, @_mk_option_pred A r o). exists (Some a). reflexivity.
  generalize (ε_spec h).
  set (o := ε (_mk_option_pred r)). unfold _mk_option_pred. auto.  
Qed.

(****************************************************************************)
(* Mapping of list. *)
(****************************************************************************)

Definition list' (A : Type') := {| type := list A; el := nil |}.

Canonical list'.

Definition FCONS {A : Type'} (a : A) (f: nat -> A) (n : nat) : A :=
  match n with
  | 0 => a
  | S n => f n
  end.

Lemma FCONS_def {A : Type'} : @FCONS A = @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A) (fun FCONS' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A => forall _17460 : prod nat (prod nat (prod nat (prod nat nat))), (forall a : A, forall f : nat -> A, (FCONS' _17460 a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (FCONS' _17460 a f (S n)) = (f n))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
      (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
          NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))); intro p.
  apply fun_ext. intro a. apply fun_ext. intro f. apply fun_ext. intro n.
  match goal with [|- _ = ε ?x _ _ _ _] => set (Q := x) end. 
  assert (i : exists q, Q q). exists (fun _ => @FCONS A). unfold Q. intro. auto.
  generalize (ε_spec i). intro H. destruct n. simpl. symmetry. apply H. simpl. symmetry. apply H.
Qed.

Fixpoint _dest_list {A : Type'} l :=
  match l with
  | nil => @CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A)
  | cons a l => (fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a (@_dest_list A l)
  end.

Definition _mk_list_pred {A : Type'} (r : recspace A) : list A -> Prop :=
  fun l => _dest_list l = r.

Definition _mk_list : forall {A : Type'}, (recspace A) -> list A :=
  fun A r => ε (_mk_list_pred r).

Lemma FCONS_0 {A : Type'} (a : A) (f : nat -> A) : FCONS a f (NUMERAL 0) = a.
Proof. reflexivity. Qed.

Lemma _dest_list_inj :
  forall {A : Type'} (l l' : list A), _dest_list l = _dest_list l' -> l = l'.
Proof.
  induction l; induction l'; simpl; rewrite (@CONSTR_INJ A); intros [e1 [e2 e3]].
  reflexivity. discriminate. discriminate. rewrite e2. rewrite (@IHl l'). reflexivity.
  rewrite <- (FCONS_0 (_dest_list l) ((fun _ : nat => BOTTOM))). 
  rewrite <- (FCONS_0 (_dest_list l') ((fun _ : nat => BOTTOM))).
  rewrite e3. reflexivity. 
Qed.    
 
Lemma axiom_15 : forall {A : Type'} (a : list A), (@_mk_list A (@_dest_list A a)) = a. 
Proof.
  intros A l. unfold _mk_list.
  match goal with [|- ε ?x = _] => set (L' := x); set (l' := ε L') end.
  assert (i : exists l', L' l'). exists l. reflexivity.
  generalize (ε_spec i). fold l'. unfold L', _mk_list_pred. apply _dest_list_inj.
Qed.

Definition list_pred {A : Type'} (r : recspace A) :=
  forall list'0 : recspace A -> Prop,
  (forall a' : recspace A, 
  a' = CONSTR (NUMERAL 0) (ε (fun _ : A => True)) (fun _ : nat => BOTTOM) \/ 
  (exists (a0 : A) (a1 : recspace A), a' = CONSTR (S (NUMERAL 0)) a0 (FCONS a1 (fun _ : nat => BOTTOM)) /\ list'0 a1) -> list'0 a') 
  -> list'0 r.

Inductive list_ind {A : Type'} : recspace A -> Prop :=
| list_ind0 : list_ind (CONSTR (NUMERAL 0) (ε (fun _ : A => True)) (fun _ : nat => BOTTOM))
| list_ind1 a'' l'': list_ind (CONSTR (S (NUMERAL 0)) a'' (FCONS (_dest_list l'') (fun _ : nat => BOTTOM))).

Lemma list_eq {A : Type'} : @list_pred A = @list_ind A.
Proof.
  apply fun_ext. intro r. apply prop_ext.
  intro h. apply h. intros r' H. destruct H. rewrite H. exact list_ind0. destruct H. destruct H. destruct H. rewrite H. destruct H0.
  assert (_dest_list nil = @CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A)).
  reflexivity. rewrite <- H0. exact (list_ind1 x nil).
  assert (_dest_list (cons a'' l'') = @CONSTR A (S (NUMERAL 0)) a'' (@FCONS (recspace A) (@_dest_list A l'') (fun n : nat => @BOTTOM A))).
  reflexivity. rewrite <- H0. exact (list_ind1 x (a'':: l'')).

  induction 1; unfold list_pred; intros R h; apply h.
  left; reflexivity.
  right. exists a''. exists (_dest_list l''). split. reflexivity. apply h. 
  induction l''. auto. right. exists a. exists (_dest_list l''). split. reflexivity. 
  apply h. exact IHl''.
Qed.  

Lemma axiom_16' : forall {A : Type'} (r : recspace A), (list_pred r) = ((@_dest_list A (@_mk_list A r)) = r).
Proof.
  intros A r. apply prop_ext.

  intro h. apply (@ε_spec _ (_mk_list_pred r)).
  rewrite list_eq in h. induction h.
  exists nil. reflexivity. exists (cons a'' l''). reflexivity.

  intro e. rewrite <- e. intros P h. apply h. destruct (_mk_list r). 
  left. reflexivity. right. exists t0. exists (_dest_list l). split. 
  reflexivity. apply h. generalize l.
  induction l0. left; reflexivity. right. exists a. exists (_dest_list l0). split. 
  reflexivity. apply h. exact IHl0.
Qed.

Lemma axiom_16 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall list' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a0 a1)) /\ (list' a1))) -> list' a') -> list' a) r) = ((@_dest_list A (@_mk_list A r)) = r).
Proof. intros A r. apply axiom_16'. Qed.

Lemma NIL_def {A : Type'} : (@nil A) = (@_mk_list A (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))).
Proof. 
  apply _dest_list_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* the sequence rewrite sym. rewrite <- axiom_16' doesn't work *)
  unfold _mk_list. 
  assert (h: exists l, @_mk_list_pred A r l). exists nil. reflexivity.
  generalize (ε_spec h). 
  set (l := ε (_mk_list_pred r)). unfold _mk_list_pred. auto.
Qed.   

Lemma CONS_def {A : Type'} : (@cons A) = (fun a0 : A => fun a1 : list A => @_mk_list A ((fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a0 (@_dest_list A a1))).
Proof.
  apply fun_ext. intro a. apply fun_ext; intro l. apply _dest_list_inj. simpl. 
  match goal with [|- ?x = _] => set (r := x) end.
  unfold _mk_list.
  assert (h: exists l', @_mk_list_pred A r l'). exists (cons a l). reflexivity.
  generalize (ε_spec h).
  set (l' := ε (_mk_list_pred r)). unfold _mk_list_pred. auto.
Qed.

Require Import ExtensionalityFacts.

Lemma ISO_def {A B : Type'} : (@is_inverse A B) = (fun _17569 : A -> B => fun _17570 : B -> A => (forall x : B, (_17569 (_17570 x)) = x) /\ (forall y : A, (_17570 (_17569 y)) = y)).
Proof.
  apply fun_ext; intro f. apply fun_ext; intro g.
  unfold is_inverse. apply prop_ext; tauto.
Qed. 

Require Import List.

Lemma APPEND_def {A : Type'} : (@app A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list' A) -> (list' A) -> list' A) (fun APPEND' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A => forall _17935 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  apply fun_ext. intro l. simpl.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @app A). unfold Q. intros. auto.
  generalize (ε_spec i). intro H. symmetry. apply fun_ext. intro l'.
  generalize (NUMERAL (BIT1 32), (NUMERAL 80, (NUMERAL 80, (NUMERAL (BIT1 34), (NUMERAL 78, NUMERAL 68))))); intro p.
  induction l. simpl. apply H. 
  assert (ε Q p (a :: l) l' = (a :: (ε Q p l l'))). apply H. simpl. rewrite <- IHl. apply H0.
Qed.     

Lemma REVERSE_def {A : Type'} : (@rev A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list' A) -> list' A) (fun REVERSE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A => forall _17939 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@app A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))).
Proof. 
  apply fun_ext. intro l. simpl. 
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @rev A). unfold Q. intros. auto.
  generalize (ε_spec i). intro H. symmetry.
  induction l. simpl. apply H. 
  simpl. rewrite <- IHl. 
  generalize (NUMERAL 82, 
              (NUMERAL (BIT1 34), 
                (NUMERAL 86, 
                  (NUMERAL (BIT1 34), 
                    (NUMERAL 82, (NUMERAL (BIT1 (BIT1 20)), 
                      NUMERAL (BIT1 34))))))); intro p.
  assert (ε Q p (a :: l) = (ε Q p l) ++ (a :: nil)). apply H. apply H0.
Qed.   

Lemma LENGTH_def {A : Type'} : (@length A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat) (fun LENGTH' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat => forall _17943 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), ((LENGTH' _17943 (@nil A)) = (NUMERAL 0)) /\ (forall h : A, forall t : list A, (LENGTH' _17943 (@cons A h t)) = (S (LENGTH' _17943 t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof. 
  generalize (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))); intro p.
  apply fun_ext. intro l. simpl. 
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @length A). unfold Q. auto.
  generalize (ε_spec i). intro H. symmetry.
  induction l. simpl. apply H.
  simpl. rewrite <- IHl. apply H.
Qed.  

Lemma MAP_def {A B : Type'} : (@map A B) = (@ε ((prod nat (prod nat nat)) -> (A -> B) -> (list' A) -> list' B) (fun MAP' : (prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod nat (prod nat nat), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof. 
  generalize (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
              (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
                NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))); intro p.
  apply fun_ext. intro f. apply fun_ext. intro l. 
  match goal with |- _ = ε ?x _ _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @map A B). unfold Q. auto.
  generalize (ε_spec i). intro H. symmetry. 
  induction l. simpl. apply H.
  simpl. rewrite <- IHl. apply H.
Qed. 

Lemma COND_list {A : Type'} (l0 l1 l2 : list A) : 
  match l0 with
  | nil => l1
  | cons h t => l2
  end
  = COND (l0 = nil) l1 l2.
Proof.
  induction l0. symmetry. assert ((@nil A = nil) = True). apply prop_ext. auto. auto. 
  rewrite H. apply COND_True.
  assert ((a :: l0 = nil) = False). apply prop_ext. intro.
  assert (nil <> a :: l0). apply nil_cons. easy. easy.
  rewrite H. symmetry. apply COND_False.
Qed.       

Lemma BUTLAST_def {_25251 : Type'} : (@removelast _25251) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list' _25251) -> list' _25251) (fun BUTLAST' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list _25251) -> list _25251 => forall _17958 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((BUTLAST' _17958 (@nil _25251)) = (@nil _25251)) /\ (forall h : _25251, forall t : list _25251, (BUTLAST' _17958 (@cons _25251 h t)) = (@COND (list' _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (BUTLAST' _17958 t))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof. 
  generalize (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
              (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
                (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
                  (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
                    (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
                      (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
                        NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))); intro p.
  apply fun_ext. intro l.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @removelast _25251). unfold Q. intro. split.
  simpl. reflexivity.
  intros. simpl. apply COND_list.
  generalize (ε_spec i). intro H. symmetry. 
  induction l. simpl. apply H.
  assert (ε Q p (a :: l) = COND (l = nil) nil (a :: ε Q p l)). 
  apply H. simpl. rewrite <- IHl. transitivity (COND (l = nil) nil (a :: ε Q p l)). 
  exact H0. symmetry. apply COND_list.
Qed.     

Lemma ALL_def {_25307 : Type'} : (@Forall _25307) = (@ε ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop) (fun ALL' : (prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod nat (prod nat nat), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
      NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))); intro p.
  apply fun_ext. intro P. apply fun_ext. intro l.  
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => @Forall _25307). 
  unfold Q. intro. split. intro. apply prop_ext. trivial. intro. apply Forall_nil.
  intros h P0 t. apply prop_ext; apply Forall_cons_iff. 
  generalize (ε_spec i). intro. induction l; destruct (H p) as [H1 H2].  
  rewrite H1. apply prop_ext. trivial. intro; apply Forall_nil. rewrite H2. 
  transitivity (P a /\ Forall P l). apply prop_ext; apply Forall_cons_iff. rewrite IHl. reflexivity.
Qed.                

Lemma ForallOrdPairs_nil {A : Type'} (R : A -> A -> Prop) : @ForallOrdPairs A R nil = True.
Proof. 
  apply prop_ext. trivial. intro; exact (FOP_nil R).
Qed.

Lemma ForallOrdPairs_hd_tl {A : Type'} (R : A -> A -> Prop) (l : list A) :
  @ForallOrdPairs A R l = ((@Forall A (R (hd (el A) l)) (tl l)) /\ @ForallOrdPairs A R (tl l)).
Proof.
  apply prop_ext. intro. destruct H; simpl. rewrite ForallOrdPairs_nil. 
  split. apply Forall_nil. trivial.
  split. exact H. exact H0. 
  intro. destruct H as [H1 H2]. destruct l; simpl. rewrite ForallOrdPairs_nil. trivial. 
  apply FOP_cons. exact H1. exact H2.
Qed.    

Lemma ForallOrdPairs_cons {A : Type'} (R : A -> A -> Prop) (h : A) (t : list A) :
  @ForallOrdPairs A R (h :: t) = ((@Forall A (R h) t) /\ @ForallOrdPairs A R t).
Proof. apply ForallOrdPairs_hd_tl. Qed.  

Lemma PAIRWISE_def {A : Type'} : (@ForallOrdPairs A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop) (fun PAIRWISE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (list A) -> Prop => forall _18057 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18057 r (@nil A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : list A, (PAIRWISE' _18057 r (@cons A h t)) = ((@Forall A (r h) t) /\ (PAIRWISE' _18057 r t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
      (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
        (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
          (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
            (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
              (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
                NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))); intro p.
  apply fun_ext; intro R. apply fun_ext; intro l. 
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end. 
  assert (i : exists q, Q q). exists (fun _ => @ForallOrdPairs A). 
  unfold Q. intro. split. apply ForallOrdPairs_nil. intros h r t; apply ForallOrdPairs_cons.  
  generalize (ε_spec i). intro H. symmetry. induction l. rewrite ForallOrdPairs_nil. 
  apply H. rewrite (ForallOrdPairs_cons R a l). rewrite <- IHl. apply H.
Qed.

(* Coercion from bool to Prop, used in the mapping of char to ascii below. *)

Coercion is_true : bool >-> Sortclass.

Lemma is_true_of_true : True = is_true true.
Proof.
  unfold is_true. apply prop_ext. trivial. trivial.
Qed.

Lemma is_true_of_false : False = is_true false.
Proof.
  unfold is_true. apply prop_ext. auto. intro. discriminate.
Qed.

(* Coercion from Prop to bool. *)
(*
Definition bool_of_Prop (P:Prop) : bool := COND P true false.

Coercion bool_of_Prop: Sortclass >-> bool.
*)
(* There are problems for mapping FILTER to List.filter because
HOL-Light's FILTER takes propositional functions as argument while
Coq's List.filter function takes boolean functions as argument. The
error does not occur here but later in the HOL-Light proofs.

Fixpoint filter_bis {A : Type'} (f : A -> Prop) (l : list A) : list A
      := match l with | nil => nil | x :: l => @COND (list A) (f x)
      (x::filter_bis f l) (filter_bis f l) end.

Lemma FILTER_def {_25594 : Type'} : (@filter _25594) = (@ε ((prod nat
(prod nat (prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop)
-> (list _25594) -> list _25594) (fun FILTER' : (prod nat (prod nat
(prod nat (prod nat (prod nat nat))))) -> (_25594 -> Prop) -> (list
_25594) -> list _25594 => forall _18022 : prod nat (prod nat (prod nat
(prod nat (prod nat nat)))), (forall P : _25594 -> Prop, (FILTER'
_18022 P (@nil _25594)) = (@nil _25594)) /\ (forall h : _25594, forall
P : _25594 -> Prop, forall t : list _25594, (FILTER' _18022 P (@cons
_25594 h t)) = (@COND (list _25594) (P h) (@cons _25594 h (FILTER'
_18022 P t)) (FILTER' _18022 P t)))) (@pair nat (prod nat (prod nat
(prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0
(BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat)))
(NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair
nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0
(BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0
(BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1
(BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1
(BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).  Proof.  generalize
(NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL
(BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0
(BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0 (BIT0
(BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), (NUMERAL (BIT1 (BIT0 (BIT1
(BIT0 (BIT0 (BIT0 (BIT1 0))))))), NUMERAL (BIT0 (BIT1 (BIT0 (BIT0
(BIT1 (BIT0 (BIT1 0)))))))))))); intro p.  apply fun_ext; intro
f. apply fun_ext; intro l.  match goal with |- _ = ε ?x _ _ _=> set (Q
:= x) end.  assert (i : exists q, Q q). exists (fun _=> @filter_bis
_25594).  unfold Q. intro. auto.  generalize (ε_spec i). intro
H. symmetry. induction l; simpl. apply H.  assert (ε Q p (fun x :
_25594 => f x) (a :: l) = COND (f a) (a::ε Q p (fun x : _25594 => f x)
l) (ε Q p (fun x : _25594 => f x) l )).  apply H. transitivity (COND
(f a) (a :: ε Q p (fun x : _25594 => f x) l) (ε Q p (fun x : _25594 =>
f x) l)).  exact H0. transitivity (COND (f a) (a :: ε Q p (fun x :
_25594 => f x) l) (filter f l)).  rewrite <- IHl. reflexivity.
destruct (f a). rewrite <- is_true_of_true. rewrite COND_True. rewrite
<- IHl. reflexivity.  rewrite <- is_true_of_false. apply COND_False.
Qed.*)

Lemma MEM_def {_25376 : Type'} : (@In _25376) = (@ε ((prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop) (fun MEM' : (prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop => forall _17995 : prod nat (prod nat nat), (forall x : _25376, (MEM' _17995 x (@nil _25376)) = False) /\ (forall h : _25376, forall x : _25376, forall t : list _25376, (MEM' _17995 x (@cons _25376 h t)) = ((x = h) \/ (MEM' _17995 x t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
      NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))); intro p.
  apply fun_ext; intro x. apply fun_ext; intro l. 
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end. 
  assert (i : exists q, Q q). exists (fun _=> @In _25376). unfold Q. intro. simpl.
  split. trivial. intros. apply prop_ext. intro. destruct H. symmetry in H. left. exact H. right. exact H.
  intro. destruct H. left. symmetry in H. exact H. right. exact H.
  generalize (ε_spec i). intro H. symmetry. induction l; simpl. apply H. rewrite <- IHl.
  transitivity ((x = a \/ ε Q p x l)). apply H. apply prop_ext. 
  intro. destruct H0. left. symmetry. exact H0. right. exact H0. 
  intro. destruct H0. left. symmetry. exact H0. right. exact H0. 
Qed.

Definition repeat_with_perm_args {A: Type'} (n: nat) (a: A) := @repeat A a n.

Lemma REPLICATE_def {_25272 : Type'} : (@repeat_with_perm_args _25272) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272) (fun REPLICATE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272 => forall _17962 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall x : _25272, (REPLICATE' _17962 (NUMERAL 0) x) = (@nil _25272)) /\ (forall n : nat, forall x : _25272, (REPLICATE' _17962 (S n) x) = (@cons _25272 x (REPLICATE' _17962 n x)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
      (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
        (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
          (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
            (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
              (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), 
                (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
                  NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))); intro p.
  apply fun_ext; intro n. apply fun_ext; intro a.
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _=> @repeat_with_perm_args _25272). 
  unfold Q. intro; simpl. auto.
  generalize (ε_spec i). intro H. symmetry. induction n; simpl. apply H. 
  rewrite <- IHn. apply H. 
Qed.

Definition fold_right_with_perm_args {A B : Type'} (f: B -> A -> A) (l: list B) (a: A) :=
  @fold_right A B f a l.

Lemma ITLIST_def {_25350 _25351 : Type'} : (@fold_right_with_perm_args _25350 _25351) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350) (fun ITLIST' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (_25351 -> _25350 -> _25350) -> (list _25351) -> _25350 -> _25350 => forall _17988 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall f : _25351 -> _25350 -> _25350, forall b : _25350, (ITLIST' _17988 f (@nil _25351) b) = b) /\ (forall h : _25351, forall f : _25351 -> _25350 -> _25350, forall t : list _25351, forall b : _25350, (ITLIST' _17988 f (@cons _25351 h t) b) = (f h (ITLIST' _17988 f t b)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
    (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
      (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
        (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
          (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), 
            NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))); intro p.
  apply fun_ext; intro f. apply fun_ext; intro l. apply fun_ext; intro a.
  match goal with |- _ = ε ?x _ _ _ _=> set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _=> @fold_right_with_perm_args _25350 _25351).
  unfold Q. intro. simpl. auto.
  generalize (ε_spec i). intro H. symmetry. induction l; simpl. apply H. 
  rewrite <- IHl. apply H.
Qed.  

Definition HD {A : Type'} := @ε ((prod nat nat) -> (list A) -> A) (fun HD' : (prod nat nat) -> (list A) -> A => forall _17927 : prod nat nat, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))).

Lemma HD_of_cons {A: Type'} (h: A) (t: list A) : @HD A (h :: t) = h.
Proof.
  unfold HD. generalize (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
    NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))); intro p.
  match goal with |- ε ?x _ _ = _=> set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _=> @hd A (HD nil)). 
  unfold Q. intro. simpl. trivial. 
  generalize (ε_spec i). intro H. apply H.
Qed.

Definition hd {A:Type'} := @hd A (HD nil).

Lemma HD_def {A : Type'} : @hd A = @HD A. 
Proof.
  apply fun_ext. intro l. unfold hd, HD.
  generalize (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), 
    NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))); intro p. 
  match goal with |- _ = ε ?x _ _=> set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @hd A).
  unfold Q. intro. simpl. trivial.
  generalize (ε_spec i). intro H. destruct l; simpl. reflexivity. rewrite H. reflexivity.
Qed.

Definition TL {A : Type'} := (@ε ((prod nat nat) -> (list A) -> list A) (fun TL' : (prod nat nat) -> (list A) -> list A => forall _17931 : prod nat nat, forall h : A, forall t : list A, (TL' _17931 (@cons A h t)) = t) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).

Definition tl {A : Type'} (l : list A) :=
match l with
| nil => @TL A nil
| cons h t => @tl A (cons h t)
end.

Lemma TL_def {A : Type'} : @tl A = @TL A.
Proof.
  apply fun_ext. intro l. destruct l. simpl. reflexivity. unfold TL.
  generalize (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
    NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))); intro p.
  match goal with |-_ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _=> @tl A).
  unfold Q. intro. simpl. trivial.
  generalize (ε_spec i). intro H.
  unfold Q. simpl. symmetry. apply H.
Qed.

(* We cannot map EL to List.nth because the equation defining EL
requires (TL NIL) to be equal to NIL, which is not the case.

Lemma nth_of_0 {A: Type'} (l: list A) d : nth (NUMERAL 0) l d =
List.hd d l.  Proof. destruct l;
simpl. reflexivity. symmetry. reflexivity. Qed.

Lemma nth_of_Suc {A: Type'} (n: nat) (l: list A) d : nth (S n) l d =
nth n (List.tl l) d.  Proof. destruct l; simpl. destruct n; simpl;
reflexivity. reflexivity. Qed.

Definition EL {A: Type'} (n: nat) (l: list A) : A := @nth A n l (HD
nil).

Lemma EL_def {_25569 : Type'} : (@EL _25569) = (@ε ((prod nat nat) ->
nat -> (list _25569) -> _25569) (fun EL' : (prod nat nat) -> nat ->
(list _25569) -> _25569 => forall _18015 : prod nat nat, (forall l :
list _25569, (EL' _18015 (NUMERAL 0) l) = (@hd _25569 l)) /\ (forall n
: nat, forall l : list _25569, (EL' _18015 (S n) l) = (EL' _18015 n
(@tl _25569 l)))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0
(BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0
(BIT0 (BIT1 0)))))))))).  Proof.  generalize (NUMERAL (BIT1 (BIT0
(BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), NUMERAL (BIT0 (BIT0 (BIT1
(BIT1 (BIT0 (BIT0 (BIT1 0)))))))); intro p.  apply fun_ext. intro n.
match goal with |-_ = ε ?x _ _ => set (Q := x) end.  assert (i: exists
q, Q q). exists (fun _ => @EL _25569).  unfold Q. intro. unfold
EL. simpl. split.  destruct l; reflexivity. intros n' l. rewrite
nth_of_Suc.  generalize (ε_spec i). intro H. unfold EL. apply fun_ext.
induction n; simpl; intro l.  rewrite nth_of_0. symmetry. apply H.
rewrite nth_of_Suc. rewrite (IHn (tl l)). symmetry. apply H.  Qed.*)

(****************************************************************************)
(* Mapping of char. *)
(****************************************************************************)

(* Note the mismatch between Coq's ascii which takes booleans as arguments
and HOL-Light's char which takes propositions as arguments.*) 

Require Import Coq.Strings.Ascii.

Definition ascii' := {| type := ascii; el := zero |}.

Canonical ascii'.

Definition _dest_char : ascii -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) :=
fun a => match a with 
| Ascii a0 a1 a2 a3 a4 a5 a6 a7 => (fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7
end.

Definition _mk_char_pred (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) : ascii -> Prop :=
fun a => _dest_char a = r.

Definition _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> ascii :=
fun r => ε (_mk_char_pred r).

Lemma eq_true_inj (b b' : bool) : is_true b = is_true b' -> b = b'. 
Proof.
  intro. induction b; induction b'. 
  reflexivity. 
  unfold is_true in H. symmetry. rewrite <- H. reflexivity.
  unfold is_true in H. rewrite H; reflexivity.
  reflexivity.
Qed.    

Lemma _dest_char_inj (a a' : ascii) : _dest_char a = _dest_char a' -> a = a'.
Proof.
  induction a. induction a'. simpl. 
  rewrite (@CONSTR_INJ (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))).
  intros [e1[ e2 e3]]. 
  assert (b = b7 /\ b0 = b8 /\ b1 = b9 /\ b2 = b10 /\ b3 = b11 /\ b4 = b12 /\ b5 = b13 /\ b6 = b14).
  apply pair_equal_spec in e2. repeat (rewrite pair_equal_spec in e2; split).
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. split. 
  apply eq_true_inj; apply e2. 
  apply eq_true_inj; apply e2. 
  destruct H; rewrite H. destruct H0; rewrite H0. destruct H1; rewrite H1. destruct H2; rewrite H2. destruct H3; rewrite H3.
  destruct H4; rewrite H4. destruct H5; rewrite H5. rewrite H6. reflexivity.
Qed.

Lemma axiom_17 : forall (a : ascii), (_mk_char (_dest_char a)) = a.
Proof.
  intro a. unfold _mk_char. 
  match goal with [|- ε ?x = _] => set (A' := x); set (a' := ε A') end.
  assert (i : exists a', A' a'). exists a. reflexivity. 
  generalize (ε_spec i). fold a'. unfold A', _mk_char_pred. apply _dest_char_inj.
Qed.

Definition char_pred (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) := 
  forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' = 
    ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' r.

Inductive char_ind : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) -> Prop :=
| char_ind_cons a0 a1 a2 a3 a4 a5 a6 a7 : char_ind (CONSTR (NUMERAL 0) (is_true a0, (is_true a1, (is_true a2, (is_true a3, (is_true a4, (is_true a5, (is_true a6, is_true a7))))))) (fun _ : nat => BOTTOM)).

Lemma Prop_bool_eq (P : Prop) : P = @COND bool P true false.
Proof.
  assert (P = True \/ P = False). apply prop_degen. destruct H.
  rewrite H. rewrite (COND_True bool true false). rewrite is_true_of_true. reflexivity.
  rewrite H. rewrite (COND_False bool true false). rewrite is_true_of_false. reflexivity.
Qed. 

Lemma char_eq : char_pred = char_ind.
Proof.
  apply fun_ext. intro r. apply prop_ext.
  intro h. apply h. intros r' H. destruct H as [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 e]]]]]]]].
  rewrite e. 
  rewrite (Prop_bool_eq a0).
  rewrite (Prop_bool_eq a1).
  rewrite (Prop_bool_eq a2).
  rewrite (Prop_bool_eq a3).
  rewrite (Prop_bool_eq a4).
  rewrite (Prop_bool_eq a5).
  rewrite (Prop_bool_eq a6).
  rewrite (Prop_bool_eq a7).
  exact (char_ind_cons (@COND bool a0 true false) (@COND bool a1 true false) (@COND bool a2 true false) 
  (@COND bool a3 true false) (@COND bool a4 true false) (@COND bool a5 true false) (@COND bool a6 true false) 
  (@COND bool a7 true false)).
  induction 1. unfold char_pred. intros R h. apply h. 
  exists a0. exists a1. exists a2. exists a3. exists a4. exists a5. exists a6. exists a7.
  reflexivity.     
Qed.

Lemma axiom_18' : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))),
char_pred r = ((_dest_char (_mk_char r)) = r).
Proof.
  intro r. apply prop_ext.
  
  intro h. apply (@ε_spec _ (_mk_char_pred r)).
  rewrite char_eq in h. induction h. exists (Ascii a0 a1 a2 a3 a4 a5 a6 a7). reflexivity.

  intro e. rewrite <- e. intros P h. apply h. destruct (_mk_char r); simpl.
  exists (is_true b). exists (is_true b0). exists (is_true b1). exists (is_true b2). exists (is_true b3). exists (is_true b4). exists (is_true b5). exists (is_true b6).
  reflexivity.
Qed.

Lemma axiom_18 : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))), ((fun a : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) => forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' = 
((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) = ((_dest_char (_mk_char r)) = r).
Proof. intro r. apply axiom_18'. Qed.

(*******************************************************************************)
(* Mapping of nadd (the type of nearly-additive sequences of natural numbers). *)
(*******************************************************************************)

Definition dist := fun _22820 : prod nat nat => Nat.add (Nat.sub (@fst nat nat _22820) (@snd nat nat _22820)) (Nat.sub (@snd nat nat _22820) (@fst nat nat _22820)).

Definition is_nadd := fun _23130 : nat -> nat => exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (Nat.mul m (_23130 n)) (Nat.mul n (_23130 m)))) (Nat.mul B (Nat.add m n)).

Definition nadd : Type := {f : nat -> nat | is_nadd f}.

Lemma dist_refl : forall n : nat, dist (n,n) = 0.
Proof.
  intro n. unfold dist. simpl. rewrite sub_diag. simpl. reflexivity.
Qed.

Lemma is_nadd_0 : is_nadd (fun _ => 0).
Proof. 
  unfold is_nadd. exists 0. intros m n. simpl. repeat rewrite mul_0_r. rewrite dist_refl. auto.
Qed.    

Definition fun_0' : nadd := exist _ _ is_nadd_0.

Definition nadd' : Type' := {| type := nadd ; el := fun_0'|}.

Definition dest_nadd : nadd -> (nat -> nat) := fun f => proj1_sig f.

Definition mk_nadd_pred (f : nat -> nat) (g : nadd) := dest_nadd g = f.

Definition mk_nadd : (nat -> nat) -> nadd :=
  fun f => @ε (nadd') (mk_nadd_pred f).

Lemma eq_nadd : forall (f g : nadd), dest_nadd f = dest_nadd g -> f = g.
Proof.
  intros [f hf] [g hg]. simpl. intro e. subst g. apply subset_eq_compat. reflexivity.
Qed.

Lemma axiom_20 : forall (r : nat -> nat), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).
Proof.
  intro f. apply prop_ext. 
  intro h. apply (@ε_spec (nadd') (mk_nadd_pred f)). exists (exist _ _ h). reflexivity.
  intro e. rewrite <- e. destruct (mk_nadd f) as [g h]. simpl. exact h.
Qed.

Lemma axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.
Proof.
  intros [f h]. simpl. apply eq_nadd. simpl. rewrite <- axiom_20. exact h. 
Qed.
