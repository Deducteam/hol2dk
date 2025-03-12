(****************************************************************************)
(* Coq theory for encoding HOL-Light proofs. *)
(****************************************************************************)

Lemma ext_fun {A B} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof. intros fg x. rewrite fg. reflexivity. Qed.

Lemma eq_false_negb_true b : b = false -> negb b = true.
Proof. intro e. subst. reflexivity. Qed.

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

Require Export HOLLight_Real_With_N.type.

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
(* Functional extensionality. *)
(****************************************************************************)

Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.

Tactic Notation "ext" simple_intropattern(x) :=
  apply fun_ext ; intros x.

Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) :=
  ext x ; ext y.

Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) :=
  ext x ; ext y; ext z.

Tactic Notation "gen_intro" constr(h) simple_intropattern(e) :=
  generalize h; clear e; intros e.

Tactic Notation "intro_ext" simple_intropattern(e) :=
  intros e; gen_intro (ext_fun e) e.

Tactic Notation "intro_ext" simple_intropattern(e) ident(x) :=
  intro_ext e; gen_intro (ext_fun (e x)) e.

(****************************************************************************)
(* Hilbert's ε operator. *)
(****************************************************************************)

Require Import Coq.Logic.ClassicalEpsilon.

Definition ε : forall {A : Type'}, (type A -> Prop) -> type A :=
  fun A P => epsilon (inhabits (el A)) P.

Lemma ε_spec {A : Type'} {P : type A -> Prop} : (exists x, P x) -> P (ε P).
Proof. intro h. unfold ε. apply epsilon_spec. exact h. Qed.

Lemma align_ε (A : Type') (P : A -> Prop) a : P a -> (forall x, P x -> a = x) -> a = ε P.
Proof.
  intros ha hg.
  apply hg.
  apply ε_spec.
  exists a. apply ha.
Qed.

Ltac gobble f x :=
  let g := fresh in
  set (g := f x) in * ;
  clearbody g ; clear f x ;
  rename g into f.

Ltac align_ε :=
  let rec aux :=
    lazymatch goal with
    | |- _ = ε _ => apply align_ε
    | |- _ ?x = ε _ ?x => apply (f_equal (fun f => f x)) ; aux
    | |- ?f = ε _ ?r =>
      apply (f_equal (fun g => g r) (x := fun _ => f)) ;
      aux ; [
        intros _
      | let g := fresh f in
        let na := fresh in
        let h := fresh in
        intros g h ;
        ext na ; specialize (h na) ; gobble g na ;
        revert g h
      ]
    end
  in
  aux.

Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.

Lemma prop_ext_eq: forall {P Q : Prop}, (P <-> Q) -> P = Q.
Proof.
  intros P Q H.
  apply prop_ext.
  - exact (proj1 H).
  - exact(proj2 H).
Qed.

Require Import Coq.Logic.ClassicalFacts.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  apply prop_ext_em_degen.
  - unfold prop_extensionality.
    exact @prop_ext_eq.
  - intro P.
    apply classic.
Qed.

Lemma is_True P : (P = True) = P.
Proof.
  apply prop_ext; intro h.
  - rewrite h.
    exact I.
  - apply prop_ext; intro g.
    + exact I.
    + exact h.
Qed.

Lemma is_False P : (P = False) = ~ P.
Proof.
  apply prop_ext; intro h.
  - rewrite h.
    intro f.
    exact f.
  - apply prop_ext; intro g.
    + apply h.
      exact g.
    + apply False_rec.
      exact g.
Qed.

Lemma refl_is_True {A} (x:A) : (x = x) = True.
Proof. rewrite is_True. reflexivity. Qed.

Lemma sym {A} (x y : A) : (x = y) = (y = x).
Proof. apply prop_ext; intro e; symmetry; exact e. Qed.

Lemma True_and_True : (True /\ True) = True.
Proof. rewrite is_True. tauto. Qed.

Lemma not_forall_eq A (P : A -> Prop) : (~ forall x, P x) = exists x, ~ (P x).
Proof.
  apply prop_ext; intro h.
  - apply not_all_ex_not.
    exact h.
  - apply ex_not_not_all.
    exact h.
Qed.

Lemma not_exists_eq A (P : A -> Prop) : (~ exists x, P x) = forall x, ~ (P x).
Proof.
  apply prop_ext; intro h.
  - apply not_ex_all_not.
    exact h.
  - apply all_not_not_ex.
    exact h.
Qed.

Lemma ex2_eq A (P Q : A -> Prop) : (exists2 x, P x & Q x) = (exists x, P x /\ Q x).
Proof.
  apply prop_ext.
  - intros [x l r].
    exists x.
    exact (conj l r).
  - intros [x [l r]].
    exists x; assumption.
Qed.

Lemma not_conj_eq P Q : (~(P /\ Q)) = (~P \/ ~Q).
Proof.
  apply prop_ext; intro h.
  - case (classic P); intro p.
    + right.
      intro q.
      apply h.
      exact (conj p q).
    + left.
      exact p.
  - intros [p q].
    destruct h as [h|h]; contradiction.
Qed.

Lemma not_disj_eq P Q : (~(P \/ Q)) = (~P /\ ~Q).
Proof.
  apply prop_ext; intro h.
  - split; intro i; apply h.
    + left.
      exact i.
    + right.
      exact i.
  - destruct h as [np nq]; intros [i|i]; contradiction.
Qed.

Lemma imp_eq_disj P Q : (P -> Q) = (~P \/ Q).
Proof.
  apply prop_ext; intro h.
  - case (classic P); intro p.
    + right.
      exact (h p).
    + left.
      exact p.
  - intro p.
    destruct h as [h|h].
    + contradiction.
    + exact h.
Qed.

Lemma not_not_eq P: (~~ P) = P.
Proof.
    apply prop_ext; intro h.
      - case (prop_degen P); intro p.
        + rewrite is_True in p.
          assumption.
        + rewrite is_False in p.
          contradiction.
      - intro p.
        apply p.
        assumption.
Qed.

(****************************************************************************)
(* Conditional. *)
(****************************************************************************)

Definition COND {A : Type'} := fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2)).

Lemma COND_def {A : Type'} : (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Proof. exact (eq_refl (@COND A)). Qed.

Lemma COND_True (A : Type') (x y : A) : COND True x y = x.
Proof.
  symmetry.
  unfold COND.
  align_ε.
  - split; intro h.
    + reflexivity.
    + apply False_rec.
      rewrite <- h.
      exact I.
  - intros z [ht _].
    symmetry.
    apply ht.
    reflexivity.
Qed.

Lemma COND_False (A : Type') (x y : A) : COND False x y = y.
Proof.
  symmetry.
  unfold COND.
  align_ε.
  - split; intro h.
    + apply False_rec.
      rewrite h.
      exact I.
    + reflexivity.
  - intros z [_ hf].
    symmetry.
    apply hf.
    reflexivity.
Qed.

Lemma prove_COND (P Q R : Prop) : (P -> Q) -> (~ P -> R) -> COND P Q R.
Proof.
  intros hq hr.
  destruct (prop_degen P) as [-> | ->].
  - rewrite COND_True. apply hq. exact I.
  - rewrite COND_False. apply hr. intro h. exact h.
Qed.

Lemma COND_elim {P Q R G : Prop} : COND P Q R -> (P -> Q -> G) -> (~ P -> R -> G) -> G.
Proof.
  intros h hq hr.
  destruct (prop_degen P) as [-> | ->].
  - rewrite COND_True in h. exact (hq I h).
  - rewrite COND_False in h. apply hr.
    + intro f. exact f.
    + exact h.
Qed.

Definition COND_dep (Q: Prop) (C: Type) (f1: Q -> C) (f2: ~Q -> C) : C :=
  match excluded_middle_informative Q with
  | left _ x => f1 x
  | right _ x => f2 x
  end.

(****************************************************************************)
(* Miscellaneous. *)
(****************************************************************************)

Lemma GABS_def {A : Type'} : (@ε A) = (fun P : A -> Prop => @ε A P).
Proof. exact (eq_refl (@ε A)). Qed.

Lemma GEQ_def {A : Type'} : (@eq A) = (fun a : A => fun b : A => a = b).
Proof. exact (eq_refl (@eq A)). Qed.

Lemma _UNGUARDED_PATTERN_def : and = (fun p : Prop => fun r : Prop => p /\ r).
Proof. exact (eq_refl and). Qed.

Lemma _FALSITY__def : False = False.
Proof. exact (eq_refl False). Qed.

Lemma hashek_def : True = True.
Proof. exact (eq_refl True). Qed.

Require Import Coq.Logic.ExtensionalityFacts.

Lemma ISO_def {A B : Type'} : (@is_inverse A B) = (fun _17569 : A -> B => fun _17570 : B -> A => (forall x : B, (_17569 (_17570 x)) = x) /\ (forall y : A, (_17570 (_17569 y)) = y)).
Proof. ext f g. unfold is_inverse. apply prop_ext; tauto. Qed.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. reflexivity. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof.
  intros A P x h. apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h)).
Qed.

(*****************************************************************************)
(* Alignment of subtypes. *)
(*****************************************************************************)

Require Import Coq.Logic.ProofIrrelevance.

Section Subtype.

  Variables (A : Type) (P : A -> Prop) (a : A) (h : P a).

  Definition subtype := {| type := {x : A | P x}; el := exist P a h |}.

  Definition dest : subtype -> A := fun x => proj1_sig x.

  Definition mk : A -> subtype :=
    fun x => COND_dep (P x) subtype (exist P x) (fun _ => exist P a h).

  Lemma dest_mk_aux x : P x -> (dest (mk x) = x).
  Proof.
    intro hx. unfold mk, COND_dep. destruct excluded_middle_informative.
    reflexivity. contradiction.
  Qed.

  Lemma dest_mk x : P x = (dest (mk x) = x).
  Proof.
    apply prop_ext. apply dest_mk_aux.
    destruct (mk x) as [b i]. simpl. intro e. subst x. exact i.
  Qed.

  Lemma mk_dest x : mk (dest x) = x.
  Proof.
    unfold mk, COND_dep. destruct x as [b i]; simpl.
    destruct excluded_middle_informative.
    rewrite (proof_irrelevance _ p i). reflexivity.
    contradiction.
  Qed.

  Lemma dest_inj x y : dest x = dest y -> x = y.
  Proof.
    intro e. destruct x as [x i]. destruct y as [y j]. simpl in e.
    subst y. rewrite (proof_irrelevance _ i j). reflexivity.
  Qed.

  Lemma mk_inj x y : P x -> P y -> mk x = mk y -> x = y.
  Proof.
    intros hx hy. unfold mk, COND_dep.
    destruct (excluded_middle_informative (P x));
      destruct (excluded_middle_informative (P y)); intro e; inversion e.
    reflexivity. contradiction. contradiction. contradiction.
  Qed.

End Subtype.

Arguments subtype [A P a].
Arguments mk [A P a].
Arguments dest [A P a].
Arguments dest_mk_aux [A P a].
Arguments dest_mk [A P a].
Arguments mk_dest [A P a].

Canonical subtype.

(*****************************************************************************)
(* Alignment of quotients. *)
(*****************************************************************************)

Section Quotient.

  Variables (A : Type') (R : A -> A -> Prop).

  Definition is_eq_class X := exists a, X = R a.

  Definition class_of x := R x.

  Lemma is_eq_class_of x : is_eq_class (class_of x).
  Proof. exists x. reflexivity. Qed.

  Lemma non_empty : is_eq_class (class_of (el A)).
  Proof. exists (el A). reflexivity. Qed.

  Definition quotient := subtype non_empty.

  Definition mk_quotient : (A -> Prop) -> quotient := mk non_empty.
  Definition dest_quotient : quotient -> (A -> Prop) := dest non_empty.

  Lemma mk_dest_quotient : forall x, mk_quotient (dest_quotient x) = x.
  Proof. exact (mk_dest non_empty). Qed.

  Lemma dest_mk_aux_quotient : forall x, is_eq_class x -> (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk_aux non_empty). Qed.

  Lemma dest_mk_quotient : forall x, is_eq_class x = (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk non_empty). Qed.

  Definition elt_of : quotient -> A := fun x => ε (dest_quotient x).

  Variable R_refl : forall a, R a a.

  Lemma eq_elt_of a : R a (ε (R a)).
  Proof. apply ε_spec. exists a. apply R_refl. Qed.

  Lemma dest_quotient_elt_of x : dest_quotient x (elt_of x).
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    apply ε_spec. exists a. apply R_refl.
  Qed.

  Variable R_sym : forall x y, R x y -> R y x.
  Variable R_trans : forall x y z, R x y -> R y z -> R x z.

  Lemma dest_quotient_elim x y : dest_quotient x y -> R (elt_of x) y.
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    intro h. apply R_trans with a. apply R_sym. apply eq_elt_of. exact h.
  Qed.

  Lemma eq_class_intro_elt (x y: quotient) : R (elt_of x) (elt_of y) -> x = y.
  Proof.
    destruct x as [c [x h]]. destruct y as [d [y i]]. unfold elt_of. simpl.
    intro r. apply subset_eq_compat. subst c. subst d.
    ext a. apply prop_ext; intro j.

    apply R_trans with (ε (R y)). apply eq_elt_of.
    apply R_trans with (ε (R x)). apply R_sym. apply r.
    apply R_trans with x. apply R_sym. apply eq_elt_of. exact j.

    apply R_trans with (ε (R x)). apply eq_elt_of.
    apply R_trans with (ε (R y)). apply r.
    apply R_trans with y. apply R_sym. apply eq_elt_of. exact j.
  Qed.

  Lemma eq_class_intro (x y: A) : R x y -> R x = R y.
  Proof.
    intro xy. ext a. apply prop_ext; intro h.
    apply R_trans with x. apply R_sym. exact xy. exact h.
    apply R_trans with y. exact xy. exact h.
  Qed.

  Lemma eq_class_elim (x y: A) : R x = R y -> R x y.
  Proof.
    intro h. generalize (ext_fun h y); intro hy.
    assert (e : R y y = True). rewrite is_True. apply R_refl.
    rewrite e, is_True in hy. exact hy.
  Qed.

  Lemma mk_quotient_elt_of x : mk_quotient (R (elt_of x)) = x.
  Proof.
    apply eq_class_intro_elt. set (a := elt_of x). unfold elt_of.
    rewrite dest_mk_aux_quotient. apply R_sym. apply eq_elt_of.
    exists a. reflexivity.
  Qed.

End Quotient.

Arguments quotient [A].
Arguments mk_quotient [A].
Arguments dest_quotient [A].
Arguments mk_dest_quotient [A].
Arguments dest_mk_aux_quotient [A].
Arguments dest_mk_quotient [A].
Arguments is_eq_class [A].
Arguments elt_of [A R].
Arguments dest_quotient_elt_of [A R].

(****************************************************************************)
(* Alignment of connectives. *)
(****************************************************************************)

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  intro A.
  unfold ex1.
  ext P.
  unfold unique.
  apply prop_ext.
  - intros [x [px u]].
    split.
    + exact (ex_intro P x px).
    + intros a b [ha hb].
      transitivity x.
      * symmetry.
        apply u.
        exact ha.
      * apply u.
        exact hb.
  - intros [[x px] u].
    apply (ex_intro _ x).
    split.
    + exact px.
    + intros y py.
      apply u.
      split.
      * exact px.
      * exact py.
Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof.
  apply prop_ext.
  - intros b p.
    exact (False_rec p b).
  - intro h.
    exact (h False).
Qed.

Lemma not_def : not = (fun p : Prop => p -> False).
Proof. reflexivity. Qed.

Lemma or_def : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Proof.
  ext p q.
  apply prop_ext.
  - intros [P|Q] r pr qr.
    + exact (pr P).
    + exact (qr Q).
  - intro h.
    apply h; intro i.
    + left.
      exact i.
    + right.
      exact i.
Qed.

Lemma ex_def : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Proof.
  intro A.
  ext p.
  apply prop_ext.
  - intros [x px] q pq.
    eapply pq.
    apply px.
  - intro h.
    apply h.
    intros x px.
    apply (ex_intro p x px).
Qed.

Lemma all_def : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Proof.
  intro A.
  ext p.
  apply prop_ext.
  - intro h.
    ext x.
    apply prop_ext; intros _.
    + exact I.
    + exact (h x).
  - intros e x.
    rewrite e.
    exact I.
Qed.

Lemma imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Proof.
  ext p q.
  apply prop_ext; intro h.
  - apply prop_ext.
    + intros [hp _].
      exact hp.
    + intro hp.
      split.
      * exact hp.
      * apply h.
        exact hp.
  - rewrite <- h.
    intros [_ hq].
    exact hq.
Qed.

Lemma and_def : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Proof.
  ext p q.
  apply prop_ext.
  - intros [hp hq].
    ext f.
    case (prop_degen p); intro e; subst p.
    + case (prop_degen q); intro e; subst q.
      * reflexivity.
      * exfalso.
        exact hq.
    + exfalso.
      exact hp.
  - intro_ext e.
    split.
    + rewrite (e (fun p _ => p)).
      exact I.
    + rewrite (e (fun _ q => q)).
      exact I.
Qed.

Lemma T_def : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Proof. apply prop_ext. reflexivity. intros _; exact I. Qed.

(****************************************************************************)
(* Alignment of the unit type. *)
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
(* Alignment of the product type constructor. *)
(****************************************************************************)

Definition prod' (a b : Type') := {| type := a * b; el := pair (el a) (el b) |}.
Canonical prod'.

Definition mk_pair {A B : Type'} :=
  fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y).

Lemma mk_pair_def {A B : Type'} : (@mk_pair A B) = (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).
Proof. exact (eq_refl (@mk_pair A B)). Qed.

Lemma mk_pair_inj {A B : Type'} {x x' : A} {y y' : B} :
  mk_pair x y = mk_pair x' y' -> x = x' /\ y = y'.
Proof.
  intro_ext e x.
  gen_intro (e y) e.
  unfold mk_pair in e.
  rewrite refl_is_True, refl_is_True, True_and_True, sym, is_True in e.
  exact e.
Qed.

Definition ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B :=
  fun A B f => ε (fun p => f = mk_pair (fst p) (snd p)).

Lemma ABS_prod_mk_pair {A B : Type'} {x : A} {y : B} :
  (x,y) = ABS_prod (mk_pair x y).
Proof.
  unfold ABS_prod.
  align_ε.
  - reflexivity.
  - intros [x' y'] h.
    apply pair_equal_spec.
    exact (mk_pair_inj h).
Qed.

Definition REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop :=
  fun A B p a b => mk_pair (fst p) (snd p) a b.

Lemma pair_def {A B : Type'} : (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Proof.
  ext x y.
  exact ABS_prod_mk_pair.
Qed.

Lemma FST_def {A B : Type'} : (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Proof.
  ext [x y].
  align_ε.
  - exists y.
    reflexivity.
  - intros x' h.
    destruct h as [y' h].
    rewrite h.
    reflexivity.
Qed.

Lemma SND_def {A B : Type'} : (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Proof.
  ext [x y].
  align_ε.
  - exists x.
    reflexivity.
  - intros y' h.
    destruct h as [x' h].
    rewrite h.
    reflexivity.
Qed.

Lemma axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.
Proof. intros A B [a b]. symmetry. exact ABS_prod_mk_pair. Qed.

Lemma axiom_5 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).
Proof.
  intros A B f.
  apply prop_ext.
  - intros [a [b e]].
    rewrite e, <- ABS_prod_mk_pair.
    reflexivity.
  - generalize (ABS_prod f).
    intros [a b] e.
    exists a.
    exists b.
    rewrite <- e.
    reflexivity.
Qed.

(****************************************************************************)
(* Alignment of the infinite type ind. *)
(****************************************************************************)

Definition nat' := {| type := nat; el := 0 |}.
Canonical nat'.

Definition ind : Type' := nat'.

Definition ONE_ONE {A B : Type'} := fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2.

Lemma ONE_ONE_def {A B : Type'} : (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).
Proof. exact (eq_refl (@ONE_ONE A B)). Qed.

Definition ONTO {A B : Type'} := fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x).

Lemma ONTO_def {A B : Type'} : (@ONTO A B) = (fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x)).
Proof. exact (eq_refl (@ONTO A B)). Qed.

Lemma axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Proof.
  exists S.
  split.
  - exact eq_add_S.
  - intro h.
    generalize (h 0).
    intros [x hx].
    discriminate.
Qed.

Definition IND_SUC_pred := fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).

Definition IND_SUC := ε IND_SUC_pred.

Lemma IND_SUC_def : IND_SUC = (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))).
Proof. exact (eq_refl IND_SUC). Qed.

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

Lemma IND_0_def : IND_0 = (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))).
Proof. exact (eq_refl IND_0). Qed.

Lemma IND_0_ex : exists z, IND_0_pred z.
Proof.
  generalize IND_SUC_prop. intros [z [h1 h2]]. exists z. split. exact h1. exact h2.
Qed.

Lemma IND_0_prop : IND_0_pred IND_0.
Proof. unfold IND_0. apply ε_spec. apply IND_0_ex. Qed.

Lemma IND_SUC_neq_0 i : IND_SUC i <> IND_0.
Proof. generalize IND_0_prop. intros [h1 h2]. apply h2. Qed.

(****************************************************************************)
(* Properties of NUM_REP. *)
(****************************************************************************)

Definition NUM_REP := fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a.

Lemma NUM_REP_def : NUM_REP = (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a).
Proof. exact (eq_refl NUM_REP). Qed.

Definition NUM_REP' := fun a : ind => forall P : ind -> Prop, (P IND_0 /\ forall i, P i -> P (IND_SUC i)) -> P a.

Lemma NUM_REP_eq : NUM_REP = NUM_REP'.
Proof.
  ext a.
  apply prop_ext; intros h P.
  - intros [p0 ps].
    apply h.
    intros a' [i|i].
    + rewrite i.
      exact p0.
    + destruct i as [b [e i]].
      rewrite e.
      apply ps.
      exact i.
  - intro i.
    apply h.
    split.
    + apply i.
      left.
      reflexivity.
    + intros b pb.
      apply i.
      right.
      exists b.
      split.
        * reflexivity.
        * exact pb.
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
  ext i. apply prop_ext.
  rewrite NUM_REP_eq. intro h. apply h. split.
    apply NUM_REP_ID_0.
    intros j hj. apply NUM_REP_ID_S. exact hj.
  induction 1. apply NUM_REP_0. apply NUM_REP_S. assumption.
Qed.

(****************************************************************************)
(* Alignment of the type of natural numbers. *)
(****************************************************************************)

Require Import Coq.NArith.BinNat Coq.micromega.Lia.

Open Scope N_scope.

Definition N' := {| type := N; el := N0 |}.
Canonical N'.

Lemma N0_or_succ n : n = 0 \/ exists p, n = N.succ p.
Proof. destruct (classic (n = 0)). lia. right. exists (N.pred n). lia. Qed.

Lemma recursion_succ A (a:A) f n :
  N.recursion a f (N.succ n) = f n (N.recursion a f n).
Proof.
  apply N.recursion_succ. reflexivity.
  intros n1 n2 n12 a1 a2 a12. subst n2. subst a2. reflexivity.
Qed.

Definition dest_num := N.recursion IND_0 (fun _ r => IND_SUC r).

Lemma dest_num0 : dest_num 0 = IND_0.
Proof. unfold dest_num. apply N.recursion_0. Qed.

Lemma dest_numS n : dest_num (N.succ n) = IND_SUC (dest_num n).
Proof. unfold dest_num at 1. apply recursion_succ. Qed.

Lemma dest_num_inj : ONE_ONE dest_num.
Proof.
  intro x. pattern x. revert x. apply N.peano_ind.
  intro y. destruct (N0_or_succ y) as [h|[p h]]; subst y. reflexivity.
  rewrite dest_numS.
intro e. apply False_ind. eapply IND_SUC_neq_0. symmetry. exact e.
  intros x hx y. destruct (N0_or_succ y) as [h|[p h]]; subst y.
  rewrite dest_numS.
  intro e. apply False_ind. eapply IND_SUC_neq_0. exact e.
  rewrite !dest_numS. intro e. apply (f_equal N.succ). apply hx.
  apply IND_SUC_inj. exact e.
Qed.

Definition dest_num_img i := exists n, i = dest_num n.

Lemma NUM_REP_eq_dest_num_img : NUM_REP = dest_num_img.
Proof.
  ext i. apply prop_ext.
  rewrite NUM_REP_eq_ID. revert i. induction 1.
    exists 0. reflexivity.
    destruct IHNUM_REP_ID as [n hn]. rewrite hn.
    exists (N.succ n). rewrite dest_numS. reflexivity.
  intros [n hn]. subst. pattern n. revert n. apply N.peano_ind.
  rewrite dest_num0. apply NUM_REP_0.
  intros n hn. rewrite dest_numS. apply NUM_REP_S. exact hn.
Qed.

Lemma NUM_REP_dest_num k : NUM_REP (dest_num k).
Proof. rewrite NUM_REP_eq_dest_num_img. exists k. reflexivity. Qed.

Definition mk_num_pred i n := i = dest_num n.

Definition mk_num i := ε (mk_num_pred i).

Lemma mk_num_ex i : NUM_REP i -> exists n, mk_num_pred i n.
Proof.
  rewrite NUM_REP_eq_ID. induction 1.
  exists 0. reflexivity.
  destruct IHNUM_REP_ID as [n hn]. exists (N.succ n). unfold mk_num_pred.
  rewrite hn, dest_numS. reflexivity.
Qed.

Lemma mk_num_prop i : NUM_REP i -> dest_num (mk_num i) = i.
Proof. intro hi. symmetry. apply (ε_spec (mk_num_ex i hi)). Qed.

Notation dest_num_mk_num := mk_num_prop.

Lemma mk_num_dest_num k : mk_num (dest_num k) = k.
Proof. apply dest_num_inj. apply dest_num_mk_num. apply NUM_REP_dest_num. Qed.

Lemma axiom_7 : forall (a : N), (mk_num (dest_num a)) = a.
Proof. exact mk_num_dest_num. Qed.

Lemma axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
Proof.
  intro r. apply prop_ext. apply dest_num_mk_num. intro h. rewrite <- h.
  apply NUM_REP_dest_num.
Qed.

Lemma _0_def : 0 = (mk_num IND_0).
Proof.
  unfold mk_num.
  align_ε.
  - reflexivity.
  - exact (dest_num_inj 0).
Qed.

Lemma mk_num_S : forall i, NUM_REP i -> mk_num (IND_SUC i) = N.succ (mk_num i).
Proof.
  intros i hi. rewrite NUM_REP_eq_dest_num_img in hi. destruct hi as [n hn].
  subst i. rewrite mk_num_dest_num, <- dest_numS, mk_num_dest_num. reflexivity.
Qed.

Lemma SUC_def : N.succ = (fun _2104 : N => mk_num (IND_SUC (dest_num _2104))).
Proof.
  symmetry. ext x. rewrite mk_num_S. 2: apply NUM_REP_dest_num.
  apply f_equal. apply axiom_7.
Qed.

(****************************************************************************)
(* Alignment of mathematical functions on natural numbers with N. *)
(****************************************************************************)

Definition NUMERAL (x : N) := x.

Lemma NUMERAL_def : NUMERAL = (fun _2128 : N => _2128).
Proof. exact (eq_refl NUMERAL). Qed.

Definition BIT0 := N.double.

Lemma BIT0_def : BIT0 = @ε (arr N N') (fun y0 : N -> N => ((y0 (NUMERAL N0)) = (NUMERAL N0)) /\ (forall y1 : N, (y0 (N.succ y1)) = (N.succ (N.succ (y0 y1))))).
Proof.
  unfold BIT0.
  align_ε.
  - split.
    + reflexivity.
    + lia.
  - intros BIT0' [h0 hs].
    apply fun_ext.
    apply N.peano_ind.
    + exact (eq_sym h0).
    + intros n IH.
      rewrite (hs n), <- IH.
      lia.
Qed.

Definition BIT1 := fun n : N => N.succ (BIT0 n).

Lemma BIT1_def : BIT1 = (fun _2143 : N => N.succ (BIT0 _2143)).
Proof. exact (eq_refl BIT1). Qed.

Lemma BIT1_eq_succ_double : BIT1 = N.succ_double.
Proof. ext n. unfold BIT1, BIT0. lia. Qed.

Lemma PRE_def : N.pred = (@ε (arr (prod N (prod N N)) (arr N N')) (fun PRE' : (prod N (prod N N)) -> N -> N' => forall _2151 : prod N (prod N N), ((PRE' _2151 (NUMERAL N0)) = (NUMERAL N0)) /\ (forall n : N, (PRE' _2151 (N.succ n)) = n)) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  align_ε.
  - split.
    + reflexivity.
    + lia.
  - intros PRE' [h0 hs].
    apply fun_ext.
    intro n.
    destruct (N0_or_succ n) as [n0|np].
    + rewrite n0.
      exact (eq_sym h0).
    + destruct np as [p np].
      rewrite np, hs.
      lia.
Qed.

Lemma add_def : N.add = (@ε (arr N (arr N (arr N N'))) (fun add' : N -> N -> N -> N => forall _2155 : N, (forall n : N, (add' _2155 (NUMERAL N0) n) = n) /\ (forall m : N, forall n : N, (add' _2155 (N.succ m) n) = (N.succ (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  align_ε.
  - split; unfold NUMERAL; lia.
  - intros add' [h0 hs].
    ext x y.
    revert x.
    apply N.peano_ind.
    + exact (eq_sym (h0 y)).
    + intros n IH.
      rewrite hs, <- IH.
      lia.
Qed.

Lemma mul_def : N.mul = (@ε (arr N (arr N (arr N N'))) (fun mul' : N -> N -> N -> N => forall _2186 : N, (forall n : N, (mul' _2186 (NUMERAL N0) n) = (NUMERAL N0)) /\ (forall m : N, forall n : N, (mul' _2186 (N.succ m) n) = (N.add (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  align_ε.
  - split; unfold NUMERAL; lia.
  - intros mul' [h0 hs].
    ext x y.
    revert x.
    apply N.peano_ind.
    + exact (eq_sym (h0 y)).
    + intros n IH.
      rewrite hs, <- IH.
      lia.
Qed.

Lemma EXP_def : N.pow = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun EXP' : (prod N (prod N N)) -> N -> N -> N => forall _2224 : prod N (prod N N), (forall m : N, EXP' _2224 m (NUMERAL N0) = NUMERAL (BIT1 N0)) /\ (forall m : N, forall n : N, (EXP' _2224 m (N.succ n)) = (N.mul m (EXP' _2224 m n)))) (@pair N (prod N N) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))) (@pair N N (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))).
Proof.
  cbn.
  align_ε.
  - split.
    + reflexivity.
    + exact N.pow_succ_r'.
  - intros pow' [h0 hs].
    ext x.
    apply fun_ext.
    apply N.peano_ind.
    + exact (eq_sym (h0 x)).
    + intros n IH.
      rewrite hs, <- IH.
      exact (N.pow_succ_r' x n).
Qed.

Lemma le_def : N.le = (@ε (arr (prod N N) (arr N (arr N Prop'))) (fun le' : (prod N N) -> N -> N -> Prop => forall _2241 : prod N N, (forall m : N, (le' _2241 m (NUMERAL N0)) = (m = (NUMERAL N0))) /\ (forall m : N, forall n : N, (le' _2241 m (N.succ n)) = ((m = (N.succ n)) \/ (le' _2241 m n)))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))))).
Proof.
  cbn.
  align_ε.
  - split.
    + intro n.
      apply prop_ext_eq.
      exact (N.le_0_r n).
    + intros n m.
      apply prop_ext_eq.
      rewrite or_comm.
      exact (N.le_succ_r n m).
  - intros le' [h0 hs].
    ext x.
    apply fun_ext.
    apply N.peano_ind.
    + rewrite h0.
      apply prop_ext_eq.
      exact (N.le_0_r x).
    + intros n IH.
      rewrite hs, <- IH.
      apply prop_ext_eq.
      rewrite or_comm.
      exact (N.le_succ_r x n).
Qed.

Lemma lt_def : N.lt = (@ε (arr N (arr N (arr N Prop'))) (fun lt : N -> N -> N -> Prop => forall _2248 : N, (forall m : N, (lt _2248 m (NUMERAL N0)) = False) /\ (forall m : N, forall n : N, (lt _2248 m (N.succ n)) = ((m = n) \/ (lt _2248 m n)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))).
Proof.
  cbn.
  align_ε.
  - split.
    + intro n.
      rewrite is_False.
      exact (N.nlt_0_r n).
    + intros n m.
      apply prop_ext_eq.
      rewrite N.lt_succ_r.
      rewrite or_comm.
      exact (N.lt_eq_cases n m).
  - intros le' [h0 hs].
    ext x.
    apply fun_ext.
    apply N.peano_ind.
    + rewrite h0.
      rewrite is_False.
      exact (N.nlt_0_r x).
    + intros n IH.
      rewrite hs, <- IH.
      apply prop_ext_eq.
      rewrite N.lt_succ_r.
      rewrite or_comm.
      exact (N.lt_eq_cases x n).
Qed.

Lemma ge_def : N.ge = (fun _2249 : N => fun _2250 : N => N.le _2250 _2249).
Proof. ext x y. apply prop_ext_eq. exact (N.ge_le_iff x y). Qed.

Lemma gt_def : N.gt = (fun _2261 : N => fun _2262 : N => N.lt _2262 _2261).
Proof. ext x y. apply prop_ext_eq. exact (N.gt_lt_iff x y). Qed.

Lemma N0_le_eq_True y : N.le 0 y = True.
Proof. rewrite is_True. exact (N.le_0_l y). Qed.

Lemma succ_le_0_is_False x : N.le (N.succ x) 0 = False.
Proof. rewrite is_False. exact (N.nle_succ_0 x). Qed.

Lemma succ_eq_0_is_False x : (N.succ x = N0) = False.
Proof. rewrite is_False. exact (N.neq_succ_0 x).  Qed.

Lemma le_succ_succ x y : N.le (N.succ x) (N.succ y) = N.le x y.
Proof. symmetry. apply prop_ext_eq. exact (N.succ_le_mono x y). Qed.

Lemma MAX_def : N.max = (fun _2273 : N => fun _2274 : N => @COND N (N.le _2273 _2274) _2274 _2273).
Proof.
  ext x. apply fun_ext. pattern x. revert x. apply N.peano_ind.
  intro y. rewrite N.max_0_l, N0_le_eq_True, COND_True. reflexivity.
  intros x hx. intro y. pattern y. revert y. apply N.peano_ind.
  rewrite N.max_0_r, succ_le_0_is_False, COND_False. reflexivity.
  intros y hy. rewrite <- N.succ_max_distr, hx, le_succ_succ.
  destruct (prop_degen (N.le x y)) as [h|h]; rewrite h.
  rewrite! COND_True. reflexivity. rewrite! COND_False. reflexivity.
Qed.

Lemma MIN_def : N.min = (fun _2285 : N => fun _2286 : N => @COND N (N.le _2285 _2286) _2285 _2286).
Proof.
  ext x. apply fun_ext. pattern x. revert x. apply N.peano_ind.
  intro y. rewrite N.min_0_l, N0_le_eq_True, COND_True. reflexivity.
  intros x hx. intro y. pattern y. revert y. apply N.peano_ind.
  rewrite N.min_0_r, succ_le_0_is_False, COND_False. reflexivity.
  intros y hy. rewrite <- N.succ_min_distr, hx, le_succ_succ.
  destruct (prop_degen (N.le x y)) as [h|h]; rewrite h.
  rewrite! COND_True. reflexivity. rewrite! COND_False. reflexivity.
Qed.

Lemma minus_def : N.sub = (@ε (arr N (arr N (arr N N'))) (fun pair' : N -> N -> N -> N => forall _2766 : N, (forall m : N, (pair' _2766 m (NUMERAL N0)) = m) /\ (forall m : N, forall n : N, (pair' _2766 m (N.succ n)) = (N.pred (pair' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  cbn.
  align_ε.
  - split.
    + exact N.sub_0_r.
    + exact N.sub_succ_r.
  - intros sub' [h0 hs].
    ext x.
    apply fun_ext.
    apply N.peano_ind.
    + rewrite h0.
      exact (N.sub_0_r x).
    + intros y IH.
      rewrite hs, <- IH.
      exact (N.sub_succ_r x y).
Qed.

Definition fact := N.peano_rect (fun _ => N) 1 (fun n r => N.succ n * r).

Lemma FACT_def : fact = @ε ((prod N (prod N (prod N N))) -> N -> N) (fun FACT' : (prod N (prod N (prod N N))) -> N -> N => forall _2944 : prod N (prod N (prod N N)), ((FACT' _2944 (NUMERAL 0%N)) = (NUMERAL (BIT1 0%N))) /\ (forall n : N, (FACT' _2944 (N.succ n)) = (N.mul (N.succ n) (FACT' _2944 n)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0%N))))))))))).
Proof.
  unfold NUMERAL. cbn. align_ε.

  split. reflexivity.
  intro n. unfold fact. rewrite N.peano_rect_succ. reflexivity.

  intros f [f0 fs]. ext n. pattern n. apply N.peano_ind.
  rewrite f0. reflexivity.
  intros x h. unfold fact. rewrite fs, N.peano_rect_succ, <- h. reflexivity.
Qed.

Lemma Nadd_sub a b : a + b - a = b. Proof. lia. Qed.

Lemma Nswap_add_sub a a' b : a' <= a -> a + b - a' = a - a' + b. Proof. lia. Qed.

Lemma Ndivmod_unicity {k k' r r'} q :
  r < q -> r' < q -> k * q + r = k' * q + r' -> k = k' /\ r = r'.
Proof.
  intros h h' e. destruct (classic (N.lt k k')).
  apply False_rec.
  assert (e2 : k * q + r - k' * q = k' * q + r' - k' * q). lia.
  rewrite Nadd_sub, Nswap_add_sub, <- N.mul_sub_distr_r in e2. nia. nia.
  destruct (classic (N.lt k' k)).
  assert (e2 : k * q + r - k' * q = k' * q + r' - k' * q). lia.
  rewrite Nadd_sub, Nswap_add_sub, <- N.mul_sub_distr_r in e2. nia. nia.
  nia.
Qed.

Lemma DIV_def : N.div = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun q : (prod N (prod N N)) -> N -> N -> N => forall _3086 : prod N (prod N N), exists r : N -> N -> N, forall m : N, forall n : N, @COND Prop (n = (NUMERAL N0)) (((q _3086 m n) = (NUMERAL N0)) /\ ((r m n) = m)) ((m = (N.add (N.mul (q _3086 m n) n) (r m n))) /\ (N.lt (r m n) n))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
  cbn.
  align_ε.
  - exists N.modulo.
    intros m n.
    apply prove_COND; intro h.
    + rewrite h.
      split.
      * exact (N.div_0_r m).
      * exact (N.mod_0_r m).
    + split.
      * rewrite N.mul_comm.
        exact (N.Div0.div_mod m n).
      * exact (N.mod_lt m n h).
  - intros div' h.
    destruct h as [mod' h].
    ext x y.
    apply (COND_elim (h x y)); intros c [d m].
    + rewrite d, c.
      exact (N.div_0_r x).
    + apply (@proj1 _ (x mod y = mod' x y)).
      apply (Ndivmod_unicity y).
      * exact (N.mod_lt x y c).
      * exact m.
      * rewrite <- d, N.mul_comm.
        exact (eq_sym (N.Div0.div_mod x y)).
Qed.

Lemma MOD_def : N.modulo = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun r : (prod N (prod N N)) -> N -> N -> N => forall _3087 : prod N (prod N N), forall m : N, forall n : N, @COND Prop (n = (NUMERAL 0)) (((N.div m n) = (NUMERAL 0)) /\ ((r _3087 m n) = m)) ((m = (N.add (N.mul (N.div m n) n) (r _3087 m n))) /\ (N.lt (r _3087 m n) n))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  cbn.
  align_ε.
  - intros m n.
    apply prove_COND; intro h.
    + rewrite h.
      split.
      * exact (N.div_0_r m).
      * exact (N.mod_0_r m).
    + split.
      * rewrite N.mul_comm.
        exact (N.Div0.div_mod m n).
      * exact (N.mod_lt m n h).
  - intros mod' h.
    ext x y.
    apply (COND_elim (h x y)); intros c [d m].
    + rewrite m, c.
      exact (N.mod_0_r x).
    + apply (@proj2 (x / y = x / y)).
      apply (Ndivmod_unicity y).
      * exact (N.mod_lt x y c).
      * exact m.
      * rewrite <- d, N.mul_comm.
        exact (eq_sym (N.Div0.div_mod x y)).
Qed.

(****************************************************************************)
(* Alignment of the Even and Odd predicates. *)
(****************************************************************************)

Lemma NEven0: N.Even 0 = True.
Proof.
  rewrite is_True.
  apply (proj1 (N.even_spec 0)).
  reflexivity.
Qed.

Lemma NOdd0: N.Odd 0 = False.
Proof.
  rewrite is_False.
  apply (proj1 (not_iff_compat (N.odd_spec 0))).
  rewrite (Bool.not_true_iff_false _).
  exact N.odd_0.
Qed.

(* N.odd_odd since Coq >= 8.20 *)
Lemma odd_odd : forall n, N.odd (2 * n + 1) = true.
Proof. intros n; rewrite N.odd_spec; exists n; reflexivity. Qed.

(* N.even_odd since Coq >= 8.20 *)
Lemma even_odd : forall n, N.even (2 * n + 1) = false.
Proof. intros n; rewrite <- N.negb_odd, odd_odd; reflexivity. Qed.

(* N.even_even since Coq >= 8.20 *)
Lemma even_even : forall n, N.even (2 * n) = true.
Proof. intros n; apply N.even_spec; exists n; reflexivity. Qed.

(* N.odd_even since Coq >= 8.20 *)
Lemma odd_even : forall n, N.odd (2 * n) = false.
Proof. intros n; rewrite <- N.negb_even, even_even; reflexivity. Qed.

Lemma NEvenS: forall n: N, N.Even (N.succ n) = ~ N.Even n.
Proof.
  intro n.
  rewrite (prop_ext_eq (N.Even_succ n)).
  apply prop_ext.
    - unfold N.Odd.
      apply ex_ind.
      intros m o.
      rewrite o, <- (prop_ext_eq (N.even_spec _)), (Bool.not_true_iff_false _).
      exact (even_odd _).
    - case (N.Even_or_Odd n).
      + exact (absurd _).
      + trivial.
Qed.

Lemma NOddS: forall n: N, N.Odd (N.succ n) = ~ N.Odd n.
Proof.
  intro n.
  rewrite (prop_ext_eq (N.Odd_succ n)).
  apply prop_ext.
  - unfold N.Even.
    apply ex_ind.
    intros m o.
    rewrite o, <- (prop_ext_eq (N.odd_spec _)), (Bool.not_true_iff_false _).
    exact (odd_even _).
  - case (N.Even_or_Odd n).
    + trivial.
    + exact (absurd _).
Qed.

Lemma EVEN_def : N.Even = @ε ((prod N (prod N (prod N N))) -> N -> Prop) (fun EVEN' : (prod N (prod N (prod N N))) -> N -> Prop => forall _2603 : prod N (prod N (prod N N)), ((EVEN' _2603 (NUMERAL 0%N)) = True) /\ (forall n : N, (EVEN' _2603 (N.succ n)) = (~ (EVEN' _2603 n)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0%N))))))))))).
Proof.
  unfold NUMERAL. cbn. align_ε.
  - split.
    + exact (NEven0).
    + exact (NEvenS).
  - intros Even' [h0 hS].
    ext n.
    revert n.
    apply N.peano_ind.
    + rewrite h0.
      exact (NEven0).
    + intros n IH.
      rewrite (hS n), (NEvenS n), IH.
      reflexivity.
Qed.

Lemma ODD_def: N.Odd = @ε ((prod N (prod N N)) -> N -> Prop) (fun ODD' : (prod N (prod N N)) -> N -> Prop => forall _2607 : prod N (prod N N), ((ODD' _2607 (NUMERAL 0%N)) = False) /\ (forall n : N, (ODD' _2607 (N.succ n)) = (~ (ODD' _2607 n)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0%N)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%N)))))))))).
Proof.
  unfold NUMERAL. cbn. align_ε.
  - split.
    + exact (NOdd0).
    + exact (NOddS).
  - intros Odd' [h0 hS].
    ext n.
    revert n.
    apply N.peano_ind.
    + rewrite h0.
      exact (NOdd0).
    + intros n IH.
      rewrite (hS n), (NOddS n), IH.
      reflexivity.
Qed.

(****************************************************************************)
(* NUMPAIR(x,y) = 2^x(2y+1): bijection between N² and N-{0}. *)
(****************************************************************************)

Definition NUMPAIR := fun x : N => fun y : N => N.mul (N.pow (NUMERAL (BIT0 (BIT1 0))) x) (N.add (N.mul (NUMERAL (BIT0 (BIT1 0))) y) (NUMERAL (BIT1 0))).

Lemma NUMPAIR_def : NUMPAIR = (fun _17487 : N => fun _17488 : N => N.mul (N.pow (NUMERAL (BIT0 (BIT1 N0))) _17487) (N.add (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17488) (NUMERAL (BIT1 N0)))).
Proof. exact (eq_refl NUMPAIR). Qed.

Lemma double_0 : N.double 0 = 0. Proof. lia. Qed.

Lemma succ_0 : N.succ 0 = 1. Proof. lia. Qed.

Lemma double_1 : N.double 1 = 2. Proof. lia. Qed.

Lemma lt2le {a b} : (a < b) = (N.succ a <= b).
Proof. apply prop_ext; lia. Qed.

Lemma le_is_add {a b} : a <= b -> exists c, b = a + c.
Proof. intro h. exists (b - a). lia. Qed.

Lemma eq_mul_r {a b} : a <> 0 -> a = b * a -> b = 1.
Proof.
  intro h. rewrite <- (N.mul_1_l a) at 1. intro e. apply Nmult_reg_r in e.
  auto. auto.
Qed.

Lemma NDIV_MULT m n : m <> 0 -> (m * n) / m = n.
Proof. intro h. rewrite N.mul_comm. apply N.div_mul. exact h. Qed.

Lemma NUMPAIR_INJ : forall x1 : N, forall y1 : N, forall x2 : N, forall y2 : N, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Proof.
  intros x1 y1 x2 y2. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  unfold NUMPAIR, NUMERAL, BIT1, BIT0. rewrite double_0, succ_0, double_1.
  intro e.

  destruct (classic (x1 < x2)) as [h|h]. rewrite lt2le in h.
  apply False_rec. destruct (le_is_add h) as [k hk]. subst x2.
  generalize (f_equal (fun x => N.div x (2 ^ x1)) e).
  rewrite NDIV_MULT, N.pow_add_r, N.pow_succ_r, (N.mul_comm 2 (2 ^ x1)),
    <- !N.mul_assoc, NDIV_MULT.
  lia. lia. lia. lia.

  destruct (classic (x2 < x1)) as [i|i]. rewrite lt2le in i.
  apply False_rec. destruct (le_is_add i) as [k hk]. subst x1.
  generalize (f_equal (fun x => N.div x (2 ^ x2)) e).
  rewrite NDIV_MULT, N.pow_add_r, N.pow_succ_r, (N.mul_comm 2 (2 ^ x2)),
    <- !N.mul_assoc, NDIV_MULT.
  lia. lia. lia. lia.

  assert (j: x1 = x2). lia. subst x2. split. reflexivity. nia.
Qed.

Lemma NUMPAIR_nonzero x y : NUMPAIR x y <> 0.
Proof.
  unfold NUMPAIR, NUMERAL, BIT1, BIT0.
  rewrite double_0, succ_0, double_1, N.mul_add_distr_l, N.mul_1_r. nia.
Qed.

(****************************************************************************)
(* Inverse of NUMPAIR. *)
(****************************************************************************)

Lemma INJ_INVERSE2 {A B C : Type'} : forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Proof.
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

Definition NUMFST0_pred :=  fun X : N -> N => exists Y : N -> N, forall x : N, forall y : N, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMFST0 := ε NUMFST0_pred.

Lemma NUMFST0_NUMPAIR x y : NUMFST0 (NUMPAIR x y) = x.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists q, NUMFST0_pred q). exists fst. exists snd. assumption.
  generalize (ε_spec i). fold NUMFST0. unfold NUMFST0_pred.
  intros [snd' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMSND0_pred :=  fun Y : N -> N => exists X : N -> N, forall x : N, forall y : N, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND0 := ε NUMSND0_pred.

Lemma NUMSND0_NUMPAIR x y : NUMSND0 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND0_pred x). exists snd. exists fst. assumption.
  generalize (ε_spec i). fold NUMSND0. unfold NUMSND0_pred.
  intros [fst' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMFST := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun X : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17340 : prod N (prod N (prod N (prod N (prod N N)))), exists Y : N -> N, forall x : N, forall y : N, ((X _17340 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).

Lemma NUMFST_def : NUMFST = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun X : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17503 : prod N (prod N (prod N (prod N (prod N N)))), exists Y : N -> N, forall x : N, forall y : N, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (eq_refl NUMFST). Qed.

Lemma NUMFST_NUMPAIR x y : NUMFST (NUMPAIR x y) = x.
Proof.
  unfold NUMFST.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
          NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
  generalize (prod N (prod N (prod N (prod N (prod N N))))); intros A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (fst := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMFST0). unfold Q. intros _. exists NUMSND0.
  intros x' y'. rewrite NUMFST0_NUMPAIR, NUMSND0_NUMPAIR. auto.
  generalize (ε_spec i). change (Q fst -> fst a (NUMPAIR x y) = x). intro h.
  destruct (h a) as [snd j]. destruct (j x y) as [j1 j2]. exact j1.
Qed.

Definition NUMSND1_pred :=  fun Y : N -> N => forall x : N, forall y : N, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND1 := ε NUMSND1_pred.

Lemma NUMSND1_NUMPAIR x y : NUMSND1 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 _ NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND1_pred x). exists snd. unfold NUMSND1_pred.
  intros x' y'. rewrite NUMFST_NUMPAIR. destruct (h x' y') as [h1 h2]. auto.
  generalize (ε_spec i). fold NUMSND1. unfold NUMSND1_pred. intro j.
  destruct (j x y) as [j1 j2]. exact j2.
Qed.

Definition NUMSND := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17341 : prod N (prod N (prod N (prod N (prod N N)))), forall x : N, forall y : N, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17341 (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).

Lemma NUMSND_def : NUMSND = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17504 : prod N (prod N (prod N (prod N (prod N N)))), forall x : N, forall y : N, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (eq_refl NUMSND). Qed.

Lemma NUMSND_NUMPAIR x y : NUMSND (NUMPAIR x y) = y.
Proof.
  unfold NUMSND.
  generalize  (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
     (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
       (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
         NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))).
  generalize (prod N (prod N (prod N (prod N (prod N N))))); intros A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (snd := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMSND1). unfold Q. intros _.
  intros x' y'. rewrite NUMFST_NUMPAIR, NUMSND1_NUMPAIR. auto.
  generalize (ε_spec i). change (Q snd -> snd a (NUMPAIR x y) = y). intro h.
  destruct (h a x y) as [h1 h2]. exact h2.
Qed.

(****************************************************************************)
(* NUMSUM(b,n) = if b then 2n+1 else 2n : bijection between BxN and N. *)
(****************************************************************************)

Definition NUMSUM := fun b : Prop => fun n : N => @COND N b (N.succ (N.mul (NUMERAL (BIT0 (BIT1 0))) n)) (N.mul (NUMERAL (BIT0 (BIT1 0))) n).

Lemma NUMSUM_def : NUMSUM = (fun _17505 : Prop => fun _17506 : N => @COND N _17505 (N.succ (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17506)) (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17506)).
Proof. exact (eq_refl NUMSUM). Qed.

Definition NUMLEFT n := if N.even n then False else True.

Definition NUMRIGHT n := if N.even n then n / 2 else (n - 1) / 2.

Lemma even_double n : N.even (2 * n) = true.
Proof. rewrite N.even_spec. exists n. reflexivity. Qed.

Lemma NUMLEFT_NUMSUM b n : NUMLEFT (NUMSUM b n) = b.
Proof.
  unfold NUMSUM, NUMERAL, BIT1, BIT0, NUMLEFT.
  destruct (prop_degen b); subst; rewrite double_0, succ_0, double_1.
  rewrite COND_True, N.even_succ, N.odd_mul, N.odd_2. reflexivity.
  rewrite COND_False, even_double. reflexivity.
Qed.

Lemma succ_minus_1 x : N.succ x - 1 = x.
Proof. lia. Qed.

Lemma NUMRIGHT_NUMSUM b n : NUMRIGHT (NUMSUM b n) = n.
Proof.
  unfold NUMSUM, NUMERAL, BIT1, BIT0, NUMRIGHT.
  destruct (prop_degen b); subst; rewrite double_0, succ_0, double_1.
  rewrite COND_True, N.even_succ, N.odd_mul, N.odd_2, succ_minus_1, NDIV_MULT.
  reflexivity. lia.
  rewrite COND_False, even_double, NDIV_MULT. reflexivity. lia.
Qed.

Lemma Nplus_1_minus_1 x : x + 1 - 1 = x.
Proof. lia. Qed.

Lemma NUMSUM_surjective n : exists b x, n = NUMSUM b x.
Proof.
  exists (NUMLEFT n). exists (NUMRIGHT n). unfold NUMSUM, NUMLEFT, NUMRIGHT, NUMERAL, BIT1, BIT0.
  case_eq (N.even n); intro h.
  rewrite COND_False. rewrite N.even_spec in h. destruct h as [k h]. subst n.
  rewrite NDIV_MULT. reflexivity. lia.
  rewrite COND_True. apply eq_false_negb_true in h. change (N.odd n = true) in h.
  rewrite N.odd_spec in h. destruct h as [k h]. subst. rewrite Nplus_1_minus_1.
  rewrite NDIV_MULT. lia. lia.
Qed.

Lemma NUMLEFT_def : NUMLEFT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop) (fun X : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop => forall _17372 : prod N (prod N (prod N (prod N (prod N (prod N N))))), exists Y : N -> N, forall x : Prop, forall y : N, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  cbn.
  align_ε.
  - exists NUMRIGHT.
    intros x y.
    split.
    + exact (NUMLEFT_NUMSUM x y).
    + exact (NUMRIGHT_NUMSUM x y).
  - intros NUMLEFT' h.
    destruct h as [NUMRIGHT' h].
    ext s.
    destruct (NUMSUM_surjective s) as [b [x k]].
    rewrite k, (NUMLEFT_NUMSUM b x), (proj1 (h b x)).
    reflexivity.
Qed.

Lemma NUMRIGHT_def : NUMRIGHT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N => forall _17373 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), forall x : Prop, forall y : N, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  cbn.
  align_ε.
  - intros x y.
    split.
    + exact (NUMLEFT_NUMSUM x y).
    + exact (NUMRIGHT_NUMSUM x y).
  - intros NUMRIGHT' h.
    ext s.
    destruct (NUMSUM_surjective s) as [b [x k]].
    rewrite k, (NUMRIGHT_NUMSUM b x), (proj2 (h b x)).
    reflexivity.
Qed.

(****************************************************************************)
(* Alignment of well-foundedness.
HOL Light: non-empty subsets has minimal, Coq: has induction *)
(****************************************************************************)

Require Import Coq.Init.Wf.

Definition well_founded := Coq.Init.Wf.well_founded.

Lemma WF_def {A : Type'} : (@well_founded A) = (fun _6923 : A -> A -> Prop => forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (_6923 y x) -> ~ (P y))).
Proof.
  ext R.
  apply prop_ext; intro H.
  - intros X ne.
    destruct ne as [x Hx].
    rewrite <- (not_not_eq _); intro goal.
    case (prop_degen (forall y: A, ~ X y)); intro h.
    + rewrite is_True in h.
      assert (~ X x) by exact (h x).
      contradiction.
    + rewrite is_False in h.
      apply h.
      apply (well_founded_induction H).
      intros y g Xy.
      apply goal.
      exists y.
      split; assumption.
  - unfold well_founded.
    case (prop_degen (forall a : A, Acc R a)); intro h.
    + rewrite is_True in h.
      assumption.
    + rewrite is_False, not_forall_eq in h.
      apply except.
      assert (G: exists x : A, ~ Acc R x /\ (forall y : A, R y x -> ~~ Acc R y))
        by apply (H _ h).
      destruct G as [x Gx].
      destruct Gx as [H0 H1].
      apply H0.
      apply Acc_intro.
      intros y Ryx.
      rewrite <- (not_not_eq _).
      apply H1.
      assumption.
Qed.

(****************************************************************************)
(* Alignment of  measures, that is functions A -> N which creates a wf order by inverse image *)
(****************************************************************************)

Require Import Coq.Arith.PeanoNat.

Lemma inj_lt m n: (N.to_nat m > N.to_nat n)%nat = (n < m).
Proof.
  apply prop_ext; intro h.
  - unfold N.lt.
    rewrite (Nnat.N2Nat.inj_compare n m).
    apply (proj2 (Nat.compare_lt_iff _ _)).
    assumption.
  - apply (proj1 (Nat.compare_lt_iff _ _)).
    rewrite <- (Nnat.N2Nat.inj_compare n m).
    unfold N.lt in h.
    assumption.
Qed.

(*Definition MEASURE {A : Type'} : (A -> N) -> A -> A -> Prop := fun f : A -> N => @Wf_nat.gtof A (fun x : A => N.to_nat (f x)).

Lemma MEASURE_def {A : Type'} : (fun f : A -> N => @Wf_nat.gtof A (fun x : A => N.to_nat (f x))) = (fun _8094 : A -> N => fun x : A => fun y : A => N.lt (_8094 x) (_8094 y)).
Proof.
  apply fun_ext; intro f.
  unfold Wf_nat.gtof, MEASURE.
  ext x y.
  exact (inj_lt _ _).
Qed.*)

(****************************************************************************)
(* Alignment of recspace, the HOL-Light type used to encode inductive types. *)
(****************************************************************************)

Definition INJN {A : Type'} := fun x : N => fun n : N => fun a : A => n = x.

Lemma INJN_def {A : Type'} : (@INJN A) = (fun _17537 : N => fun n : N => fun a : A => n = _17537).
Proof. exact (eq_refl (@INJN A)). Qed.

Definition INJA {A : Type'} := fun x : A => fun n : N => fun b : A => b = x.

Lemma INJA_def {A : Type'} : (@INJA A) = (fun _17542 : A => fun n : N => fun b : A => b = _17542).
Proof. exact (eq_refl (@INJA A)). Qed.

Definition INJF {A : Type'} := fun f : N -> N -> A -> Prop => fun n : N => f (NUMFST n) (NUMSND n).

Lemma INJF_def {A : Type'} : (@INJF A) = (fun _17549 : N -> N -> A -> Prop => fun n : N => _17549 (NUMFST n) (NUMSND n)).
Proof. exact (eq_refl (@INJF A)). Qed.

Definition INJP {A : Type'} := fun f : N -> A -> Prop => fun g : N -> A -> Prop => fun n : N => fun a : A => @COND Prop (NUMLEFT n) (f (NUMRIGHT n) a) (g (NUMRIGHT n) a).

Lemma INJP_def {A : Type'} : (@INJP A) = (fun _17554 : N -> A -> Prop => fun _17555 : N -> A -> Prop => fun n : N => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)).
Proof. exact (eq_refl (@INJP A)). Qed.

Definition ZCONSTR {A : Type'} := fun n : N => fun a : A => fun f : N -> N -> A -> Prop => @INJP A (@INJN A (N.succ n)) (@INJP A (@INJA A a) (@INJF A f)).

Lemma ZCONSTR_def {A : Type'} : (@ZCONSTR A) = (fun _17566 : N => fun _17567 : A => fun _17568 : N -> N -> A -> Prop => @INJP A (@INJN A (N.succ _17566)) (@INJP A (@INJA A _17567) (@INJF A _17568))).
Proof. exact (eq_refl (@ZCONSTR A)). Qed.

Definition ZBOT {A : Type'} := @INJP A (@INJN A (NUMERAL 0)) (@ε (N -> A -> Prop) (fun z : N -> A -> Prop => True)).

Lemma ZBOT_def {A : Type'} : (@ZBOT A) = (@INJP A (@INJN A (NUMERAL N0)) (@ε (N -> A -> Prop) (fun z : N -> A -> Prop => True))).
Proof. exact (eq_refl (@ZBOT A)). Qed.

Inductive _ZRECSPACE {A : Type'} : (N -> A -> Prop) -> Prop :=
| ZRECSPACE0 : _ZRECSPACE ZBOT
| ZRECSPACE1 c i r : (forall n, _ZRECSPACE (r n)) -> _ZRECSPACE (ZCONSTR c i r).

Definition ZRECSPACE {A:Type'} := @_ZRECSPACE A.

Lemma ZRECSPACE_def {A : Type'} : (@ZRECSPACE A) = (fun a : N -> A -> Prop => forall ZRECSPACE' : (N -> A -> Prop) -> Prop, (forall a' : N -> A -> Prop, ((a' = (@ZBOT A)) \/ (exists c : N, exists i : A, exists r : N -> N -> A -> Prop, (a' = (@ZCONSTR A c i r)) /\ (forall n : N, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a).
Proof.
  ext a. apply prop_ext.
  induction 1; intros a h; apply h. left. reflexivity.
  right. exists c. exists i. exists r. split. reflexivity. intro n. apply (H0 n a h).
  intro h. apply h. intros a' [e|[c [i [r [e j]]]]]; subst.
  apply ZRECSPACE0. apply ZRECSPACE1. exact j.
Qed.

Definition recspace : Type' -> Type' := fun A => subtype (@ZRECSPACE0 A).

Definition _dest_rec : forall {A : Type'}, (recspace A) -> N -> A -> Prop :=
  fun A => dest (@ZRECSPACE0 A).

Definition _mk_rec : forall {A : Type'}, (N -> A -> Prop) -> recspace A :=
  fun A => mk (@ZRECSPACE0 A).

Lemma axiom_10 : forall {A : Type'} (r : N -> A -> Prop), (@ZRECSPACE A r) = ((@_dest_rec A (@_mk_rec A r)) = r).
Proof. intros A r. apply dest_mk. Qed.

Lemma axiom_9 : forall {A : Type'} (a : recspace A), (@_mk_rec A (@_dest_rec A a)) = a.
Proof. intros A a. apply mk_dest. Qed.

Definition BOTTOM {A : Type'} := @_mk_rec A (@ZBOT A).

Lemma BOTTOM_def {A : Type'} : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. exact (eq_refl (@BOTTOM A)). Qed.

Definition CONSTR {A : Type'} := fun n : N => fun a : A => fun f : N -> recspace A => @_mk_rec A (@ZCONSTR A n a (fun x : N => @_dest_rec A (f x))).

Lemma CONSTR_def {A : Type'} : (@CONSTR A) = (fun _17591 : N => fun _17592 : A => fun _17593 : N -> recspace A => @_mk_rec A (@ZCONSTR A _17591 _17592 (fun n : N => @_dest_rec A (_17593 n)))).
Proof. exact (eq_refl (@CONSTR A)). Qed.

Lemma NUMSUM_INJ : forall b1 : Prop, forall x1 : N, forall b2 : Prop, forall x2 : N, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Proof.
  intros b1 x1 b2 x2. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  unfold NUMSUM. unfold NUMERAL, BIT1, BIT0.
  destruct (prop_degen b1); destruct (prop_degen b2); subst; try rewrite !COND_True; try rewrite !COND_False; intro e.
  split. auto. lia.
  apply False_rec. lia.
  apply False_rec. lia.
  split. auto. lia.
Qed.

Lemma INJN_INJ {A : Type'} : forall n1 : N, forall n2 : N, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof.
  intros n1 n2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. generalize (ext_fun e n1); clear e; intro e.
  generalize (ext_fun e (el A)); clear e. unfold INJN.
  rewrite refl_is_True, sym, is_True. auto.
Qed.

Lemma INJA_INJ {A : Type'} : forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof.
  intros a1 a2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. generalize (ext_fun e 0); clear e; intro e.
  generalize (ext_fun e a2); clear e. unfold INJA.
  rewrite refl_is_True, is_True. auto.
Qed.

Lemma INJF_INJ {A : Type'} : forall f1 : N -> N -> A -> Prop, forall f2 : N -> N -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof.
  intros f1 f2. apply prop_ext. 2: intro e; subst; reflexivity.
  intro e. ext x y a.
  generalize (ext_fun e (NUMPAIR x y)); clear e; intro e.
  generalize (ext_fun e a); clear e. unfold INJF.
  rewrite NUMFST_NUMPAIR, NUMSND_NUMPAIR. auto.
Qed.

Lemma Nodd_double n : N.odd (2 * n) = false.
Proof. rewrite N.odd_mul, N.odd_2. reflexivity. Qed.

Lemma Neven_double n : N.even (2 * n) = true.
Proof. rewrite N.even_spec. exists n. reflexivity. Qed.

Lemma INJP_INJ {A : Type'} : forall f1 : N -> A -> Prop, forall f1' : N -> A -> Prop, forall f2 : N -> A -> Prop, forall f2' : N -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Proof.
  intros f1 f1' f2 f2'. apply prop_ext. 2: intros [e1 e2]; subst; reflexivity.
  intro e.
  assert (e1: forall x a, INJP f1 f2 x a = INJP f1' f2' x a).
  intros x a. rewrite e. reflexivity.
  split; ext x a.
  generalize (e1 (N.succ (2 * x)) a). unfold INJP, NUMLEFT, NUMRIGHT.
  rewrite N.even_succ, Nodd_double, !COND_True, succ_minus_1, NDIV_MULT. auto. lia.
  generalize (e1 (2 * x) a). unfold INJP, NUMLEFT, NUMRIGHT.
  rewrite Neven_double, !COND_False, NDIV_MULT. auto. lia.
Qed.

Lemma ZCONSTR_INJ {A : Type'} c1 i1 r1 c2 i2 r2 : @ZCONSTR A c1 i1 r1 = ZCONSTR c2 i2 r2 -> c1 = c2 /\ i1 = i2 /\ r1 = r2.
Proof.
  unfold ZCONSTR. intro e.
  rewrite INJP_INJ in e. destruct e as [e1 e2].
  rewrite INJN_INJ in e1. rewrite INJP_INJ in e2. destruct e2 as [e2 e3].
  rewrite INJA_INJ in e2. rewrite INJF_INJ in e3. apply N.succ_inj in e1. auto.
Qed.

Lemma MK_REC_INJ {A : Type'} : forall x : N -> A -> Prop, forall y : N -> A -> Prop, ((@_mk_rec A x) = (@_mk_rec A y)) -> ((@ZRECSPACE A x) /\ (@ZRECSPACE A y)) -> x = y.
Proof.
  intros x y e [hx hy]. rewrite axiom_10 in hx. rewrite axiom_10 in hy.
  rewrite <- hx, <- hy, e. reflexivity.
Qed.

Lemma CONSTR_INJ : forall {A : Type'}, forall c1 : N, forall i1 : A, forall r1 : N -> recspace A, forall c2 : N, forall i2 : A, forall r2 : N -> recspace A, ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Proof.
  intros A c1 i1 r1 c2 i2 r2. apply prop_ext.
  2: intros [e1 [e2 e3]]; subst; reflexivity.
  unfold CONSTR. intro e. apply MK_REC_INJ in e. apply ZCONSTR_INJ in e.
  destruct e as [e1 [e2 e3]]. split. auto. split. auto. ext x.
  apply dest_inj. generalize (ext_fun e3 x). auto.
  split; apply ZRECSPACE1; intro n. destruct (r1 n). auto. destruct (r2 n). auto.
Qed.

(****************************************************************************)
(* Alignment of the sum type constructor. *)
(****************************************************************************)

Definition sum' (A B : Type') : Type' := {| type:= sum A B; el := inl (el A) |}.
Canonical sum'.

Definition _dest_sum : forall {A B : Type'}, sum A B -> recspace (prod A B) :=
fun A B p => match p with
| inl a => CONSTR (NUMERAL N0) (a , ε (fun _ => True)) (fun _ => BOTTOM)
| inr b => CONSTR (N.succ (NUMERAL N0)) (ε (fun _ => True) , b) (fun _ => BOTTOM)
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
  intros A B a. unfold _mk_sum. apply _dest_sum_inj.
  rewrite sym. apply (@ε_spec (sum A B)). exists a. reflexivity.
Qed.

Lemma axiom_12 : forall {A B : Type'} (r : recspace (prod A B)), ((fun a : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = ((fun a''' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a''' (@ε B (fun v : B => True))) (fun n : N => @BOTTOM (prod A B))) a'')) \/ (exists a'' : B, a' = ((fun a''' : B => @CONSTR (prod A B) (N.succ (NUMERAL N0)) (@pair A B (@ε A (fun v : A => True)) a''') (fun n : N => @BOTTOM (prod A B))) a''))) -> sum' a') -> sum' a) r) = ((@_dest_sum A B (@_mk_sum A B r)) = r).
Proof.
  intros. apply prop_ext.
  intro h. unfold _mk_sum. rewrite sym. apply (@ε_spec (sum' A B)).
  apply (h (fun r : recspace (prod A B) => exists x : sum' A B, r = _dest_sum x)).
  intros. destruct H. destruct H. exists (inl(x)). simpl. exact H.

  destruct H. exists (inr(x)). simpl. exact H.

  intro e. rewrite <- e. intros P h. apply h. destruct (_mk_sum r).
  simpl. left. exists t. reflexivity. right. exists t. reflexivity.
Qed.

Lemma INL_def {A B : Type'} : (@inl A B) = (fun a : A => @_mk_sum A B ((fun a' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : N => @BOTTOM (prod A B))) a)).
Proof.
  ext a. apply _dest_sum_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite sym. rewrite <- axiom_12. doesn't work *)
  unfold _mk_sum. assert (h: exists p, r = _dest_sum p).
  exists (inl a). simpl. reflexivity.
  generalize (ε_spec h). set (o := ε (fun p : sum' A B => _dest_sum p = r)).
  auto.
Qed.

Lemma INR_def {A B : Type'} : (@inr A B) = (fun a : B => @_mk_sum A B ((fun a' : B => @CONSTR (prod A B) (N.succ (NUMERAL N0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : N => @BOTTOM (prod A B))) a)).
Proof.
  ext b. apply _dest_sum_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite sym. rewrite <- axiom_12. doesn't work *)
  unfold _mk_sum. assert (h: exists p, r = _dest_sum p).
  exists (inr(b)). simpl. reflexivity.
  generalize (ε_spec h). set (o := ε (fun p : sum' A B => _dest_sum p = r)).
  auto.
Qed.

(****************************************************************************)
(* Alignment of the option type constructor. *)
(****************************************************************************)

Definition option' (A : Type') := {| type := option A; el := None |}.
Canonical option'.

Definition _dest_option : forall {A : Type'}, option A -> recspace A :=
  fun A o =>
    match o with
    | None => CONSTR (NUMERAL N0) (ε (fun _ => True)) (fun _ => BOTTOM)
    | Some a => CONSTR (N.succ (NUMERAL N0)) a (fun _ => BOTTOM)
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
       a' = CONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => BOTTOM) \/
       (exists a'' : A, a' = CONSTR (N.succ (NUMERAL N0)) a'' (fun _ : N => BOTTOM)) ->
       option' a') -> option' r.

Inductive option_ind {A : Type'} : recspace A -> Prop :=
| option_ind0 : option_ind (CONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => BOTTOM))
| option_ind1 a'' : option_ind (CONSTR (N.succ (NUMERAL N0)) a'' (fun _ : N => BOTTOM)).

Lemma option_eq {A : Type'} : @option_pred A = @option_ind A.
Proof.
  ext r. apply prop_ext.
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
  right. exists t. reflexivity. left. reflexivity.
Qed.

Lemma axiom_14 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (N.succ (NUMERAL N0)) a''' (fun n : N => @BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof. intros A r. apply axiom_14'. Qed.

Lemma NONE_def {A : Type'} : (@None A) = (@_mk_option A (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))).
Proof.
  apply _dest_option_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite <- axiom_14'. doesn't work *)
  unfold _mk_option.
  assert (h: exists o, @_mk_option_pred A r o). exists None. reflexivity.
  generalize (ε_spec h).
  set (o := ε (_mk_option_pred r)). unfold _mk_option_pred. auto.
Qed.

Lemma SOME_def {A : Type'} : (@Some A) = (fun a : A => @_mk_option A ((fun a' : A => @CONSTR A (N.succ (NUMERAL N0)) a' (fun n : N => @BOTTOM A)) a)).
Proof.
  ext a. apply _dest_option_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* rewrite <- axiom_14'. doesn't work *)
  unfold _mk_option.
  assert (h: exists o, @_mk_option_pred A r o). exists (Some a). reflexivity.
  generalize (ε_spec h).
  set (o := ε (_mk_option_pred r)). unfold _mk_option_pred. auto.
Qed.

(****************************************************************************)
(* Alignment of the list type constructor. *)
(****************************************************************************)

Definition list' (A : Type') := {| type := list A; el := nil |}.
Canonical list'.

Definition FCONS {A : Type'} (a : A) (f: N -> A) (n : N) : A :=
  N.recursion a (fun n _ => f n) n.

Lemma FCONS_def {A : Type'} : @FCONS A = @ε ((prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A) (fun FCONS' : (prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A => forall _17460 : prod N (prod N (prod N (prod N N))), (forall a : A, forall f : N -> A, (FCONS' _17460 a f (NUMERAL N0)) = a) /\ (forall a : A, forall f : N -> A, forall n : N, (FCONS' _17460 a f (N.succ n)) = (f n))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
    (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
          NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))); intro p.
  ext a f n.
  match goal with [|- _ = ε ?x _ _ _ _] => set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => @FCONS A).
  unfold Q, FCONS, NUMERAL. intros _. split; intros b g.
  apply N.recursion_0.
  intro x. rewrite N.recursion_succ. reflexivity. reflexivity.
  intros n1 n2 n12 a1 a2 a12. subst n2. subst a2. reflexivity.
  generalize (ε_spec i). intro H. unfold Q at 1 in H.
  generalize (H p); intros [h1 h2].
  destruct (N0_or_succ n) as [|[m j]]; subst n; unfold FCONS.
  rewrite h1. apply N.recursion_0.
  rewrite h2. rewrite N.recursion_succ. reflexivity. reflexivity.
  intros n1 n2 n12 a1 a2 a12. subst n2. subst a2. reflexivity.
Qed.

Fixpoint _dest_list {A : Type'} l : recspace A :=
  match l with
  | nil => CONSTR (NUMERAL N0) (ε (fun _ => True)) (fun _ => BOTTOM)
  | cons a l => CONSTR (N.succ (NUMERAL N0)) a (FCONS (_dest_list l) (fun _ => BOTTOM))
  end.

Definition _mk_list_pred {A : Type'} (r : recspace A) : list A -> Prop :=
  fun l => _dest_list l = r.

Definition _mk_list : forall {A : Type'}, (recspace A) -> list A :=
  fun A r => ε (_mk_list_pred r).

Lemma FCONS_0 {A : Type'} (a : A) (f : N -> A) : FCONS a f (NUMERAL N0) = a.
Proof. reflexivity. Qed.

Lemma _dest_list_inj :
  forall {A : Type'} (l l' : list A), _dest_list l = _dest_list l' -> l = l'.
Proof.
  induction l; induction l'; simpl; rewrite (@CONSTR_INJ A); intros [e1 [e2 e3]].
  reflexivity. discriminate. discriminate. rewrite e2. rewrite (@IHl l'). reflexivity.
  rewrite <- (FCONS_0 (_dest_list l) ((fun _ : N => BOTTOM))).
  rewrite <- (FCONS_0 (_dest_list l') ((fun _ : N => BOTTOM))).
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
  a' = CONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => BOTTOM) \/
  (exists (a0 : A) (a1 : recspace A), a' = CONSTR (N.succ (NUMERAL N0)) a0 (FCONS a1 (fun _ : N => BOTTOM)) /\ list'0 a1) -> list'0 a')
  -> list'0 r.

Inductive list_ind {A : Type'} : recspace A -> Prop :=
| list_ind0 : list_ind (CONSTR (NUMERAL N0) (ε (fun _ : A => True)) (fun _ : N => BOTTOM))
| list_ind1 a'' l'': list_ind (CONSTR (N.succ (NUMERAL N0)) a'' (FCONS (_dest_list l'') (fun _ : N => BOTTOM))).

Lemma list_eq {A : Type'} : @list_pred A = @list_ind A.
Proof.
  ext r. apply prop_ext.
  intro h. apply h. intros r' H. destruct H. rewrite H. exact list_ind0. destruct H. destruct H. destruct H. rewrite H. destruct H0.
  assert (_dest_list nil = @CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A)).
  reflexivity. rewrite <- H0. exact (list_ind1 x nil).
  assert (_dest_list (cons a'' l'') = @CONSTR A (N.succ (NUMERAL N0)) a'' (@FCONS (recspace A) (@_dest_list A l'') (fun n : N => @BOTTOM A))).
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
  left. reflexivity. right. exists t. exists (_dest_list l). split.
  reflexivity. apply h. generalize l.
  induction l0. left; reflexivity. right. exists a. exists (_dest_list l0). split.
  reflexivity. apply h. exact IHl0.
Qed.

Lemma axiom_16 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall list' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => @CONSTR A (N.succ (NUMERAL N0)) a0' (@FCONS (recspace A) a1' (fun n : N => @BOTTOM A))) a0 a1)) /\ (list' a1))) -> list' a') -> list' a) r) = ((@_dest_list A (@_mk_list A r)) = r).
Proof. intros A r. apply axiom_16'. Qed.

Lemma NIL_def {A : Type'} : (@nil A) = (@_mk_list A (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))).
Proof.
  apply _dest_list_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  (* the sequence rewrite sym. rewrite <- axiom_16' doesn't work *)
  unfold _mk_list.
  assert (h: exists l, @_mk_list_pred A r l). exists nil. reflexivity.
  generalize (ε_spec h).
  set (l := ε (_mk_list_pred r)). unfold _mk_list_pred. auto.
Qed.

Lemma CONS_def {A : Type'} : (@cons A) = (fun a0 : A => fun a1 : list A => @_mk_list A ((fun a0' : A => fun a1' : recspace A => @CONSTR A (N.succ (NUMERAL N0)) a0' (@FCONS (recspace A) a1' (fun n : N => @BOTTOM A))) a0 (@_dest_list A a1))).
Proof.
  ext a l. apply _dest_list_inj. simpl.
  match goal with [|- ?x = _] => set (r := x) end.
  unfold _mk_list.
  assert (h: exists l', @_mk_list_pred A r l'). exists (cons a l). reflexivity.
  generalize (ε_spec h).
  set (l' := ε (_mk_list_pred r)). unfold _mk_list_pred. auto.
Qed.

Require Import Coq.Lists.List.

Lemma APPEND_def {A : Type'} : (@app A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list' A) -> (list' A) -> list' A) (fun APPEND' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> (list A) -> list A => forall _17935 : prod N (prod N (prod N (prod N (prod N N)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  ext l. simpl.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @app A). unfold Q. intros. auto.
  generalize (ε_spec i). intro H. symmetry. ext l'.
  generalize (NUMERAL (BIT1 32), (NUMERAL 80, (NUMERAL 80, (NUMERAL (BIT1 34), (NUMERAL 78, NUMERAL 68))))); intro p.
  induction l as [|a l]. simpl. apply H.
  assert (ε Q p (a :: l) l' = (a :: (ε Q p l l'))). apply H. simpl. rewrite <- IHl. apply H0.
Qed.

Lemma REVERSE_def {A : Type'} : (@rev A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list' A) -> list' A) (fun REVERSE' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list A) -> list A => forall _17939 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@app A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))).
Proof.
  ext l. simpl.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @rev A). unfold Q. intros. auto.
  generalize (ε_spec i). intro H. symmetry.
  induction l as [|a l]. simpl. apply H.
  simpl. rewrite <- IHl.
  generalize (NUMERAL 82,
              (NUMERAL (BIT1 34),
                (NUMERAL 86,
                  (NUMERAL (BIT1 34),
                    (NUMERAL 82, (NUMERAL (BIT1 (BIT1 20)),
                      NUMERAL (BIT1 34))))))); intro p.
  assert (ε Q p (a :: l) = (ε Q p l) ++ (a :: nil)). apply H. apply H0.
Qed.

(*Lemma LENGTH_def {A : Type'} : (@length A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> N) (fun LENGTH' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> N => forall _17943 : prod N (prod N (prod N (prod N (prod N N)))), ((LENGTH' _17943 (@nil A)) = (NUMERAL N0)) /\ (forall h : A, forall t : list A, (LENGTH' _17943 (@cons A h t)) = (N.succ (LENGTH' _17943 t)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))), (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))), NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))); intro p.
  apply fun_ext. intro l. simpl.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @length A). unfold Q. auto.
  generalize (ε_spec i). intro H. symmetry.
  induction l. simpl. apply H.
  simpl. rewrite <- IHl. apply H.
Qed.*)

Lemma MAP_def {A B : Type'} : (@map A B) = (@ε ((prod N (prod N N)) -> (A -> B) -> (list' A) -> list' B) (fun MAP' : (prod N (prod N N)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod N (prod N N), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
              (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
                NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))); intro p.
  ext f l.
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
  induction l0 as [|a l0]. symmetry. assert ((@nil A = nil) = True). apply prop_ext. auto. auto.
  rewrite H. apply COND_True.
  assert ((a :: l0 = nil) = False). apply prop_ext. intro.
  assert (nil <> a :: l0). apply nil_cons. easy. easy.
  rewrite H. symmetry. apply COND_False.
Qed.

Lemma BUTLAST_def {_25251 : Type'} : (@removelast _25251) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list' _25251) -> list' _25251) (fun BUTLAST' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list _25251) -> list _25251 => forall _17958 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((BUTLAST' _17958 (@nil _25251)) = (@nil _25251)) /\ (forall h : _25251, forall t : list _25251, (BUTLAST' _17958 (@cons _25251 h t)) = (@COND (list' _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (BUTLAST' _17958 t))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
              (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
                (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
                  (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
                    (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
                      (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
                        NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))); intro p.
  ext l.
  match goal with |- _ = ε ?x _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @removelast _25251). unfold Q. intro. split.
  simpl. reflexivity.
  intros. simpl. apply COND_list.
  generalize (ε_spec i). intro H. symmetry.
  induction l as [|a l]. simpl. apply H.
  assert (ε Q p (a :: l) = COND (l = nil) nil (a :: ε Q p l)).
  apply H. simpl. rewrite <- IHl. transitivity (COND (l = nil) nil (a :: ε Q p l)).
  exact H0. symmetry. apply COND_list.
Qed.

Lemma ALL_def {_25307 : Type'} : (@Forall _25307) = (@ε ((prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop) (fun ALL' : (prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod N (prod N N), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
    (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
      NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))); intro p.
  ext P l.
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => @Forall _25307).
  unfold Q. intro. split. intro. apply prop_ext. trivial. intro. apply Forall_nil.
  intros h P0 t. apply prop_ext; apply Forall_cons_iff.
  generalize (ε_spec i). intro. induction l as [|a l]; destruct (H p) as [H1 H2].
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

Lemma PAIRWISE_def {A : Type'} : (@ForallOrdPairs A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop) (fun PAIRWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop => forall _18057 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18057 r (@nil A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : list A, (PAIRWISE' _18057 r (@cons A h t)) = ((@Forall A (r h) t) /\ (PAIRWISE' _18057 r t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  generalize (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
    (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
          (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
            (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
              (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
                NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))); intro p.
  ext R l.
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _ => @ForallOrdPairs A).
  unfold Q. intro. split. apply ForallOrdPairs_nil. intros h r t; apply ForallOrdPairs_cons.
  generalize (ε_spec i). intro H. symmetry. induction l as [|a l]. rewrite ForallOrdPairs_nil.
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

Lemma FILTER_def {_25594 : Type'} : (@filter _25594) = (@ε ((prod N
(prod N (prod N (prod N (prod N N))))) -> (_25594 -> Prop)
-> (list _25594) -> list _25594) (fun FILTER' : (prod N (prod N
(prod N (prod N (prod N N))))) -> (_25594 -> Prop) -> (list
_25594) -> list _25594 => forall _18022 : prod N (prod N (prod N
(prod N (prod N N)))), (forall P : _25594 -> Prop, (FILTER'
_18022 P (@nil _25594)) = (@nil _25594)) /\ (forall h : _25594, forall
P : _25594 -> Prop, forall t : list _25594, (FILTER' _18022 P (@cons
_25594 h t)) = (@COND (list _25594) (P h) (@cons _25594 h (FILTER'
_18022 P t)) (FILTER' _18022 P t)))) (@pair N (prod N (prod N
(prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0
(BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N)))
(NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair
N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0
(BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0
(BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1
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

Lemma MEM_def {_25376 : Type'} : (@In _25376) = (@ε ((prod N (prod N N)) -> _25376 -> (list _25376) -> Prop) (fun MEM' : (prod N (prod N N)) -> _25376 -> (list _25376) -> Prop => forall _17995 : prod N (prod N N), (forall x : _25376, (MEM' _17995 x (@nil _25376)) = False) /\ (forall h : _25376, forall x : _25376, forall t : list _25376, (MEM' _17995 x (@cons _25376 h t)) = ((x = h) \/ (MEM' _17995 x t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
    (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
      NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))); intro p.
  ext x l.
  match goal with |- _ = ε ?x _ _ _=> set (Q := x) end.
  assert (i : exists q, Q q). exists (fun _=> @In _25376). unfold Q. intro. simpl.
  split. trivial. intros. apply prop_ext. intro. destruct H. symmetry in H. left. exact H. right. exact H.
  intro. destruct H. left. symmetry in H. exact H. right. exact H.
  generalize (ε_spec i). intro H. symmetry. induction l as [|a l]; simpl. apply H. rewrite <- IHl.
  transitivity ((x = a \/ ε Q p x l)). apply H. apply prop_ext.
  intro. destruct H0. left. symmetry. exact H0. right. exact H0.
  intro. destruct H0. left. symmetry. exact H0. right. exact H0.
Qed.

(*Definition repeat_with_perm_args {A: Type'} (n: N) (a: A) := @repeat A a n.

Lemma REPLICATE_def {_25272 : Type'} : (@repeat_with_perm_args _25272) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> N -> _25272 -> list _25272) (fun REPLICATE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> N -> _25272 -> list _25272 => forall _17962 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall x : _25272, (REPLICATE' _17962 (NUMERAL N0) x) = (@nil _25272)) /\ (forall n : N, forall x : _25272, (REPLICATE' _17962 (N.succ n) x) = (@cons _25272 x (REPLICATE' _17962 n x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))))).
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
Qed.*)

(*
Definition fold_right_with_perm_args {A B : Type'} (f: A -> B -> B) (l: list A) (b: B) : B := @fold_right B A f b l.

Lemma ITLIST_def {A B : Type'} : (@fold_right_with_perm_args A B) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> (list A) -> B -> B) (fun ITLIST' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> (list A) -> B -> B => forall _18151 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall b : B, (ITLIST' _18151 f (@nil A) b) = b) /\ (forall h : A, forall f : A -> B -> B, forall t : list A, forall b : B, (ITLIST' _18151 f (@cons A h t) b) = (f h (ITLIST' _18151 f t b)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof.
  generalize (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
    (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
          (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
            NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))); intro p.
  apply fun_ext; intro f. apply fun_ext; intro l. apply fun_ext; intro a.
  match goal with |- _ = ε ?x _ _ _ _ => set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @fold_right_with_perm_args A B).
  unfold Q. intro. simpl. auto.
  generalize (ε_spec i). intro H. symmetry. induction l; simpl. apply H.
  rewrite <- IHl. apply H.
Qed.
*)

Definition HD {A : Type'} := @ε ((prod N N) -> (list A) -> A) (fun HD' : (prod N N) -> (list A) -> A => forall _17927 : prod N N, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))).

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
  ext l. unfold hd, HD.
  generalize (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
    NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))); intro p.
  match goal with |- _ = ε ?x _ _=> set (Q := x) end.
  assert (i: exists q, Q q). exists (fun _ => @hd A).
  unfold Q. intro. simpl. trivial.
  generalize (ε_spec i). intro H. destruct l; simpl. reflexivity. rewrite H. reflexivity.
Qed.

Definition TL {A : Type'} := (@ε ((prod N N) -> (list A) -> list A) (fun TL' : (prod N N) -> (list A) -> list A => forall _17931 : prod N N, forall h : A, forall t : list A, (TL' _17931 (@cons A h t)) = t) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).

Definition tl {A : Type'} (l : list A) :=
match l with
| nil => @TL A nil
| cons h t => @tl A (cons h t)
end.

Lemma TL_def {A : Type'} : @tl A = @TL A.
Proof.
  ext l. destruct l. simpl. reflexivity. unfold TL.
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

Lemma nth_of_0 {A: Type'} (l: list A) d : nth (NUMERAL N0) l d =
List.hd d l.  Proof. destruct l;
simpl. reflexivity. symmetry. reflexivity. Qed.

Lemma nth_of_Suc {A: Type'} (n: N) (l: list A) d : nth (N.succ n) l d =
nth n (List.tl l) d.  Proof. destruct l; simpl. destruct n; simpl;
reflexivity. reflexivity. Qed.

Definition EL {A: Type'} (n: N) (l: list A) : A := @nth A n l (HD
nil).

Lemma EL_def {_25569 : Type'} : (@EL _25569) = (@ε ((prod N N) ->
N -> (list _25569) -> _25569) (fun EL' : (prod N N) -> N ->
(list _25569) -> _25569 => forall _18015 : prod N N, (forall l :
list _25569, (EL' _18015 (NUMERAL N0) l) = (@hd _25569 l)) /\ (forall n
: N, forall l : list _25569, (EL' _18015 (N.succ n) l) = (EL' _18015 n
(@tl _25569 l)))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0
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
(* Alignment of the type of ASCII characters. *)
(****************************************************************************)

(* Note the mismatch between Coq's ascii which takes booleans as arguments
and HOL-Light's char which takes propositions as arguments. *)

Require Import Coq.Strings.Ascii.

Definition ascii' := {| type := ascii; el := zero |}.
Canonical ascii'.

Definition _dest_char : ascii -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) :=
fun a => match a with
| Ascii a0 a1 a2 a3 a4 a5 a6 a7 => (fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7
end.

Definition _mk_char_pred (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) : ascii -> Prop :=
  fun a => _dest_char a = r.

Definition _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> ascii :=
  fun r => ε (_mk_char_pred r).

Lemma is_true_inj (b b' : bool) : is_true b = is_true b' -> b = b'.
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
  intros [e1 [e2 e3]].
  assert (b = b7 /\ b0 = b8 /\ b1 = b9 /\ b2 = b10 /\ b3 = b11 /\ b4 = b12 /\ b5 = b13 /\ b6 = b14).
  apply pair_equal_spec in e2. repeat (rewrite pair_equal_spec in e2; split).
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2. split.
  apply is_true_inj; apply e2.
  apply is_true_inj; apply e2.
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
    ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' r.

Inductive char_ind : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) -> Prop :=
| char_ind_cons a0 a1 a2 a3 a4 a5 a6 a7 :
  char_ind (CONSTR (NUMERAL N0) (is_true a0, (is_true a1, (is_true a2, (is_true a3, (is_true a4, (is_true a5, (is_true a6, is_true a7))))))) (fun _ => BOTTOM)).

Lemma Prop_bool_eq (P : Prop) : P = COND P true false.
Proof.
  case (prop_degen P); intro H; rewrite H.
  rewrite COND_True, is_true_of_true. reflexivity.
  rewrite COND_False, is_true_of_false. reflexivity.
Qed.

Lemma char_eq : char_pred = char_ind.
Proof.
  ext r. apply prop_ext.
  intro h. apply h. intros r' [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 e]]]]]]]].
  rewrite e, (Prop_bool_eq a0), (Prop_bool_eq a1), (Prop_bool_eq a2),
    (Prop_bool_eq a3), (Prop_bool_eq a4), (Prop_bool_eq a5), (Prop_bool_eq a6),
    (Prop_bool_eq a7).
  exact (char_ind_cons (COND a0 true false) (COND a1 true false)
           (COND a2 true false) (COND a3 true false) (COND a4 true false)
           (COND a5 true false) (COND a6 true false) (COND a7 true false)).
  induction 1. unfold char_pred. intros R h. apply h.
  exists a0. exists a1. exists a2. exists a3. exists a4. exists a5. exists a6. exists a7. reflexivity.
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
((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) = ((_dest_char (_mk_char r)) = r).
Proof. intro r. apply axiom_18'. Qed.

(*****************************************************************************)
(* Alignment of the type nadd of nearly additive sequences of naturals. *)
(*****************************************************************************)

Definition dist := fun p : prod N N => N.add (N.sub (@fst N N p) (@snd N N p)) (N.sub (@snd N N p) (@fst N N p)).

Lemma dist_def : dist = (fun _22947 : prod N N => N.add (N.sub (@fst N N _22947) (@snd N N _22947)) (N.sub (@snd N N _22947) (@fst N N _22947))).
Proof. exact (eq_refl dist). Qed.

Lemma DIST_REFL : forall n : N, dist (n,n) = 0.
Proof. intro n. unfold dist. simpl. rewrite N.sub_diag. reflexivity. Qed.

Lemma DIST_SYM x y : dist (x,y) = dist (y,x).
Proof. unfold dist; simpl. lia. Qed.

Lemma DIST_TRIANGLE x y z : dist (x,z) <= dist (x,y) + dist (y,z).
Proof. unfold dist; simpl. lia. Qed.

Definition is_nadd := fun f : N -> N => exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (f n)) (N.mul n (f m)))) (N.mul B (N.add m n)).

Lemma is_nadd_def : is_nadd = (fun _23257 : N -> N => exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (_23257 n)) (N.mul n (_23257 m)))) (N.mul B (N.add m n))).
Proof. exact (eq_refl is_nadd). Qed.

Lemma is_nadd_times n : is_nadd (fun x => n * x).
Proof.
  exists 0. intros x y. simpl. assert (e: x*(n*y)=y*(n*x)). lia.
  rewrite e, DIST_REFL. reflexivity.
Qed.

Lemma is_nadd_0 : is_nadd (fun _ => 0).
Proof. exact (is_nadd_times 0). Qed.

Definition nadd := subtype is_nadd_0.

Definition mk_nadd := mk is_nadd_0.
Definition dest_nadd := dest is_nadd_0.

Lemma axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.
Proof. exact (mk_dest is_nadd_0). Qed.

Lemma axiom_20_aux : forall (r : N -> N), (is_nadd r) -> ((dest_nadd (mk_nadd r)) = r).
Proof. exact (dest_mk_aux is_nadd_0). Qed.

Lemma axiom_20 : forall (r : N -> N), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).
Proof. exact (dest_mk is_nadd_0). Qed.

Definition nadd_of_num : N -> nadd := fun _23288 : N => mk_nadd (fun n : N => N.mul _23288 n).

Lemma nadd_of_num_def : nadd_of_num = (fun _23288 : N => mk_nadd (fun n : N => N.mul _23288 n)).
Proof. exact (eq_refl nadd_of_num). Qed.

Definition nadd_le : nadd -> nadd -> Prop := fun _23295 : nadd => fun _23296 : nadd => exists B : N, forall n : N, N.le (dest_nadd _23295 n) (N.add (dest_nadd _23296 n) B).

Lemma nadd_le_def : nadd_le = (fun _23295 : nadd => fun _23296 : nadd => exists B : N, forall n : N, N.le (dest_nadd _23295 n) (N.add (dest_nadd _23296 n) B)).
Proof. exact (eq_refl nadd_le). Qed.

Lemma nadd_le_refl x : nadd_le x x.
Proof. exists 0. intro n. lia. Qed.

Lemma  nadd_le_trans x y z : nadd_le x y -> nadd_le y z -> nadd_le x z.
Proof.
  intros [B h] [C i]. exists (B+C). intro n. generalize (h n). generalize (i n). lia.
Qed.

Add Relation _ nadd_le
    reflexivity proved by nadd_le_refl
    transitivity proved by nadd_le_trans
as nadd_le_rel.

Definition nadd_add : nadd -> nadd -> nadd := fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : N => N.add (dest_nadd _23311 n) (dest_nadd _23312 n)).

Lemma nadd_add_def : nadd_add = (fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : N => N.add (dest_nadd _23311 n) (dest_nadd _23312 n))).
Proof. exact (eq_refl nadd_add). Qed.

Lemma is_nadd_add_aux f g : is_nadd f -> is_nadd g -> is_nadd (fun n => f n + g n).
Proof.
  intros [b i] [c j]. exists (b+c). intros x y.
  generalize (i x y); intro ixy. generalize (j x y); intro jxy.
  unfold dist in *; simpl in *. lia.
Qed.

Lemma is_nadd_add f g : is_nadd (fun n => dest_nadd f n + dest_nadd g n).
Proof.
  destruct f as [f hf]. destruct g as [g hg]. simpl.
  apply is_nadd_add_aux. exact hf. exact hg.
Qed.

Lemma nadd_of_num_add p q :
  nadd_of_num (p + q) = nadd_add (nadd_of_num p) (nadd_of_num q).
Proof.
  unfold nadd_add, nadd_of_num. f_equal. ext x.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  lia.
Qed.

Lemma NADD_ADD_SYM p q : nadd_add p q = nadd_add q p.
Proof. unfold nadd_add. f_equal. ext x. lia. Qed.

Lemma NADD_ADD_ASSOC p q r :
  nadd_add (nadd_add p q) r = nadd_add p (nadd_add q r).
Proof.
  unfold nadd_add. f_equal. ext x. rewrite !axiom_20_aux. lia.
  apply is_nadd_add. apply is_nadd_add.
Qed.

Definition nadd_mul : nadd -> nadd -> nadd := fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : N => dest_nadd _23325 (dest_nadd _23326 n)).

Lemma nadd_mul_def : nadd_mul = (fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : N => dest_nadd _23325 (dest_nadd _23326 n))).
Proof. exact (eq_refl nadd_mul). Qed.

Definition nadd_rinv : nadd -> N -> N := fun _23462 : nadd => fun n : N => N.div (N.mul n n) (dest_nadd _23462 n).

Lemma nadd_rinv_def : nadd_rinv = (fun _23462 : nadd => fun n : N => N.div (N.mul n n) (dest_nadd _23462 n)).
Proof. exact (eq_refl nadd_rinv). Qed.

Definition nadd_eq : nadd -> nadd -> Prop := fun _23276 : nadd => fun _23277 : nadd => exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd _23276 n) (dest_nadd _23277 n))) B.

Lemma nadd_eq_def : nadd_eq = (fun _23276 : nadd => fun _23277 : nadd => exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd _23276 n) (dest_nadd _23277 n))) B).
Proof. exact (eq_refl nadd_eq). Qed.

Lemma NADD_EQ_REFL f : nadd_eq f f.
Proof. unfold nadd_eq. exists 0. intro n. unfold dist; simpl. lia. Qed.

Lemma nadd_eq_sym f g : nadd_eq f g -> nadd_eq g f.
Proof. intros [b fg]. exists b. intro n. rewrite DIST_SYM. apply fg. Qed.

Lemma nadd_eq_trans f g h : nadd_eq f g -> nadd_eq g h -> nadd_eq f h.
Proof.
  intros [b fg] [c gh]. exists (b+c). intro n.
  rewrite DIST_TRIANGLE with (y := dest_nadd g n).
  generalize (fg n); intro fgn. generalize (gh n); intro ghn.
  transitivity (b + dist (dest_nadd g n, dest_nadd h n)). lia.
  transitivity (b+c); lia.
Qed.

Add Relation _ nadd_eq
    reflexivity proved by NADD_EQ_REFL
    symmetry proved by nadd_eq_sym
    transitivity proved by nadd_eq_trans
as nadd_eq_rel.

Require Import Coq.Setoids.Setoid.

Add Morphism nadd_add
    with signature nadd_eq ==> nadd_eq ==> nadd_eq
      as nadd_add_morph.
Proof.
  intros f f' [b ff'] g g' [c gg']. exists (b+c). intro n.
  generalize (ff' n); intro ff'n. generalize (gg' n); intro gg'n.
  unfold nadd_add. rewrite !axiom_20_aux. unfold dist in *; simpl in *. lia.
  apply is_nadd_add. apply is_nadd_add.
Qed.

(*Add Morphism nadd_le
    with signature nadd_eq ==> nadd_eq ==> iff
      as nadd_le_morph.
Proof.
  intros f f' [b ff'] g g' [c gg'].
Abort.*)

Lemma nadd_add_lcancel x y z : nadd_add x y = nadd_add x z -> y = z.
Proof.
  intro h. destruct x as [x hx]. destruct y as [y hy]. destruct z as [z hz].
  apply subset_eq_compat. unfold nadd_add in h. simpl in h. apply mk_inj in h.
  ext a. generalize (ext_fun h a); simpl; intro ha. lia.
  apply is_nadd_add_aux; assumption. apply is_nadd_add_aux; assumption.
Qed.

Lemma NADD_ADD_LCANCEL x y z :
  nadd_eq (nadd_add x y ) (nadd_add x z) -> nadd_eq y z.
Proof.
  intro h. destruct x as [x hx]. destruct y as [y hy]. destruct z as [z hz].
  destruct h as [B h]. exists B. intro n. generalize (h n). unfold nadd_add. simpl.
  unfold dest_nadd, mk_nadd. rewrite !dest_mk_aux. unfold dist. simpl. lia.
  apply is_nadd_add_aux; assumption. apply is_nadd_add_aux; assumption.
Qed.

Definition nadd_inv : nadd -> nadd := fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL N0))) (nadd_of_num (NUMERAL N0)) (mk_nadd (nadd_rinv _23476)).

Lemma nadd_inv_def : nadd_inv = (fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL N0))) (nadd_of_num (NUMERAL N0)) (mk_nadd (nadd_rinv _23476))).
Proof. exact (eq_refl nadd_inv). Qed.

(*****************************************************************************)
(* Alignment of the type hreal of non-negative real numbers. *)
(*****************************************************************************)

Definition hreal := quotient nadd_eq.

Definition mk_hreal := mk_quotient nadd_eq.
Definition dest_hreal := dest_quotient nadd_eq.

Lemma axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.
Proof. exact (mk_dest_quotient nadd_eq). Qed.

Lemma axiom_22_aux : forall r : nadd -> Prop, (exists x : nadd, r = nadd_eq x) -> dest_hreal (mk_hreal r) = r.
Proof. exact (dest_mk_aux_quotient nadd_eq). Qed.

Lemma axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).
Proof. exact (dest_mk_quotient nadd_eq). Qed.

Definition hreal_of_num : N -> hreal := fun m : N => mk_hreal (nadd_eq (nadd_of_num m)).

Lemma hreal_of_num_def : hreal_of_num = (fun m : N => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)).
Proof. exact (eq_refl hreal_of_num). Qed.

Definition hreal_add : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_add_def : hreal_add = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact (eq_refl hreal_add). Qed.

Lemma hreal_add_of_num p q :
  hreal_of_num (p + q) = hreal_add (hreal_of_num p) (hreal_of_num q).
Proof.
  unfold hreal_add, hreal_of_num. f_equal. ext x.
  apply prop_ext; intro h.
  exists (nadd_of_num p). exists (nadd_of_num q). split.
  rewrite <- nadd_of_num_add. exact h. split.
  rewrite axiom_22_aux. 2: exists (nadd_of_num p); reflexivity. apply NADD_EQ_REFL.
  rewrite axiom_22_aux. 2: exists (nadd_of_num q); reflexivity. apply NADD_EQ_REFL.
  destruct h as [f [g [h1 [h2 h3]]]].
  rewrite axiom_22_aux in h2. 2: exists (nadd_of_num p); reflexivity.
  rewrite axiom_22_aux in h3. 2: exists (nadd_of_num q); reflexivity.
  rewrite nadd_of_num_add. rewrite h2, h3. exact h1.
Qed.

Lemma succ_eq_add_1 n : N.succ n = n + 1. Proof. lia. Qed.

Lemma hreal_of_num_S n : hreal_of_num (N.succ n) = hreal_add (hreal_of_num n) (hreal_of_num 1).
Proof. rewrite succ_eq_add_1, hreal_add_of_num. reflexivity. Qed.

Lemma hreal_add_sym p q : hreal_add p q = hreal_add q p.
Proof.
  unfold hreal_add. f_equal. ext x.
  apply prop_ext; intros [y [z [h1 [h2 h3]]]].
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
Qed.

Lemma hreal_add_of_mk_hreal p q :
  hreal_add (mk_hreal (nadd_eq p)) (mk_hreal (nadd_eq q))
  = mk_hreal (nadd_eq (nadd_add p q)).
Proof.
  unfold hreal_add. apply f_equal. ext x.
  apply prop_ext; intro h.

  unfold dest_hreal, mk_hreal in h. destruct h as [p' [q' [h1 [h2 h3]]]].
  rewrite dest_mk_aux_quotient in h2. 2: apply is_eq_class_of.
  rewrite dest_mk_aux_quotient in h3. 2: apply is_eq_class_of.
  rewrite h2, h3. exact h1.

  exists p. exists q. split. exact h. unfold dest_hreal, mk_hreal.
  rewrite !dest_mk_aux_quotient. split; reflexivity.
  apply is_eq_class_of. apply is_eq_class_of.
Qed.

Lemma mk_hreal_nadd_eq p : mk_hreal (nadd_eq (elt_of p)) = p.
Proof.
  unfold mk_hreal. apply mk_quotient_elt_of.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed.

(*Lemma hreal_add_is_mk_hreal p q :
  hreal_add p q = mk_hreal (nadd_eq (nadd_add (elt_of p) (elt_of q))).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q), hreal_add_of_mk_hreal.
  unfold mk_hreal at 3. unfold mk_hreal at 3. rewrite !mk_quotient_elt_of.
  reflexivity.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed.*)

Lemma hreal_add_assoc p q r :
  hreal_add (hreal_add p q) r = hreal_add p (hreal_add q r).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal.
  f_equal. rewrite NADD_ADD_ASSOC. reflexivity.
Qed.

Lemma hreal_add_lcancel p q r : hreal_add p r = hreal_add q r -> p = q.
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal; intro e.
  unfold mk_hreal, mk_quotient in e. apply mk_inj in e.
  2: apply is_eq_class_of. 2: apply is_eq_class_of.
  apply eq_class_elim in e. 2: apply NADD_EQ_REFL.
  rewrite NADD_ADD_SYM, (NADD_ADD_SYM (elt_of q)) in e.
  apply NADD_ADD_LCANCEL in e.
  f_equal. apply eq_class_intro. apply nadd_eq_sym. apply nadd_eq_trans.
  exact e.
Qed.

Definition hreal_mul : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_mul_def : hreal_mul = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact (eq_refl hreal_mul). Qed.

Definition hreal_le : hreal -> hreal -> Prop := fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_le_def : hreal_le = (fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact (eq_refl hreal_le). Qed.

(*Lemma hreal_le_refl x : hreal_le x x.
Proof.
  unfold hreal_le.
  match goal with [|- ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i: exists x, Q x). exists True. set (t := elt_of x). exists t. exists t. split.
  rewrite is_True. apply nadd_le_refl.
  assert (h: dest_hreal x t). apply dest_quotient_elt_of. apply NADD_EQ_REFL.
  auto.
  generalize (ε_spec i); intros [x1 [x2 [h1 [h2 h3]]]].
  unfold reverse_coercion. rewrite <- h1.
  apply dest_quotient_elim in h2.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  apply dest_quotient_elim in h3.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  rewrite <- h2, <- h3. reflexivity.
Qed.

Add Relation _ hreal_le
    reflexivity proved by hreal_le_refl
    (*transitivity proved by hreal_le_trans*)
as hreal_le_rel.*)

Definition hreal_inv : hreal -> hreal := fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x')).

Lemma hreal_inv_def : hreal_inv = (fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x'))).
Proof. exact (eq_refl hreal_inv). Qed.

(*****************************************************************************)
(* Operations on treal (pairs of hreal's). *)
(*****************************************************************************)

Definition treal_of_num : N -> prod hreal hreal := fun _23721 : N => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL N0)).

Lemma treal_of_num_def : treal_of_num = (fun _23721 : N => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL N0))).
Proof. exact (eq_refl treal_of_num). Qed.

Definition treal_neg : (prod hreal hreal) -> prod hreal hreal := fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726).

Lemma treal_neg_def : treal_neg = (fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726)).
Proof. exact (eq_refl treal_neg). Qed.

Definition treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736)).

Lemma treal_add_def : treal_add = (fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736))).
Proof. exact (eq_refl treal_add). Qed.

Lemma treal_add_of_num p q :
  treal_of_num (p + q) = treal_add (treal_of_num p) (treal_of_num q).
Proof.
  unfold treal_of_num, treal_add; simpl.
  f_equal; rewrite <- hreal_add_of_num; reflexivity.
Qed.

Lemma treal_add_sym  p q : treal_add p q = treal_add q p.
Proof. unfold treal_add. f_equal; apply hreal_add_sym. Qed.

Definition treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758))).

Lemma treal_mul_def : treal_mul = (fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758)))).
Proof. exact (eq_refl treal_mul). Qed.

Definition treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779)).

Lemma treal_le_def : treal_le = (fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779))).
Proof. exact (eq_refl treal_le). Qed.

(*Lemma treal_le_refl x : treal_le x x.
Proof.
  unfold treal_le. destruct x as [x1 x2]. simpl. apply hreal_le_refl.
Qed.

Add Relation _ treal_le
    reflexivity proved by treal_le_refl
    (*transitivity proved by treal_le_trans*)
as treal_le_rel.*)

Definition treal_inv : (prod hreal hreal) -> prod hreal hreal := fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_of_num (NUMERAL N0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL N0))) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d)))))).

Lemma treal_inv_def : treal_inv = (fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_of_num (NUMERAL N0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL N0))) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d))))))).
Proof. exact (eq_refl treal_inv). Qed.

Definition treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810)).

Lemma treal_eq_def : treal_eq = (fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810))).
Proof. exact (eq_refl treal_eq). Qed.

Lemma treal_eq_refl x : treal_eq x x.
Proof. reflexivity. Qed.

Lemma treal_eq_sym x y : treal_eq x y -> treal_eq y x.
Proof.
  unfold treal_eq. destruct x as [x1 x2]; destruct y as [y1 y2]; simpl.
  intro e. symmetry. exact e.
Qed.

Lemma treal_eq_trans x y z : treal_eq x y -> treal_eq y z -> treal_eq x z.
Proof.
  unfold treal_eq.
  destruct x as [x1 x2]; destruct y as [y1 y2]; destruct z as [z1 z2]; simpl.
  intros xy yz.
  assert (h: hreal_add (hreal_add x1 z2) (hreal_add y1 y2)
             = hreal_add (hreal_add z1 x2) (hreal_add y1 y2)).
  rewrite hreal_add_assoc. rewrite <- (hreal_add_assoc z2).
  rewrite (hreal_add_sym _ y2). rewrite <- hreal_add_assoc.
  rewrite (hreal_add_sym z2). rewrite xy, yz.

  rewrite hreal_add_assoc. rewrite (hreal_add_sym (hreal_add z1 x2)).
  rewrite hreal_add_assoc. rewrite (hreal_add_sym y2).
  rewrite (hreal_add_sym z1 x2). rewrite hreal_add_assoc.
  reflexivity. apply hreal_add_lcancel in h. exact h.
Qed.

Add Relation _ treal_eq
    reflexivity proved by treal_eq_refl
    symmetry proved by treal_eq_sym
    transitivity proved by treal_eq_trans
as treal_eq_rel.

Add Morphism treal_add
    with signature treal_eq ==> treal_eq ==> treal_eq
      as treal_add_morph.
Proof.
  intros f f' ff' g g' gg'. unfold treal_eq, treal_add; simpl.
  unfold treal_eq in ff', gg'.
  destruct f as [x1 x2]; destruct f' as [x'1 x'2];
    destruct g as [y1 y2]; destruct g' as [y'1 y'2]; simpl in *.
  rewrite (hreal_add_sym x1). rewrite hreal_add_assoc.
  rewrite <- (hreal_add_assoc x1). rewrite ff'.
  rewrite (hreal_add_sym x2). rewrite (hreal_add_assoc x'1 y'1).
  rewrite <- (hreal_add_assoc y'1). rewrite <- gg'.
  rewrite (hreal_add_assoc y1). rewrite (hreal_add_sym y'2).
  rewrite <- (hreal_add_assoc x'1). rewrite (hreal_add_sym x'1 y1).
  rewrite !hreal_add_assoc. reflexivity.
Qed.

(*Add Morphism treal_le
    with signature treal_eq ==> treal_eq ==> iff
      as treal_le_morph.
Proof.
Abort.*)

(*****************************************************************************)
(* HOL-Light definition of real numbers. *)
(*****************************************************************************)

Definition real := quotient treal_eq.

Module Export HL.

Definition mk_real := mk_quotient treal_eq.
Definition dest_real := dest_quotient treal_eq.

Lemma axiom_23 : forall (a : real), (mk_real (dest_real a)) = a.
Proof. exact (mk_dest_quotient treal_eq). Qed.

Lemma axiom_24_aux : forall r, (exists x, r = treal_eq x) -> dest_real (mk_real r) = r.
Proof. exact (dest_mk_aux_quotient treal_eq). Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof. exact (dest_mk_quotient treal_eq). Qed.

End HL.
