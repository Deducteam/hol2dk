Record Type' := { type :> Type; el : type }.

Definition Prop' : Type' := {| type := Prop; el := True |}.
Canonical Prop'.

Definition nat' := {| type := nat; el := 0 |}.
Canonical nat'.

Definition unit' := {| type := unit; el := tt |}.
Canonical unit'.

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

Definition prod (a b : Type') := {| type := a * b; el := pair (el a) (el b) |}.
Canonical prod.

Definition imp (p q : Prop) : Prop := p -> q.

Lemma MK_COMB {a b : Type} {s t : a -> b} {u v : a} (h1 : s = t) (h2 : u = v) : (s u) = (t v).
Proof. rewrite h1, h2. reflexivity. Qed.

Lemma EQ_MP {p q : Prop} (e : p = q) (h : p) : q.
Proof. rewrite <- e. apply h. Qed.

Lemma or_intro1 {p:Prop} (h : p) (q:Prop) : p \/ q.
Proof. exact (@or_introl p q h). Qed.

Lemma or_intro2 (p:Prop) {q:Prop} (h : q) : p \/ q.
Proof. exact (@or_intror p q h). Qed.

Lemma or_elim {p q : Prop} (h : p \/ q) {r : Prop} (h1: p -> r) (h2: q -> r) : r.
Proof. exact (@or_ind p q r h1 h2 h). Qed.

Lemma ex_elim {a} {p : a -> Prop} (h1 : exists x, p x) {r : Prop} (h2 : forall x : a, (p x) -> r) : r.
Proof. exact (@ex_ind a p r h2 h1). Qed.

Definition ex1 : forall {A : Type'}, (A -> Prop) -> Prop := fun A P => exists! x, P x.

Require Import Coq.Logic.ClassicalEpsilon.

Definition ε : forall {A : Type'}, (A -> Prop) -> A := fun A P => epsilon (inhabits (el A)) P.

Axiom fun_ext : forall {a b : Type'} {f g : a -> b}, (forall x, (f x) = (g x)) -> f = g.
Axiom prop_ext : forall {p q : Prop}, (p -> q) -> (q -> p) -> p = q.

Require Import ClassicalFacts.

Lemma prop_degen : forall p, p = True \/ p = False.
Proof.
  apply prop_ext_em_degen.
  unfold prop_extensionality. intros A B [AB BA]. apply prop_ext. exact AB. exact BA.
  intro p. apply classic.
Qed.

(*Lemma axiom_0 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
Lemma axiom_1 : forall (a : nat), (mk_num (dest_num a)) = a.
Lemma axiom_2 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Lemma axiom_3 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).
Lemma axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.
Lemma axiom_5 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).
Lemma axiom_6 : forall (a : unit), (one_ABS (one_REP a)) = a.*)

Lemma axiom_7 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof. intros A P x h. apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h)). Qed.

Lemma axiom_8 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. intros A B f. apply fun_ext; intro x. reflexivity. Qed.

(*Lemma BIT1_def : BIT1 = (fun _2143 : nat => S (BIT0 _2143)).
Lemma BIT0_def : BIT0 = (@ε (nat -> nat) (fun fn : nat -> nat => ((fn (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (fn (S n)) = (S (S (fn n)))))).
Lemma NUMERAL_def : NUMERAL = (fun _2128 : nat => _2128).
Lemma SUC_def : S = (fun _2104 : nat => mk_num (IND_SUC (dest_num _2104))).
Lemma _0_def : 0 = (mk_num IND_0).
Lemma NUM_REP_def : NUM_REP = (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a).
Lemma IND_0_def : IND_0 = (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))).
Lemma IND_SUC_def : IND_SUC = (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))).
Lemma ONTO_def : forall {A B : Type'}, (@ONTO A B) = (fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x)).
Lemma ONE_ONE_def : forall {A B : Type'}, (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).
Lemma PASSOC_def : forall {A B C D : Type'}, (@PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))).
Lemma UNCURRY_def : forall {A B C : Type'}, (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Lemma CURRY_def : forall {A B C : Type'}, (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Lemma SND_def : forall {A B : Type'}, (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Lemma FST_def : forall {A B : Type'}, (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Lemma pair_def : forall {A B : Type'}, (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Lemma mk_pair_def : forall {A B : Type'}, (@mk_pair A B) = (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).
Lemma _FUNCTION_def : forall {_4678 _4682 : Type'}, (@_FUNCTION _4678 _4682) = (fun r : _4678 -> _4682 -> Prop => fun x : _4678 => @COND _4682 (@ex1 _4682 (r x)) (@ε _4682 (r x)) (@ε _4682 (fun z : _4682 => False))).
Lemma _MATCH_def : forall {_4656 _4660 : Type'}, (@_MATCH _4656 _4660) = (fun e : _4656 => fun r : _4656 -> _4660 -> Prop => @COND _4660 (@ex1 _4660 (r e)) (@ε _4660 (r e)) (@ε _4660 (fun z : _4660 => False))).
Lemma _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Lemma _UNGUARDED_PATTERN_def : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r).
Lemma _SEQPATTERN_def : forall {_4611 _4614 : Type'}, (@_SEQPATTERN _4611 _4614) = (fun r : _4614 -> _4611 -> Prop => fun s : _4614 -> _4611 -> Prop => fun x : _4614 => @COND (_4611 -> Prop) (exists y : _4611, r x y) (r x) (s x)).
Lemma GEQ_def : forall {A : Type'}, (@GEQ A) = (fun a : A => fun b : A => a = b).
Lemma GABS_def : forall {A : Type'}, (@GABS A) = (fun P : A -> Prop => @ε A P).
Lemma LET_END_def : forall {A : Type'}, (@LET_END A) = (fun t : A => t).
Lemma LET_def : forall {A B : Type'}, (@LET A B) = (fun f : A -> B => fun x : A => f x).
Lemma hashek_def : hashek = True.
Lemma one_def : tt = (@ε unit (fun x : unit => True)).
Lemma I_def : forall {A : Type'}, (@id A) = (fun x : A => x).
Lemma o_def : forall {A B C : Type'}, (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Lemma COND_def : forall {A : Type'}, (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).*)

Lemma _FALSITY__def : False = False.
Proof. reflexivity. Qed.

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  intro A. unfold ex1. apply fun_ext; intro P. unfold unique. apply prop_ext.

  intros [x [px u]]. split. apply (ex_intro P x px). intros a b [ha hb].
  transitivity x. symmetry. apply u. exact ha. apply u. exact hb.

  intros [[x px] u]. apply (ex_intro _ x). split. exact px. intros y py. apply u. split.
  exact px. exact py.
Qed.

Lemma not_def : not = (fun p : Prop => p -> False).
Proof. reflexivity. Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof. apply prop_ext. intros b p. apply (False_rec p b). intro h. exact (h False). Qed.

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

Lemma ext_fun {A B} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof. intros fg x. rewrite fg. reflexivity. Qed.

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
