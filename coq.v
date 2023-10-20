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

Definition nat' := {| type := nat; el := 0 |}.
Canonical nat'.

Definition unit' := {| type := unit; el := tt |}.
Canonical unit'.

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

Definition prod (a b : Type') := {| type := a * b; el := pair (el a) (el b) |}.
Canonical prod.

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
(* HOL-Light axioms. *)
(****************************************************************************)

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

Require Import PropExtensionalityFacts.

Lemma is_True p : (p = True) = p.
Proof.
  apply prop_ext.
  intro e. rewrite e. exact I.
  apply PropExt_imp_ProvPropExt.
  intros a b [ab ba]. apply prop_ext. apply ab. apply ba.
Qed.

Lemma sym {A} (x y : A) : (x = y) = (y = x).
Proof. apply prop_ext; intro e; symmetry; exact e. Qed.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. intros A B f. apply fun_ext; intro x. reflexivity. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof. intros A P x h. apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h)). Qed.

(****************************************************************************)
(* Proof of HOL-Light-Coq mappings for connectives. *)
(****************************************************************************)

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

Definition one_ABS : Prop -> unit := fun _ => tt.

Definition one_REP : unit -> Prop := fun _ => True.

Lemma axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a.
Proof. intro a. destruct a. reflexivity. Qed.

Lemma axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).
Proof. intro r. compute. rewrite (sym True r), is_True. reflexivity. Qed.

(****************************************************************************)
(* HOL-Light definitions (to be removed when definitions will be
translated to definitions automatically). *)
(****************************************************************************)

Lemma _FALSITY__def : False = False.
Proof. reflexivity. Qed.

Definition o : forall {A B C : Type'}, (B -> C) -> (A -> B) -> A -> C := fun A B C f g x => f (g x).

Lemma o_def : forall {A B C : Type'}, (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. reflexivity. Qed.

Lemma I_def : forall {A : Type'}, (@id A) = (fun x : A => x).
Proof. reflexivity. Qed.

Definition LET : forall {A B : Type'}, (A -> B) -> A -> B := fun A B f x => f x.

Lemma LET_def : forall {A B : Type'}, (@LET A B) = (fun f : A -> B => fun x : A => f x).
Proof. reflexivity. Qed.

Definition LET_END : forall {A : Type'}, A -> A := fun A x => x.

Lemma LET_END_def : forall {A : Type'}, (@LET_END A) = (fun t : A => t).
Proof. reflexivity. Qed.

(*
Definition CURRY : forall {A B C : Type'}, ((prod A B) -> C) -> A -> B -> C := fun A B C f a b => f (pair a b).

Lemma CURRY_def : forall {A B C : Type'}, (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Proof. reflexivity. Qed.

Definition UNCURRY : forall {A B C : Type'}, (A -> B -> C) -> (prod A B) -> C := fun A B C f p => f (fst p) (snd p).

Lemma UNCURRY_def : forall {A B C : Type'}, (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Proof. reflexivity. Qed.
*)

Definition ONE_ONE : forall {A B : Type'}, (A -> B) -> Prop := fun A B f => forall x y, f x = f y -> x = y.

Lemma ONE_ONE_def : forall {A B : Type'}, (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).
Proof. reflexivity. Qed.
