namespace HOLLight.mapping

/-***************************************************************************-/
/- Coq theory for encoding HOL-Light proofs. -/
/-***************************************************************************-/

theorem ext_fun {A B} {f g : A -> B} : f = g -> forall x, f x = g x
:= by intro fg x; subst fg; rfl

--theorem eq_false_negb_true b : b = false -> negb b = true
--:= by intro e; subst e; rfl

/-**************************************************************************-/
/- Type of non-empty types, used to interpret HOL-Light types types -/
/-**************************************************************************-/

structure Type' where
type : Type
inhabited : Inhabited type

instance : CoeSort Type' Type where coe t := t.type

instance (A:Type') :Inhabited A where default := @default _ A.inhabited

def el {A:Type'} : A := Inhabited.default

def arr (a : Type) (b : Type) : Type := a -> b

/-**************************************************************************-/
/- Curryfied versions of some Coq connectives -/
/-**************************************************************************-/

def imp (p q : Prop) : Prop := p -> q

/-**************************************************************************-/
/- := of some HOL-Light rules -/
/-**************************************************************************-/

theorem MK_COMB {a b : Type} {s t : a -> b} {u v : a} (h1 : s = t) (h2 : u = v)
  : (s u) = (t v)
:= by subst h1 h2; rfl

theorem EQ_MP {p q : Prop} (e : p = q) (h : p) : q
:= by subst e; apply h

/-**************************************************************************-/
/- := of some natural deduction rules -/
/-**************************************************************************-/

theorem or_intro1 {p:Prop} (h : p) (q:Prop) : p \/ q
:= Or.inl h

theorem or_intro2 (p:Prop) {q:Prop} (h : q) : p \/ q
:= Or.inr h

theorem or_elim {p q : Prop} (h : p \/ q) {r : Prop} (h1: p -> r) (h2: q -> r) : r
:= match h with
| .inl hp => h1 hp
| .inr hq => h2 hq

theorem ex_elim {a} {p : a -> Prop}
  (h1 : exists x, p x) {r : Prop} (h2 : forall x : a, p x -> r) : r
:= match h1 with | .intro x h => h2 x h

/-**************************************************************************-/
/- Coq axioms necessary to handle HOL-Light proofs -/
/-**************************************************************************-/

--Require Import CoqLogicClassicalEpsilon

--def ε : forall {A : Type'}, (A -> Prop) -> A := fun A P => epsilon (inhabits (el A)) P
axiom ε : forall {A : Type'}, (A -> Prop) -> A
/-:= by
intro A P; cases Classical.em (Exists P) with
| inl h => exact Exists.choose h
| inr _ => exact A.el
-/

axiom ε_spec {A : Type'} {P : A -> Prop} : (exists x, P x) -> P (ε P)
-- := by intro h; unfold ε; apply epsilon_spec; exact h

axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, f x = g x) -> f = g

axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q

/-Require Import CoqLogicClassicalFacts

theorem prop_degen : forall P, P = True \/ P = False := by
apply prop_ext_em_degen unfold prop_extensionality intros A B [AB BA]
apply prop_ext exact AB exact BA
intro P apply classic
-/
-- Require Import CoqLogicPropExtensionalityFacts

theorem is_True P : (P = True) = P := by
apply prop_ext
intro e; rw [e]; trivial
intro p; apply prop_ext; intro _; trivial; intro _; exact p

/-
theorem is_False P : (P = False) = ~ P
:=
  apply prop_ext; intro h rewrite h intro i exact i
  apply prop_ext; intro i apply h apply i apply False_rec exact i
Qed

theorem refl_is_True {A} (x:A) : (x = x) = True
:= rewrite is_True rfl

theorem sym {A} (x y : A) : (x = y) = (y = x)
:= apply prop_ext; intro e; symmetry; exact e

theorem True_and_True : (True /\ True) = True
:= rewrite is_True tauto

theorem not_forall_eq A (P : A -> Prop) : (~ forall x, P x) = exists x, ~ (P x)
:=
  apply prop_ext; intro h apply not_all_ex_not exact h
  apply ex_not_not_all exact h
Qed

theorem not_exists_eq A (P : A -> Prop) : (~ exists x, P x) = forall x, ~ (P x)
:=
  apply prop_ext; intro h apply not_ex_all_not exact h
  apply all_not_not_ex exact h
Qed

theorem ex2_eq A (P Q : A -> Prop) : (exists2 x, P x & Q x) = (exists x, P x /\ Q x)
:=
  apply prop_ext intros [x h i] exists x auto intros [x [h i]] exists x; auto
Qed

theorem not_conj_eq P Q : (~(P /\ Q)) = (~P \/ ~Q)
:=
  apply prop_ext; intro h
  case (classic P); intro i
  right intro q apply h auto
  auto
  intros [p q] destruct h as [h|h]; contradiction
Qed

theorem not_disj_eq P Q : (~(P \/ Q)) = (~P /\ ~Q)
:=
  apply prop_ext; intro h
  split intro p apply h left exact p intro q apply h right exact q
  destruct h as [np nq] intros [i|i]; auto
Qed

theorem imp_eq_disj P Q : (P -> Q) = (~P \/ Q)
:=
  apply prop_ext; intro h
  case (classic P); intro i; auto
  intro p destruct h as [h|h] contradiction exact h
Qed

def COND {A : Type'} := fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))

theorem COND_True (A : Type') (x y : A) : COND True x y = x
:=
  unfold COND match goal with [|- ε ?x = _] => set (Q := x) end
  assert (i : exists q, Q q) exists x split; intro h
  rfl apply False_rec rewrite <- h exact I
  generalize (ε_spec i) intros [h1 h2] apply h1 rfl
Qed

theorem COND_False (A : Type') (x y : A) : COND False x y = y
:=
  unfold COND match goal with [|- ε ?x = _] => set (Q := x) end
  assert (i : exists q, Q q) exists y split; intro h apply False_rec
  rewrite h exact I rfl
  generalize (ε_spec i) intros [h1 h2] apply h2 rfl
Qed

def COND_dep (Q: Prop) (C: Type) (f1: Q -> C) (f2: ~Q -> C) : C :=
  match excluded_middle_informative Q with
  | left _ x => f1 x
  | right _ x => f2 x
  end
-/
/-**************************************************************************-/
/- := of HOL-Light axioms -/
/-**************************************************************************-/

theorem axiom_0 : forall {A B : Type}, forall t : A -> B, (fun x : A => t x) = t
:= by intros A B t; rfl

--theorem axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P)
--:= by intros A P x h; apply (epsilon_spec (inhabits (el A)) P (ex_intro P x h))

/-**************************************************************************-/
/- Alignment of connectives. -/
/-**************************************************************************-/

def ex1 {A:Type} := fun P : A -> Prop => (Exists P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)

theorem ex1_def : forall {A : Type}, (@ex1 A) = (fun P : A -> Prop => (Exists P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y))
:= by intro; rfl

theorem F_def : False = (forall p : Prop, p)
:= by
apply prop_ext
intro b p; exfalso; exact b
intro h; apply h

theorem not_def : Not = (fun p : Prop => p -> False) := by rfl

theorem or_def : Or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r)
:= by
apply fun_ext; intro p; apply fun_ext; intro q; apply prop_ext
intros pq r pr qr; cases pq with
| inl h => apply pr h
| inr h => apply qr h
intro h; apply h; intro hp; apply Or.inl hp; intro hq; apply Or.inr hq

theorem ex_def : forall {A : Type}, @Exists A = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q)
:= by
intro A; apply fun_ext; intro p; apply prop_ext
intro h; cases h with
| intro x px => intros q pq; apply pq x px
intro h; apply h; intros x px; exact Exists.intro x px

def all {A:Type} (P:A -> Prop) : Prop := forall x:A, P x

theorem all_def : forall {A : Type}, @all A = (fun P : A -> Prop => P = (fun x : A => True))
:= by
intro A; apply fun_ext; intro p; apply prop_ext
intro h; apply fun_ext; intro x; apply prop_ext
intros _; trivial; intros _; exact h x
intros e x; subst e; trivial

theorem imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p)
:= by
apply fun_ext; intro p; apply fun_ext; intro q; apply prop_ext
intro pq; apply prop_ext; intros h; cases h with
| intro hp _ => exact hp
intro hp; apply And.intro; exact hp; apply pq; exact hp
intro e; rw [e.symm]; intro pq; exact pq.right

theorem and_def : And = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True))
:= by
apply fun_ext; intro p; apply fun_ext; intro q; apply prop_ext
intro pq; cases pq with | intro hp hq =>
  apply fun_ext; intro f
  have p':=is_True p; rw [p'.symm] at hp; subst hp
  have q':=is_True q; rw [q'.symm] at hq; subst hq
  rfl
intro e; have hp := ext_fun e (fun x _ => x); have hq := ext_fun e (fun _ x => x)
simp at hp; simp at hq; apply And.intro hp hq

theorem T_def : True = ((fun p : Prop => p) = (fun p : Prop => p))
:= by
apply prop_ext
intro; rfl
intro; trivial
