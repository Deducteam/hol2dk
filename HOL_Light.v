From HB Require Import structures.
From mathcomp Require Export ssreflect ssrfun ssrbool eqtype choice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Copy paste what is needed from mathcomp.boolp *)


Axiom functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g.
Axiom propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.
Notation cid := constructive_indefinite_description.

(****************************************************************************)
(* Extensionalities *)
(****************************************************************************)

(* tactic ext should cover almost all cases of need with functional and propositional
   extensionality and their combinations. *)

(* Axiom propext : forall P Q, P <-> Q -> P = Q *)
Lemma prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Proof.
  by move=> * ; apply propositional_extensionality. 
Qed.

(* Axiom functional_extensionality_dep :
   forall f g, (forall x, f x = g x) -> f = g *)
Notation funext := functional_extensionality_dep.

(* applies them to all arguments and propositions at once *)
Tactic Notation "ext" :=
  let rec ext' := (let H := fresh in
    first [apply funext | apply prop_ext]=> H ; try ext' ; move:H)
  in ext'.

(* with a counter added to the context to apply it for exactly n arguments/propositions *)
Variant internal_witness : forall A, A -> Type :=
  w0 A : forall a : A, internal_witness a.

Definition addone : forall n, internal_witness n -> internal_witness (S n) :=
  fun n _ => w0 (S n).

Ltac typecheck A a := assert_succeeds let s:=fresh in set (s := a : A).

Tactic Notation "ext" integer(n) :=
  let ext0 x w := (first [apply funext | apply prop_ext]=>x ; set (w := w0 x))
   (* choosing the fresh variables inside ext0 fails to create new variable names. *)
  in do n (let x := fresh in let w := fresh in ext0 x w) ;
  repeat match goal with | x : _ |- _  =>
  lazymatch goal with w : internal_witness x |- _ => clear w ; revert x end end.

(* Example of use :
Lemma test : (fun f g : nat -> nat => (f=g)) = (fun f g : nat -> nat => (f=g)).
Proof.
(*  ext=> f g H n. *) (* or *)
(*  ext 3 => f g H. *)
  auto.
Qed. *)

(* Small issue : the witnesses are present in the proof term. How bad is it?
   Example :
   Lemma test (f : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat) : f = f.
   Proof. by ext 7. Qed.
   Print test.

   This means that ext should be prefered to ext n if possible. *)
(**** BACK TO MATHCOMP ****)

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
  ext => [->||] ; firstorder.
Qed.

Lemma propT {P : Prop} : P -> P = True.
Proof. by move=> ? ; ext. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; ext. Qed.

Lemma proof_irrelevance (P : Prop) (x y : P) : x = y.
Proof. by move: x (x) y => /propT-> [] []. Qed.

(* Diaconescu Theorem *)
Theorem EM P : P \/ ~ P.
Proof.
pose U val := fun Q : bool => Q = val \/ P.
have Uex val : exists b, U val b by exists val; left.
pose f val := projT1 (cid (Uex val)).
pose Uf val : U val (f val) := projT2 (cid (Uex val)).
have : f true != f false \/ P.
  have [] := (Uf true, Uf false); rewrite /U.
  by move=> [->|?] [->|?] ; do ?[by right]; left.
move=> [/eqP fTFN|]; [right=> p|by left]; apply: fTFN.
have UTF : U true = U false by rewrite predeqE /U => b; split=> _; right.
rewrite /f; move: (Uex true) (Uex false); rewrite UTF => p1 p2.
congr (projT1 (cid _)) ; exact:proof_irrelevance.
Qed.

Lemma pselect (P : Prop): {P} + {~P}.
Proof.
have : exists b, if b then P else ~ P.
  by case: (EM P); [exists true|exists false].
by move=> /cid [[]]; [left|right].
Qed.

Lemma gen_choiceMixin (T : Type) : hasChoice T.
Proof.
  exists (fun (P : pred T) (n : nat) =>
  if pselect (exists x, P x) isn't left ex then None
  else Some (projT1 (cid ex)))
  => [P n x|P [x Px]|].
  by case: pselect => // ex [<- ]; case: cid.
  by exists 0; case: pselect => // -[]; exists x.
  by move=> P Q H ; move:(funext H) => -> //.
Qed.

Definition asbool (P : Prop) := if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Proof. by ext ; rewrite/asbool ; case: pselect. Qed.

Lemma asboolP (P : Prop) : reflect P `[<P>].
Proof. by apply: (equivP idP) ; rewrite asboolE. Qed.

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].

Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Proof.
  move=> x y ; rewrite/gen_eq/asbool.
  by case:(pselect (x = y)) ; constructor.
Qed.
Definition gen_eqMixin (T : Type) : hasDecEq T :=
  hasDecEq.Build T (@gen_eqP T).

Module Export def_Type'.
HB.mixin Record isPointed T := { point : T }.

#[short(type=Type')]
HB.structure Definition Pointed := {T of isPointed T & Choice T}.
End def_Type'.

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

(* Exact same as isPointed, but we will derive choice and decidable
   equality for it, which could be bad for types that have
   their own choice/eq defined in ssreflect (like nat) if it were derived
   from isPointed directly, because it has an instance of isPointed,
   which would make it so it has two defined equalities.

   This should only be used for types without a predefined decidable equality *)

HB.factory Record HOL_isPointed T := {point : T}.

Notation is_Type' := (HOL_isPointed.Build _).

(* in classical context, is a factory for pointedType *)
HB.builders Context T of HOL_isPointed T.

HB.instance Definition _ := gen_eqMixin T.

HB.instance Definition _ := gen_choiceMixin T.

HB.instance Definition _ := isPointed.Build _ point.

HB.end.

HB.instance Definition _ := isPointed.Build _ tt.
HB.instance Definition _ := isPointed.Build _ true.
HB.instance Definition _ := isPointed.Build _ 0.
HB.instance Definition _ := is_Type' True.
HB.instance Definition _ (A B : Type') :=
  isPointed.Build (A*B)%type (point,point).
HB.instance Definition _ T (T' : T -> Type') :=
  HOL_isPointed.Build (forall t, T' t) (fun=> point).

(* Type' is the type of Types of HOL-Light (HOL-Light considers pointed types) *)
(* To define an instance of Type' for a non-empty type [T], use :
   [HB.instance Definition _ := is_Type' a] for some [a : T] *)

(****************************************************************************)
(* Repeating exists. *)
(****************************************************************************)

Tactic Notation "exist" uconstr(x1) uconstr(x2) :=
  exists x1 ; exists x2.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 ; exists x2 ; exists x3.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4 ; exists x5.

(****************************************************************************)
(* Coercion from Prop to bool? *)
(****************************************************************************)

Coercion asbool : Sortclass >-> bool.

(* Check and : bool -> bool -> bool. *)

(****************************************************************************)
(* Coercion from nat to N ? *)
(****************************************************************************)
(* TODO : For another time, if the double coercion between bool and Prop works out.
          it would require to either remove nat_of_bin as a coercion and implement
          N.of_nat and N.to_nat from Stdlib.NArith.Nnat as coercions instead,
          or prove isomorphism (conversions for the most important functions
          and relations) as ssrnat has basically none, especially for bin_of_nat.
          could allow to use for example nth or length on lists.

Require Import Stdlib.NArith.BinNat.
Coercion bin_of_nat : nat >-> N.

(* nat_of_bin is already defined as a coercion in ssrnat. *)

(* Check S : N -> N. *) *)

(****************************************************************************)
(* Curryfied versions of some Rocq connectives. *)
(****************************************************************************)

Definition arr (A B : Type') : Type' := A -> B.

Definition imp (P Q : Prop) : Prop := P -> Q.

Definition ex1 : forall (A : Type'), (A -> Prop) -> Prop := fun A P => exists! x, P x.

(****************************************************************************)
(* Proof of some HOL-Light rules. *)
(****************************************************************************)

Lemma MK_COMB (a b : Type') (s t : a -> b) (u v : a) (h1 : s = t) (h2 : u = v)
  : (s u) = (t v).
Proof. by rewrite h1 h2. Qed.

Lemma EQ_MP (p q : Prop) (e : p = q) (h : p) : q.
Proof. by rewrite -e. Qed.

(* erefl with non-implicit second parameter. *)
Definition REFL A x := @erefl A x.

(****************************************************************************)
(* Proof of some natural deduction rules. *)
(****************************************************************************)

Lemma or_intro1 (p:Prop) (h : p) (q:Prop) : p \/ q.
Proof. exact (@or_introl p q h). Qed.

Lemma or_elim (p q : Prop) (h : p \/ q) (r : Prop) (h1: p -> r) (h2: q -> r) : r.
Proof. exact (@or_ind p q r h1 h2 h). Qed.

Lemma ex_elim a (p : a -> Prop)
  (h1 : exists x, p x) (r : Prop) (h2 : forall x : a, (p x) -> r) : r.
Proof. exact (@ex_ind a p r h2 h1). Qed.

(****************************************************************************)
(* Hilbert's ε operator. *)
(****************************************************************************)

Definition xget {T : choiceType} x0 (P : T -> Prop) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).

Definition ε (A : Type') (P : A -> Prop) := xget point P.

CoInductive xget_spec {T : choiceType} x0 (P : T -> Prop) : T -> Prop -> Type :=
| XGetSome x of x = xget x0 P & P x : xget_spec x0 P x True
| XGetNone of (forall x, ~ P x) : xget_spec x0 P x0 False.

Lemma xgetP {T : choiceType} x0 (P : T -> Prop) :
  xget_spec x0 P (xget x0 P) (P (xget x0 P)).
Proof.
move: (erefl (xget x0 P)); set y := {2}(xget x0 P).
rewrite /xget; case: pselect => /= [?|neqP _].
  by case: sigW => x /= /asboolP Px; rewrite [P x]propT //; constructor.
suff NP x : ~ P x by rewrite [P x0]propF //; constructor.
by apply: contra_not neqP => Px; exists x; apply/asboolP.
Qed.

Lemma xgetPex {T : choiceType} x0 (P : T -> Prop) : (exists x, P x) -> P (xget x0 P).
Proof. by case: xgetP=> // NP [x /NP]. Qed.

Definition ε_spec {A : Type'} {P : A -> Prop} : (exists x, P x) -> P (ε P) := @xgetPex _ _ P.

Lemma align_ε (A : Type') (P : A -> Prop) a : P a -> (forall x, P a -> P x -> a = x) -> a = ε P.
Proof. 
  by move => ha ; apply ; last (apply ε_spec ; exists a).
Qed.

Lemma is_True P : (P = True) = P.
Proof.
  by ext=> // ->.
Qed.

(* From a proof of P (either a hypothesis or a lemma), rewrite P into True. *)
Ltac is_True H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ?P => rewrite <- (is_True P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

Lemma is_False P : (P = False) = ~ P.
Proof.
  by ext=> // ->.
Qed.

(* From hypothesis H : ~P, rewrite P into False *)
Ltac is_False H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ~?P => rewrite <- (is_False P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  move=>P ; rewrite is_False is_True ; exact (EM _).
Qed.

Lemma sym {A} (x y : A) : (x = y) = (y = x).
Proof. by ext. Qed.

(****************************************************************************)
(* if then else over Prop *)
(****************************************************************************)

Definition COND (A : Type) (P : Prop) (x y : A) := if P then x else y.

Lemma if_True (A : Type) (x y : A) : (if True then x else y) = x.
Proof.
  by rewrite/asbool ; case pselect.
Qed.

Lemma if_False (A : Type) (x y : A) : (if False then x else y) = y.
Proof.
by rewrite/asbool ; case pselect.
Qed.

Lemma COND_def {A : Type'} : (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Proof.
  ext=> P x y ; apply align_ε ; first by split=> -> ; rewrite/COND ?if_True ?if_False.
  move=> f' [CT CF] [f'T f'F] ; case : (prop_degen P) => H ; first by rewrite (CT H) f'T.
  by rewrite (CF H) f'F.
Qed.

Definition COND_dep (Q: Prop) (C: Type) (f1: Q -> C) (f2: ~Q -> C) : C :=
  match pselect Q with
  | left x => f1 x
  | right x => f2 x
  end.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. by []. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof.
  by move=> A P x H ; apply ε_spec ; exists x.
Qed.

(****************************************************************************)
(* Alignment of connectives. *)
(****************************************************************************)

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  rewrite/ex1=> A ; ext=> [P [x [Hx Hunique]] | P [[x Hx] Hunique]].
  - by split ; first exists x ; last move=> y z [/Hunique<- /Hunique<-].
  - by exists x ; split ; last (move=> * ; apply Hunique).
Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof.
  by ext=>H ; first destruct H ; apply H.
Qed.

Lemma not_def : not = (fun p : Prop => p -> False).
Proof. reflexivity. Qed.

Lemma or_def : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Proof.
  ext=> [P Q []|P Q] ; last apply ; tauto.
Qed.

Lemma ex_def : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Proof.
  by move=> A ; ext=> P ; last apply ; firstorder.
Qed.

Lemma all_def : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Proof.
  by move=>A ; ext=> [|| P ->].
Qed.

Lemma imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Proof.
  by ext=>[||P Q <-] ; firstorder.
Qed.

Lemma and_def : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Proof.
  ext=>[||P Q e] ; last by pattern and ; rewrite e.
  1,2 : by move=> P Q [HP HQ] ; is_True HP ; is_True HQ.
Qed.

Lemma T_def : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Proof. by ext 1. Qed.

(*****************************************************************************)
(* Alignment of subtypes. *)
(*****************************************************************************)

Require Import Stdlib.Logic.ProofIrrelevance.

Section Subtype.

  Variables (A : Type) (P : A -> Prop) (a : A) (h : P a).

  Definition subtype (h : P a) := {x | P x}.

  HB.instance Definition _ := HOL_isPointed.Build (subtype h) (exist P a h).

  Definition dest : subtype h -> A := fun x => proj1_sig x.

  Definition mk : A -> subtype h :=
    fun x => COND_dep (exist P x) (fun _ => exist P a h).

  Lemma dest_mk_aux x : P x -> (dest (mk x) = x).
  Proof.
    by move=> Px ; rewrite/mk/COND_dep ; case:(pselect (P x)).
  Qed.

  Lemma dest_mk x : P x = (dest (mk x) = x).
  Proof.
    by ext=> [|<-] ; first exact (@dest_mk_aux x) ; last case:(mk x).
  Qed.

  Lemma mk_dest x : mk (dest x) = x.
  Proof.
    rewrite/mk/COND_dep; case: (pselect (P (dest x))); case x ; last by [].
    by move=>a' p pa' ; rewrite (proof_irrelevance _ p pa').
  Qed.

  Lemma dest_inj x y : dest x = dest y -> x = y.
  Proof.
    intro e. destruct x as [x i]. destruct y as [y j]. simpl in e.
    subst y. rewrite (proof_irrelevance _ i j). reflexivity.
  Qed.

  Lemma mk_inj x y : P x -> P y -> mk x = mk y -> x = y.
  Proof.
    rewrite/mk/COND_dep=>hx hy.
    by case:(pselect (P x)); case (pselect (P y))=> Hx Hy ; try move=>[=].
  Qed.

End Subtype.

Arguments dest [_] [_] [_] _.
Arguments mk_dest [_] [_] [_] _.

(****************************************************************************)
(* Alignment of the unit type. *)
(****************************************************************************)

Definition one_ABS : Prop -> unit := fun _ => tt.

Definition one_REP : unit -> Prop := fun _ => True.

Lemma axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a.
Proof. intro a. destruct a. reflexivity. Qed.

Lemma axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).
Proof. intro r. compute. rewrite (sym True r) is_True. reflexivity. Qed.

Lemma one_def : tt = ε one_REP.
Proof. by case:(ε one_REP). Qed.

(****************************************************************************)
(* Alignment of the product type constructor. *)
(****************************************************************************)

Definition mk_pair {A B : Type'} :=
  fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y).

Lemma mk_pair_def {A B : Type'} : (@mk_pair A B) = (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).
Proof. exact erefl. Qed.

Lemma mk_pair_inj {A B : Type'} {x x' : A} {y y' : B} :
  mk_pair x y = mk_pair x' y' -> x = x' /\ y = y'.
Proof.
 by fold (mk_pair x' y' x y) ; move=><-.
Qed.

Definition ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B :=
  fun A B f => ε (fun p => f = mk_pair (fst p) (snd p)).

Lemma ABS_prod_mk_pair {A B : Type'} {x : A} {y : B} :
  (x,y) = ABS_prod (mk_pair x y).
Proof.
  unfold ABS_prod.
  apply align_ε.
  - reflexivity.
  - move=> [x' y'] _ h.
    apply pair_equal_spec.
    exact (mk_pair_inj h).
Qed.

Definition REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop :=
  fun A B p a b => mk_pair (fst p) (snd p) a b.

Lemma pair_def {A B : Type'} : (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Proof.
  ext=> x y.
  exact ABS_prod_mk_pair.
Qed.

Lemma FST_def {A B : Type'} : (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Proof.
  ext=> [[x y]].
  apply align_ε.
  - exists y.
    reflexivity.
  - by move => x' _ [y' ->].
Qed.

Lemma SND_def {A B : Type'} : (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Proof.
  ext=> [[x y]].
  apply align_ε.
  - exists x.
    reflexivity.
  - by move=> y' _ [x' ->].
Qed.

Lemma axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.
Proof. intros A B [a b]. symmetry. exact ABS_prod_mk_pair. Qed.

Lemma axiom_5 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).
Proof.
  intros A B f.
  apply prop_ext.
  - intros [a [b ->]].
    rewrite -ABS_prod_mk_pair.
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

Definition ind : Type' := nat.

Definition ONE_ONE A B := @injective B A.

Lemma ONE_ONE_def {A B : Type'} : (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).
Proof. exact erefl. Qed.

Definition ONTO {A B : Type'} (f : A -> B) := forall y, exists x, y = f x.

Lemma ONTO_def {A B : Type'} : (@ONTO A B) = (fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x)).
Proof. by []. Qed.

Lemma axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Proof.
  rewrite ONTO_def.
  exists S.
  split.
  - exact eq_add_S.
  - intro h.
    generalize (h 0).
    intros [x hx].
    discriminate.
Qed.
