Require Import Stdlib.NArith.BinNat HOLLight.type HOLLight.mappings_N.
Require Import HOLLight.terms.
Axiom thm_T_DEF : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Axiom thm_AND_DEF : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Axiom thm_IMP_DEF : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Axiom thm_FORALL_DEF : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Axiom thm_EXISTS_DEF : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Axiom thm_OR_DEF : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Axiom thm_F_DEF : False = (forall p : Prop, p).
Axiom thm_NOT_DEF : not = (fun p : Prop => p -> False).
Axiom thm_EXISTS_UNIQUE_DEF : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Axiom thm__FALSITY_ : _FALSITY_ = False.
Axiom thm_EQ_REFL : forall {A : Type'}, forall x : A, x = x.
Axiom thm_REFL_CLAUSE : forall {A : Type'}, forall x : A, (x = x) = True.
Axiom thm_EQ_SYM : forall {A : Type'}, forall x : A, forall y : A, (x = y) -> y = x.
Axiom thm_EQ_SYM_EQ : forall {A : Type'}, forall x : A, forall y : A, (x = y) = (y = x).
Axiom thm_EQ_TRANS : forall {A : Type'}, forall x : A, forall y : A, forall z : A, ((x = y) /\ (y = z)) -> x = z.
Axiom thm_BETA_THM : forall {A B : Type'}, forall f : A -> B, forall y : A, ((fun x : A => f x) y) = (f y).
Axiom thm_ABS_SIMP : forall {A B : Type'}, forall t1 : A, forall t2 : B, ((fun x : B => t1) t2) = t1.
Axiom thm_CONJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3).
Axiom thm_CONJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 /\ t2) = (t2 /\ t1).
Axiom thm_CONJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p /\ q) = (q /\ p)) /\ ((((p /\ q) /\ r) = (p /\ (q /\ r))) /\ (((p /\ (q /\ r)) = (q /\ (p /\ r))) /\ (((p /\ p) = p) /\ ((p /\ (p /\ q)) = (p /\ q))))).
Axiom thm_DISJ_ASSOC : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 \/ (t2 \/ t3)) = ((t1 \/ t2) \/ t3).
Axiom thm_DISJ_SYM : forall t1 : Prop, forall t2 : Prop, (t1 \/ t2) = (t2 \/ t1).
Axiom thm_DISJ_ACI : forall (r : Prop) (p : Prop) (q : Prop), ((p \/ q) = (q \/ p)) /\ ((((p \/ q) \/ r) = (p \/ (q \/ r))) /\ (((p \/ (q \/ r)) = (q \/ (p \/ r))) /\ (((p \/ p) = p) /\ ((p \/ (p \/ q)) = (p \/ q))))).
Axiom thm_IMP_CONJ : forall (p : Prop) (q : Prop) (r : Prop), ((p /\ q) -> r) = (p -> q -> r).
Axiom thm_IMP_CONJ_ALT : forall (q : Prop) (p : Prop) (r : Prop), ((p /\ q) -> r) = (q -> p -> r).
Axiom thm_LEFT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, (p /\ (q \/ r)) = ((p /\ q) \/ (p /\ r)).
Axiom thm_RIGHT_OR_DISTRIB : forall p : Prop, forall q : Prop, forall r : Prop, ((p \/ q) /\ r) = ((p /\ r) \/ (q /\ r)).
Axiom thm_FORALL_SIMP : forall {A : Type'}, forall t : Prop, (forall x : A, t) = t.
Axiom thm_EXISTS_SIMP : forall {A : Type'}, forall t : Prop, (exists x : A, t) = t.
Axiom thm_EQ_CLAUSES : forall t : Prop, ((True = t) = t) /\ (((t = True) = t) /\ (((False = t) = (~ t)) /\ ((t = False) = (~ t)))).
Axiom thm_NOT_CLAUSES_WEAK : ((~ True) = False) /\ ((~ False) = True).
Axiom thm_AND_CLAUSES : forall t : Prop, ((True /\ t) = t) /\ (((t /\ True) = t) /\ (((False /\ t) = False) /\ (((t /\ False) = False) /\ ((t /\ t) = t)))).
Axiom thm_OR_CLAUSES : forall t : Prop, ((True \/ t) = True) /\ (((t \/ True) = True) /\ (((False \/ t) = t) /\ (((t \/ False) = t) /\ ((t \/ t) = t)))).
Axiom thm_IMP_CLAUSES : forall t : Prop, ((True -> t) = t) /\ (((t -> True) = True) /\ (((False -> t) = True) /\ (((t -> t) = True) /\ ((t -> False) = (~ t))))).
Axiom thm_EXISTS_UNIQUE_THM : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = ((exists x : A, P x) /\ (forall x : A, forall x' : A, ((P x) /\ (P x')) -> x = x')).
Axiom thm_EXISTS_REFL : forall {A : Type'}, forall a : A, exists x : A, x = a.
Axiom thm_EXISTS_UNIQUE_REFL : forall {A : Type'}, forall a : A, @ex1 A (fun x : A => x = a).
Axiom thm_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (a = x) /\ (P x)) = (P a).
Axiom thm_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (exists x : A, (x = a) /\ (P x)) = (P a).
Axiom thm_FORALL_UNWIND_THM2 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (x = a) -> P x) = (P a).
Axiom thm_FORALL_UNWIND_THM1 : forall {A : Type'}, forall P : A -> Prop, forall a : A, (forall x : A, (a = x) -> P x) = (P a).
Axiom thm_SWAP_FORALL_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall y : B, forall x : A, P x y).
Axiom thm_SWAP_EXISTS_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists y : B, exists x : A, P x y).
Axiom thm_FORALL_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (forall x : A, (P x) /\ (Q x)) = ((forall x : A, P x) /\ (forall x : A, Q x)).
Axiom thm_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((forall x : A, P x) /\ (forall x : A, Q x)) = (forall x : A, (P x) /\ (Q x)).
Axiom thm_LEFT_AND_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) /\ Q) = (forall x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (forall x : A, Q x)) = (forall x : A, P /\ (Q x)).
Axiom thm_EXISTS_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, (exists x : A, (P x) \/ (Q x)) = ((exists x : A, P x) \/ (exists x : A, Q x)).
Axiom thm_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, ((exists x : A, P x) \/ (exists x : A, Q x)) = (exists x : A, (P x) \/ (Q x)).
Axiom thm_LEFT_OR_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) \/ Q) = (exists x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (exists x : A, Q x)) = (exists x : A, P \/ (Q x)).
Axiom thm_LEFT_EXISTS_AND_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) /\ Q) = ((exists x : A, P x) /\ Q).
Axiom thm_RIGHT_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P /\ (Q x)) = (P /\ (exists x : A, Q x)).
Axiom thm_TRIV_EXISTS_AND_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P /\ Q) = ((exists x : A, P) /\ (exists x : A, Q)).
Axiom thm_LEFT_AND_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) /\ Q) = (exists x : A, (P x) /\ Q).
Axiom thm_RIGHT_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P /\ (exists x : A, Q x)) = (exists x : A, P /\ (Q x)).
Axiom thm_TRIV_AND_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((exists x : A, P) /\ (exists x : A, Q)) = (exists x : A, P /\ Q).
Axiom thm_TRIV_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P \/ Q) = ((forall x : A, P) \/ (forall x : A, Q)).
Axiom thm_TRIV_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, ((forall x : A, P) \/ (forall x : A, Q)) = (forall x : A, P \/ Q).
Axiom thm_RIGHT_IMP_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> forall x : A, Q x) = (forall x : A, P -> Q x).
Axiom thm_RIGHT_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P -> Q x) = (P -> forall x : A, Q x).
Axiom thm_LEFT_IMP_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((exists x : A, P x) -> Q) = (forall x : A, (P x) -> Q).
Axiom thm_LEFT_FORALL_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) -> Q) = ((exists x : A, P x) -> Q).
Axiom thm_TRIV_FORALL_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (forall x : A, P -> Q) = ((exists x : A, P) -> forall x : A, Q).
Axiom thm_TRIV_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : Prop, (exists x : A, P -> Q) = ((forall x : A, P) -> exists x : A, Q).
Axiom thm_MONO_FORALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
Axiom thm_MONO_EXISTS : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), (forall x : A, (P x) -> Q x) -> (exists x : A, P x) -> exists x : A, Q x.
Axiom thm_WLOG_RELATION : forall {A : Type'}, forall R' : A -> A -> Prop, forall P : A -> A -> Prop, ((forall x : A, forall y : A, (P x y) -> P y x) /\ ((forall x : A, forall y : A, (R' x y) \/ (R' y x)) /\ (forall x : A, forall y : A, (R' x y) -> P x y))) -> forall x : A, forall y : A, P x y.
Axiom thm_EXISTS_UNIQUE_ALT : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, forall y : A, (P y) = (x = y)).
Axiom thm_EXISTS_UNIQUE : forall {A : Type'}, forall P : A -> Prop, (@ex1 A (fun x : A => P x)) = (exists x : A, (P x) /\ (forall y : A, (P y) -> y = x)).
Axiom thm_ETA_AX : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Axiom thm_EQ_EXT : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (forall x : A, (f x) = (g x)) -> f = g.
Axiom thm_FUN_EQ_THM : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, (f = g) = (forall x : A, (f x) = (g x)).
Axiom thm_SELECT_AX : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Axiom thm_EXISTS_THM : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => P (@ε A P)).
Axiom thm_SELECT_REFL : forall {A : Type'}, forall x : A, (@ε A (fun y : A => y = x)) = x.
Axiom thm_SELECT_UNIQUE : forall {A : Type'}, forall P : A -> Prop, forall x : A, (forall y : A, (P y) = (y = x)) -> (@ε A P) = x.
Axiom thm_EXCLUDED_MIDDLE : forall t : Prop, t \/ (~ t).
Axiom thm_BOOL_CASES_AX : forall t : Prop, (t = True) \/ (t = False).
Axiom thm_DE_MORGAN_THM : forall t1 : Prop, forall t2 : Prop, ((~ (t1 /\ t2)) = ((~ t1) \/ (~ t2))) /\ ((~ (t1 \/ t2)) = ((~ t1) /\ (~ t2))).
Axiom thm_NOT_CLAUSES : (forall t : Prop, (~ (~ t)) = t) /\ (((~ True) = False) /\ ((~ False) = True)).
Axiom thm_NOT_IMP : forall t1 : Prop, forall t2 : Prop, (~ (t1 -> t2)) = (t1 /\ (~ t2)).
Axiom thm_CONTRAPOS_THM : forall t1 : Prop, forall t2 : Prop, ((~ t1) -> ~ t2) = (t2 -> t1).
Axiom thm_NOT_EXISTS_THM : forall {A : Type'}, forall P : A -> Prop, (~ (exists x : A, P x)) = (forall x : A, ~ (P x)).
Axiom thm_EXISTS_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (exists x : A, ~ (P x)) = (~ (forall x : A, P x)).
Axiom thm_NOT_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, (~ (forall x : A, P x)) = (exists x : A, ~ (P x)).
Axiom thm_FORALL_NOT_THM : forall {A : Type'}, forall P : A -> Prop, (forall x : A, ~ (P x)) = (~ (exists x : A, P x)).
Axiom thm_FORALL_BOOL_THM : forall (P : Prop -> Prop), (forall b : Prop, P b) = ((P True) /\ (P False)).
Axiom thm_EXISTS_BOOL_THM : forall (P : Prop -> Prop), (exists b : Prop, P b) = ((P True) \/ (P False)).
Axiom thm_LEFT_FORALL_OR_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (forall x : A, (P x) \/ Q) = ((forall x : A, P x) \/ Q).
Axiom thm_RIGHT_FORALL_OR_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (forall x : A, P \/ (Q x)) = (P \/ (forall x : A, Q x)).
Axiom thm_LEFT_OR_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) \/ Q) = (forall x : A, (P x) \/ Q).
Axiom thm_RIGHT_OR_FORALL_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P \/ (forall x : A, Q x)) = (forall x : A, P \/ (Q x)).
Axiom thm_LEFT_IMP_FORALL_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, ((forall x : A, P x) -> Q) = (exists x : A, (P x) -> Q).
Axiom thm_LEFT_EXISTS_IMP_THM : forall {A : Type'}, forall P : A -> Prop, forall Q : Prop, (exists x : A, (P x) -> Q) = ((forall x : A, P x) -> Q).
Axiom thm_RIGHT_IMP_EXISTS_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (P -> exists x : A, Q x) = (exists x : A, P -> Q x).
Axiom thm_RIGHT_EXISTS_IMP_THM : forall {A : Type'}, forall P : Prop, forall Q : A -> Prop, (exists x : A, P -> Q x) = (P -> exists x : A, Q x).
Axiom thm_COND_DEF : forall {A : Type'}, (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Axiom thm_COND_CLAUSES : forall {A : Type'}, forall t1 : A, forall t2 : A, ((@COND A True t1 t2) = t1) /\ ((@COND A False t1 t2) = t2).
Axiom thm_COND_EXPAND : forall b : Prop, forall t1 : Prop, forall t2 : Prop, (@COND Prop b t1 t2) = (((~ b) \/ t1) /\ (b \/ t2)).
Axiom thm_COND_ID : forall {A : Type'}, forall b : Prop, forall t : A, (@COND A b t t) = t.
Axiom thm_COND_RAND : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall x : A, forall y : A, (f (@COND A b x y)) = (@COND B b (f x) (f y)).
Axiom thm_COND_RATOR : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, forall x : A, (@COND (A -> B) b f g x) = (@COND B b (f x) (g x)).
Axiom thm_COND_ABS : forall {A B : Type'}, forall b : Prop, forall f : A -> B, forall g : A -> B, (fun x : A => @COND B b (f x) (g x)) = (@COND (A -> B) b f g).
Axiom thm_COND_SWAP : forall {A : Type'}, forall p : Prop, forall x : A, forall y : A, (@COND A (~ p) x y) = (@COND A p y x).
Axiom thm_MONO_COND : forall (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop), ((A -> B) /\ (C -> D)) -> (@COND Prop b A C) -> @COND Prop b B D.
Axiom thm_COND_ELIM_THM : forall {A : Type'} (x : A) (c : Prop) (P : A -> Prop) (y : A), (P (@COND A c x y)) = ((c -> P x) /\ ((~ c) -> P y)).
Axiom thm_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, exists y : B, P x y) = (exists y : A -> B, forall x : A, P x (y x)).
Axiom thm_SKOLEM_THM_GEN : forall {A B : Type'}, forall P : A -> Prop, forall R' : A -> B -> Prop, (forall x : A, (P x) -> exists y : B, R' x y) = (exists f : A -> B, forall x : A, (P x) -> R' x (f x)).
Axiom thm_UNIQUE_SKOLEM_ALT : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (exists f : A -> B, forall x : A, forall y : B, (P x y) = ((f x) = y)).
Axiom thm_UNIQUE_SKOLEM_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, @ex1 B (fun y : B => P x y)) = (@ex1 (A -> B) (fun f : A -> B => forall x : A, P x (f x))).
Axiom thm_bool_INDUCT : forall P : Prop -> Prop, ((P False) /\ (P True)) -> forall x : Prop, P x.
Axiom thm_bool_RECURSION : forall {A : Type'}, forall a : A, forall b : A, exists f : Prop -> A, ((f False) = a) /\ ((f True) = b).
Axiom thm_o_DEF : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, (@o A B C f g) = (fun x : A => f (g x)).
Axiom thm_I_DEF : forall {A : Type'}, (@I A) = (fun x : A => x).
Axiom thm_o_THM : forall {A B C : Type'}, forall f : B -> C, forall g : A -> B, forall x : A, (@o A B C f g x) = (f (g x)).
Axiom thm_o_ASSOC : forall {A B C D : Type'}, forall f : C -> D, forall g : B -> C, forall h : A -> B, (@o A C D f (@o A B C g h)) = (@o A B D (@o B C D f g) h).
Axiom thm_I_THM : forall {A : Type'}, forall x : A, (@I A x) = x.
Axiom thm_I_O_ID : forall {A B : Type'}, forall f : A -> B, ((@o A B B (@I B) f) = f) /\ ((@o A A B f (@I A)) = f).
Axiom thm_EXISTS_ONE_REP : exists b : Prop, b.
Axiom thm_one_DEF : tt = (@ε unit (fun x : unit => True)).
Axiom thm_one : forall v : unit, v = tt.
Axiom thm_one_axiom : forall {A : Type'}, forall f : A -> unit, forall g : A -> unit, f = g.
Axiom thm_one_INDUCT : forall P : unit -> Prop, (P tt) -> forall x : unit, P x.
Axiom thm_one_RECURSION : forall {A : Type'}, forall e : A, exists fn : unit -> A, (fn tt) = e.
Axiom thm_one_Axiom : forall {A : Type'}, forall e : A, @ex1 (unit -> A) (fun fn : unit -> A => (fn tt) = e).
Axiom thm_FORALL_ONE_THM : forall (P : unit -> Prop), (forall x : unit, P x) = (P tt).
Axiom thm_EXISTS_ONE_THM : forall (P : unit -> Prop), (exists x : unit, P x) = (P tt).
Axiom thm_ETA_ONE : forall {A : Type'}, forall f : unit -> A, (fun x : unit => f tt) = f.
Axiom thm_LET_DEF : forall {A B : Type'}, forall f : A -> B, forall x : A, (@LET A B f x) = (f x).
Axiom thm_LET_END_DEF : forall {A : Type'}, forall t : A, (@LET_END A t) = t.
Axiom thm_GABS_DEF : forall {A : Type'}, forall P : A -> Prop, (@GABS A P) = (@ε A P).
Axiom thm_GEQ_DEF : forall {A : Type'}, forall a : A, forall b : A, (@eq A a b) = (a = b).
Axiom thm__SEQPATTERN : forall {A B : Type'}, (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Axiom thm__UNGUARDED_PATTERN : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p /\ r).
Axiom thm__GUARDED_PATTERN : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Axiom thm__MATCH : forall {A B : Type'}, (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Axiom thm__FUNCTION : forall {A B : Type'}, (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Axiom thm_mk_pair_def : forall {A B : Type'}, forall x : A, forall y : B, (@mk_pair A B x y) = (fun a : A => fun b : B => (a = x) /\ (b = y)).
Axiom thm_PAIR_EXISTS_THM : forall {A B : Type'}, exists x : A -> B -> Prop, exists a : A, exists b : B, x = (@mk_pair A B a b).
Axiom thm_REP_ABS_PAIR : forall {A B : Type'}, forall x : A, forall y : B, (@REP_prod A B (@ABS_prod A B (@mk_pair A B x y))) = (@mk_pair A B x y).
Axiom thm_COMMA_DEF : forall {A B : Type'}, forall x : A, forall y : B, (@pair A B x y) = (@ABS_prod A B (@mk_pair A B x y)).
Axiom thm_FST_DEF : forall {A B : Type'}, forall p : prod A B, (@fst A B p) = (@ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Axiom thm_SND_DEF : forall {A B : Type'}, forall p : prod A B, (@snd A B p) = (@ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Axiom thm_PAIR_EQ : forall {A B : Type'}, forall x : A, forall y : B, forall a : A, forall b : B, ((@pair A B x y) = (@pair A B a b)) = ((x = a) /\ (y = b)).
Axiom thm_PAIR_SURJECTIVE : forall {A B : Type'}, forall p : prod A B, exists x : A, exists y : B, p = (@pair A B x y).
Axiom thm_FST : forall {A B : Type'}, forall x : A, forall y : B, (@fst A B (@pair A B x y)) = x.
Axiom thm_SND : forall {A B : Type'}, forall x : A, forall y : B, (@snd A B (@pair A B x y)) = y.
Axiom thm_PAIR : forall {A B : Type'}, forall x : prod A B, (@pair A B (@fst A B x) (@snd A B x)) = x.
Axiom thm_pair_INDUCT : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall x : A, forall y : B, P (@pair A B x y)) -> forall p : prod A B, P p.
Axiom thm_pair_RECURSION : forall {A B C : Type'}, forall PAIR' : A -> B -> C, exists fn : (prod A B) -> C, forall a0 : A, forall a1 : B, (fn (@pair A B a0 a1)) = (PAIR' a0 a1).
Axiom thm_CURRY_DEF : forall {A B C : Type'}, forall f : (prod A B) -> C, forall x : A, forall y : B, (@CURRY A B C f x y) = (f (@pair A B x y)).
Axiom thm_UNCURRY_DEF : forall {A B C : Type'}, forall f : A -> B -> C, forall x : A, forall y : B, (@UNCURRY A B C f (@pair A B x y)) = (f x y).
Axiom thm_PASSOC_DEF : forall {A B C D : Type'}, forall f : (prod (prod A B) C) -> D, forall x : A, forall y : B, forall z : C, (@PASSOC A B C D f (@pair A (prod B C) x (@pair B C y z))) = (f (@pair (prod A B) C (@pair A B x y) z)).
Axiom thm_FORALL_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (forall p : prod A B, P p) = (forall p1 : A, forall p2 : B, P (@pair A B p1 p2)).
Axiom thm_EXISTS_PAIR_THM : forall {A B : Type'}, forall P : (prod A B) -> Prop, (exists p : prod A B, P p) = (exists p1 : A, exists p2 : B, P (@pair A B p1 p2)).
Axiom thm_LAMBDA_PAIR_THM : forall {A B C : Type'}, forall t : (prod A B) -> C, (fun p : prod A B => t p) = (@GABS ((prod A B) -> C) (fun f : (prod A B) -> C => forall x : A, forall y : B, @eq C (f (@pair A B x y)) (t (@pair A B x y)))).
Axiom thm_LAMBDA_PAIR : forall {A B C : Type'}, forall f : A -> B -> C, (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f x y))) = (fun p : prod A B => f (@fst A B p) (@snd A B p)).
Axiom thm_LAMBDA_TRIPLE_THM : forall {A B C D : Type'}, forall f : (prod A (prod B C)) -> D, (fun t : prod A (prod B C) => f t) = (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))).
Axiom thm_LAMBDA_TRIPLE : forall {A B C D : Type'}, forall f : A -> B -> C -> D, (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f x y z))) = (fun t : prod A (prod B C) => f (@fst A (prod B C) t) (@fst B C (@snd A (prod B C) t)) (@snd B C (@snd A (prod B C) t))).
Axiom thm_PAIRED_ETA_THM : forall {A B C D E : Type'}, (forall f : (prod A B) -> C, (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall x : A, forall y : B, @eq C (f' (@pair A B x y)) (f (@pair A B x y)))) = f) /\ ((forall f : (prod A (prod B C)) -> D, (@GABS ((prod A (prod B C)) -> D) (fun f' : (prod A (prod B C)) -> D => forall x : A, forall y : B, forall z : C, @eq D (f' (@pair A (prod B C) x (@pair B C y z))) (f (@pair A (prod B C) x (@pair B C y z))))) = f) /\ (forall f : (prod A (prod B (prod C D))) -> E, (@GABS ((prod A (prod B (prod C D))) -> E) (fun f' : (prod A (prod B (prod C D))) -> E => forall w : A, forall x : B, forall y : C, forall z : D, @eq E (f' (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))) (f (@pair A (prod B (prod C D)) w (@pair B (prod C D) x (@pair C D y z)))))) = f)).
Axiom thm_FORALL_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (forall f : A -> B -> C, P f) = (forall f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_UNCURRY : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : (prod A B) -> C, P (fun a : A => fun b : B => f (@pair A B a b))).
Axiom thm_EXISTS_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (exists f : (prod A B) -> C, P f) = (exists f : A -> B -> C, P (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_CURRY : forall {A B C : Type'}, forall P : ((prod A B) -> C) -> Prop, (forall f : (prod A B) -> C, P f) = (forall f : A -> B -> C, P (@GABS ((prod A B) -> C) (fun f' : (prod A B) -> C => forall a : A, forall b : B, @eq C (f' (@pair A B a b)) (f a b)))).
Axiom thm_FORALL_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (forall x : A, forall y : B, P x y) = (forall z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_EXISTS_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (exists x : A, exists y : B, P x y) = (exists z : prod A B, P (@fst A B z) (@snd A B z)).
Axiom thm_FORALL_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (forall f : A -> prod B C, P f) = (forall g : A -> B, forall h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_EXISTS_PAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> prod B C) -> Prop, (exists f : A -> prod B C, P f) = (exists g : A -> B, exists h : A -> C, P (fun a : A => @pair B C (g a) (h a))).
Axiom thm_FORALL_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (forall f : A -> B, forall g : A -> C, P f g) = (forall h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_UNPAIR_FUN_THM : forall {A B C : Type'}, forall P : (A -> B) -> (A -> C) -> Prop, (exists f : A -> B, exists g : A -> C, P f g) = (exists h : A -> prod B C, P (@o A (prod B C) B (@fst B C) h) (@o A (prod B C) C (@snd B C) h)).
Axiom thm_EXISTS_SWAP_FUN_THM : forall {A B C : Type'}, forall P : (A -> B -> C) -> Prop, (exists f : A -> B -> C, P f) = (exists f : B -> A -> C, P (fun a : A => fun b : B => f b a)).
Axiom thm_FORALL_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (all (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (forall x : A, forall y : B, P x y).
Axiom thm_EXISTS_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (ex (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (exists x : A, exists y : B, P x y).
Axiom thm_FORALL_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (all (@GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (forall x : A, forall y : B, forall z : C, P x y z).
Axiom thm_EXISTS_TRIPLED_THM : forall {A B C : Type'}, forall P : A -> B -> C -> Prop, (ex (@GABS ((prod A (prod B C)) -> Prop) (fun f : (prod A (prod B C)) -> Prop => forall x : A, forall y : B, forall z : C, @eq Prop (f (@pair A (prod B C) x (@pair B C y z))) (P x y z)))) = (exists x : A, exists y : B, exists z : C, P x y z).
Axiom thm_CHOICE_UNPAIR_THM : forall {A B : Type'}, forall P : A -> B -> Prop, (@ε (prod A B) (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))) = (@ε (prod A B) (fun p : prod A B => P (@fst A B p) (@snd A B p))).
Axiom thm_CHOICE_PAIRED_THM : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : (prod A B) -> Prop, ((exists x : A, exists y : B, P x y) /\ (forall x : A, forall y : B, (P x y) -> Q (@pair A B x y))) -> Q (@ε (prod A B) (@GABS ((prod A B) -> Prop) (fun f : (prod A B) -> Prop => forall x : A, forall y : B, @eq Prop (f (@pair A B x y)) (P x y)))).
Axiom thm_ONE_ONE : forall {A B : Type'}, forall f : A -> B, (@ONE_ONE A B f) = (forall x1 : A, forall x2 : A, ((f x1) = (f x2)) -> x1 = x2).
Axiom thm_ONTO : forall {A B : Type'}, forall f : A -> B, (@ONTO A B f) = (forall y : B, exists x : A, y = (f x)).
Axiom thm_INFINITY_AX : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Axiom thm_IND_SUC_0_EXISTS : exists f : ind -> ind, exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).
Axiom thm_NUM_REP_RULES : (NUM_REP IND_0) /\ (forall i : ind, (NUM_REP i) -> NUM_REP (IND_SUC i)).
Axiom thm_NUM_REP_CASES : forall a : ind, (NUM_REP a) = ((a = IND_0) \/ (exists i : ind, (a = (IND_SUC i)) /\ (NUM_REP i))).
Axiom thm_NUM_REP_INDUCT : forall NUM_REP' : ind -> Prop, ((NUM_REP' IND_0) /\ (forall i : ind, (NUM_REP' i) -> NUM_REP' (IND_SUC i))) -> forall a : ind, (NUM_REP a) -> NUM_REP' a.
Axiom thm_ZERO_DEF : N0 = (mk_num IND_0).
Axiom thm_SUC_DEF : forall n : N, (N.succ n) = (mk_num (IND_SUC (dest_num n))).
Axiom thm_SUC_INJ : forall m : N, forall n : N, ((N.succ m) = (N.succ n)) = (m = n).
Axiom thm_NOT_SUC : forall n : N, ~ ((N.succ n) = (N0)).
Axiom thm_num_INDUCTION : forall P : N -> Prop, ((P (N0)) /\ (forall n : N, (P n) -> P (N.succ n))) -> forall n : N, P n.
Axiom thm_num_Axiom : forall {A : Type'}, forall e : A, forall f : A -> N -> A, @ex1 (N -> A) (fun fn : N -> A => ((fn (N0)) = e) /\ (forall n : N, (fn (N.succ n)) = (f (fn n) n))).
Axiom thm_num_CASES : forall m : N, (m = (N0)) \/ (exists n : N, m = (N.succ n)).
Axiom thm_PRE : ((N.pred (N0)) = (N0)) /\ (forall n : N, (N.pred (N.succ n)) = n).
Axiom thm_ADD : (forall n : N, (N.add (N0) n) = n) /\ (forall m : N, forall n : N, (N.add (N.succ m) n) = (N.succ (N.add m n))).
Axiom thm_ADD_0 : forall m : N, (N.add m (N0)) = m.
Axiom thm_ADD_SUC : forall m : N, forall n : N, (N.add m (N.succ n)) = (N.succ (N.add m n)).
Axiom thm_ADD_CLAUSES : (forall n : N, (N.add (N0) n) = n) /\ ((forall m : N, (N.add m (N0)) = m) /\ ((forall m : N, forall n : N, (N.add (N.succ m) n) = (N.succ (N.add m n))) /\ (forall m : N, forall n : N, (N.add m (N.succ n)) = (N.succ (N.add m n))))).
Axiom thm_ADD_SYM : forall m : N, forall n : N, (N.add m n) = (N.add n m).
Axiom thm_ADD_ASSOC : forall m : N, forall n : N, forall p : N, (N.add m (N.add n p)) = (N.add (N.add m n) p).
Axiom thm_ADD_AC : forall (n : N) (m : N) (p : N), ((N.add m n) = (N.add n m)) /\ (((N.add (N.add m n) p) = (N.add m (N.add n p))) /\ ((N.add m (N.add n p)) = (N.add n (N.add m p)))).
Axiom thm_ADD_EQ_0 : forall m : N, forall n : N, ((N.add m n) = (N0)) = ((m = (N0)) /\ (n = (N0))).
Axiom thm_EQ_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, ((N.add m n) = (N.add m p)) = (n = p).
Axiom thm_EQ_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, ((N.add m p) = (N.add n p)) = (m = n).
Axiom thm_EQ_ADD_LCANCEL_0 : forall m : N, forall n : N, ((N.add m n) = m) = (n = (N0)).
Axiom thm_EQ_ADD_RCANCEL_0 : forall m : N, forall n : N, ((N.add m n) = n) = (m = (N0)).
Axiom thm_BIT0 : forall n : N, (BIT0 n) = (N.add n n).
Axiom thm_BIT1 : forall n : N, (BIT1 n) = (N.succ (N.add n n)).
Axiom thm_BIT0_THM : forall n : N, ((BIT0 n)) = (N.add (n) (n)).
Axiom thm_BIT1_THM : forall n : N, ((BIT1 n)) = (N.succ (N.add (n) (n))).
Axiom thm_ONE : ((BIT1 N0)) = (N.succ (N0)).
Axiom thm_TWO : ((BIT0 (BIT1 N0))) = (N.succ ((BIT1 N0))).
Axiom thm_ADD1 : forall m : N, (N.succ m) = (N.add m ((BIT1 N0))).
Axiom thm_MULT : (forall n : N, (N.mul (N0) n) = (N0)) /\ (forall m : N, forall n : N, (N.mul (N.succ m) n) = (N.add (N.mul m n) n)).
Axiom thm_MULT_0 : forall m : N, (N.mul m (N0)) = (N0).
Axiom thm_MULT_SUC : forall m : N, forall n : N, (N.mul m (N.succ n)) = (N.add m (N.mul m n)).
Axiom thm_MULT_CLAUSES : (forall n : N, (N.mul (N0) n) = (N0)) /\ ((forall m : N, (N.mul m (N0)) = (N0)) /\ ((forall n : N, (N.mul ((BIT1 N0)) n) = n) /\ ((forall m : N, (N.mul m ((BIT1 N0))) = m) /\ ((forall m : N, forall n : N, (N.mul (N.succ m) n) = (N.add (N.mul m n) n)) /\ (forall m : N, forall n : N, (N.mul m (N.succ n)) = (N.add m (N.mul m n))))))).
Axiom thm_MULT_SYM : forall m : N, forall n : N, (N.mul m n) = (N.mul n m).
Axiom thm_LEFT_ADD_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul m (N.add n p)) = (N.add (N.mul m n) (N.mul m p)).
Axiom thm_RIGHT_ADD_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul (N.add m n) p) = (N.add (N.mul m p) (N.mul n p)).
Axiom thm_MULT_ASSOC : forall m : N, forall n : N, forall p : N, (N.mul m (N.mul n p)) = (N.mul (N.mul m n) p).
Axiom thm_MULT_AC : forall (n : N) (m : N) (p : N), ((N.mul m n) = (N.mul n m)) /\ (((N.mul (N.mul m n) p) = (N.mul m (N.mul n p))) /\ ((N.mul m (N.mul n p)) = (N.mul n (N.mul m p)))).
Axiom thm_MULT_EQ_0 : forall m : N, forall n : N, ((N.mul m n) = (N0)) = ((m = (N0)) \/ (n = (N0))).
Axiom thm_EQ_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, ((N.mul m n) = (N.mul m p)) = ((m = (N0)) \/ (n = p)).
Axiom thm_EQ_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, ((N.mul m p) = (N.mul n p)) = ((m = n) \/ (p = (N0))).
Axiom thm_MULT_2 : forall n : N, (N.mul ((BIT0 (BIT1 N0))) n) = (N.add n n).
Axiom thm_MULT_EQ_1 : forall m : N, forall n : N, ((N.mul m n) = ((BIT1 N0))) = ((m = ((BIT1 N0))) /\ (n = ((BIT1 N0)))).
Axiom thm_EXP : (forall m : N, (N.pow m (N0)) = ((BIT1 N0))) /\ (forall m : N, forall n : N, (N.pow m (N.succ n)) = (N.mul m (N.pow m n))).
Axiom thm_EXP_EQ_0 : forall m : N, forall n : N, ((N.pow m n) = (N0)) = ((m = (N0)) /\ (~ (n = (N0)))).
Axiom thm_EXP_EQ_1 : forall x : N, forall n : N, ((N.pow x n) = ((BIT1 N0))) = ((x = ((BIT1 N0))) \/ (n = (N0))).
Axiom thm_EXP_ZERO : forall n : N, (N.pow (N0) n) = (@COND N (n = (N0)) ((BIT1 N0)) (N0)).
Axiom thm_EXP_ADD : forall m : N, forall n : N, forall p : N, (N.pow m (N.add n p)) = (N.mul (N.pow m n) (N.pow m p)).
Axiom thm_EXP_ONE : forall n : N, (N.pow ((BIT1 N0)) n) = ((BIT1 N0)).
Axiom thm_EXP_1 : forall n : N, (N.pow n ((BIT1 N0))) = n.
Axiom thm_EXP_2 : forall n : N, (N.pow n ((BIT0 (BIT1 N0)))) = (N.mul n n).
Axiom thm_MULT_EXP : forall p : N, forall m : N, forall n : N, (N.pow (N.mul m n) p) = (N.mul (N.pow m p) (N.pow n p)).
Axiom thm_EXP_MULT : forall m : N, forall n : N, forall p : N, (N.pow m (N.mul n p)) = (N.pow (N.pow m n) p).
Axiom thm_EXP_EXP : forall x : N, forall m : N, forall n : N, (N.pow (N.pow x m) n) = (N.pow x (N.mul m n)).
Axiom thm_LE : (forall m : N, (N.le m (N0)) = (m = (N0))) /\ (forall m : N, forall n : N, (N.le m (N.succ n)) = ((m = (N.succ n)) \/ (N.le m n))).
Axiom thm_LT : (forall m : N, (N.lt m (N0)) = False) /\ (forall m : N, forall n : N, (N.lt m (N.succ n)) = ((m = n) \/ (N.lt m n))).
Axiom thm_GE : forall n : N, forall m : N, (N.ge m n) = (N.le n m).
Axiom thm_GT : forall n : N, forall m : N, (N.gt m n) = (N.lt n m).
Axiom thm_MAX : forall m : N, forall n : N, (N.max m n) = (@COND N (N.le m n) n m).
Axiom thm_MIN : forall m : N, forall n : N, (N.min m n) = (@COND N (N.le m n) m n).
Axiom thm_LE_SUC_LT : forall m : N, forall n : N, (N.le (N.succ m) n) = (N.lt m n).
Axiom thm_LT_SUC_LE : forall m : N, forall n : N, (N.lt m (N.succ n)) = (N.le m n).
Axiom thm_LE_SUC : forall m : N, forall n : N, (N.le (N.succ m) (N.succ n)) = (N.le m n).
Axiom thm_LT_SUC : forall m : N, forall n : N, (N.lt (N.succ m) (N.succ n)) = (N.lt m n).
Axiom thm_LE_0 : forall n : N, N.le (N0) n.
Axiom thm_LT_0 : forall n : N, N.lt (N0) (N.succ n).
Axiom thm_LE_REFL : forall n : N, N.le n n.
Axiom thm_LT_REFL : forall n : N, ~ (N.lt n n).
Axiom thm_LT_IMP_NE : forall m : N, forall n : N, (N.lt m n) -> ~ (m = n).
Axiom thm_LE_ANTISYM : forall m : N, forall n : N, ((N.le m n) /\ (N.le n m)) = (m = n).
Axiom thm_LT_ANTISYM : forall m : N, forall n : N, ~ ((N.lt m n) /\ (N.lt n m)).
Axiom thm_LET_ANTISYM : forall m : N, forall n : N, ~ ((N.le m n) /\ (N.lt n m)).
Axiom thm_LTE_ANTISYM : forall m : N, forall n : N, ~ ((N.lt m n) /\ (N.le n m)).
Axiom thm_LE_TRANS : forall m : N, forall n : N, forall p : N, ((N.le m n) /\ (N.le n p)) -> N.le m p.
Axiom thm_LT_TRANS : forall m : N, forall n : N, forall p : N, ((N.lt m n) /\ (N.lt n p)) -> N.lt m p.
Axiom thm_LET_TRANS : forall m : N, forall n : N, forall p : N, ((N.le m n) /\ (N.lt n p)) -> N.lt m p.
Axiom thm_LTE_TRANS : forall m : N, forall n : N, forall p : N, ((N.lt m n) /\ (N.le n p)) -> N.lt m p.
Axiom thm_LE_CASES : forall m : N, forall n : N, (N.le m n) \/ (N.le n m).
Axiom thm_LT_CASES : forall m : N, forall n : N, (N.lt m n) \/ ((N.lt n m) \/ (m = n)).
Axiom thm_LET_CASES : forall m : N, forall n : N, (N.le m n) \/ (N.lt n m).
Axiom thm_LTE_CASES : forall m : N, forall n : N, (N.lt m n) \/ (N.le n m).
Axiom thm_LE_LT : forall m : N, forall n : N, (N.le m n) = ((N.lt m n) \/ (m = n)).
Axiom thm_LT_LE : forall m : N, forall n : N, (N.lt m n) = ((N.le m n) /\ (~ (m = n))).
Axiom thm_NOT_LE : forall m : N, forall n : N, (~ (N.le m n)) = (N.lt n m).
Axiom thm_NOT_LT : forall m : N, forall n : N, (~ (N.lt m n)) = (N.le n m).
Axiom thm_LT_IMP_LE : forall m : N, forall n : N, (N.lt m n) -> N.le m n.
Axiom thm_EQ_IMP_LE : forall m : N, forall n : N, (m = n) -> N.le m n.
Axiom thm_LT_NZ : forall n : N, (N.lt (N0) n) = (~ (n = (N0))).
Axiom thm_LE_1 : (forall n : N, (~ (n = (N0))) -> N.lt (N0) n) /\ ((forall n : N, (~ (n = (N0))) -> N.le ((BIT1 N0)) n) /\ ((forall n : N, (N.lt (N0) n) -> ~ (n = (N0))) /\ ((forall n : N, (N.lt (N0) n) -> N.le ((BIT1 N0)) n) /\ ((forall n : N, (N.le ((BIT1 N0)) n) -> N.lt (N0) n) /\ (forall n : N, (N.le ((BIT1 N0)) n) -> ~ (n = (N0))))))).
Axiom thm_LE_EXISTS : forall m : N, forall n : N, (N.le m n) = (exists d : N, n = (N.add m d)).
Axiom thm_LT_EXISTS : forall m : N, forall n : N, (N.lt m n) = (exists d : N, n = (N.add m (N.succ d))).
Axiom thm_LE_ADD : forall m : N, forall n : N, N.le m (N.add m n).
Axiom thm_LE_ADDR : forall m : N, forall n : N, N.le n (N.add m n).
Axiom thm_LT_ADD : forall m : N, forall n : N, (N.lt m (N.add m n)) = (N.lt (N0) n).
Axiom thm_LT_ADDR : forall m : N, forall n : N, (N.lt n (N.add m n)) = (N.lt (N0) m).
Axiom thm_LE_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.add m n) (N.add m p)) = (N.le n p).
Axiom thm_LE_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.add m p) (N.add n p)) = (N.le m n).
Axiom thm_LT_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.add m n) (N.add m p)) = (N.lt n p).
Axiom thm_LT_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.add m p) (N.add n p)) = (N.lt m n).
Axiom thm_LE_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m p) /\ (N.le n q)) -> N.le (N.add m n) (N.add p q).
Axiom thm_LET_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m p) /\ (N.lt n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LTE_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m p) /\ (N.le n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LT_ADD2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m p) /\ (N.lt n q)) -> N.lt (N.add m n) (N.add p q).
Axiom thm_LT_MULT : forall m : N, forall n : N, (N.lt (N0) (N.mul m n)) = ((N.lt (N0) m) /\ (N.lt (N0) n)).
Axiom thm_LE_MULT2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.le m n) /\ (N.le p q)) -> N.le (N.mul m p) (N.mul n q).
Axiom thm_LT_LMULT : forall m : N, forall n : N, forall p : N, ((~ (m = (N0))) /\ (N.lt n p)) -> N.lt (N.mul m n) (N.mul m p).
Axiom thm_LE_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.mul m n) (N.mul m p)) = ((m = (N0)) \/ (N.le n p)).
Axiom thm_LE_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, (N.le (N.mul m p) (N.mul n p)) = ((N.le m n) \/ (p = (N0))).
Axiom thm_LT_MULT_LCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.mul m n) (N.mul m p)) = ((~ (m = (N0))) /\ (N.lt n p)).
Axiom thm_LT_MULT_RCANCEL : forall m : N, forall n : N, forall p : N, (N.lt (N.mul m p) (N.mul n p)) = ((N.lt m n) /\ (~ (p = (N0)))).
Axiom thm_LT_MULT2 : forall m : N, forall n : N, forall p : N, forall q : N, ((N.lt m n) /\ (N.lt p q)) -> N.lt (N.mul m p) (N.mul n q).
Axiom thm_LE_SQUARE_REFL : forall n : N, N.le n (N.mul n n).
Axiom thm_LT_POW2_REFL : forall n : N, N.lt n (N.pow ((BIT0 (BIT1 N0))) n).
Axiom thm_WLOG_LE : forall (P : N -> N -> Prop), ((forall m : N, forall n : N, (P m n) = (P n m)) /\ (forall m : N, forall n : N, (N.le m n) -> P m n)) -> forall m : N, forall n : N, P m n.
Axiom thm_WLOG_LT : forall (P : N -> N -> Prop), ((forall m : N, P m m) /\ ((forall m : N, forall n : N, (P m n) = (P n m)) /\ (forall m : N, forall n : N, (N.lt m n) -> P m n))) -> forall m : N, forall y : N, P m y.
Axiom thm_WLOG_LE_3 : forall P : N -> N -> N -> Prop, ((forall x : N, forall y : N, forall z : N, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : N, forall y : N, forall z : N, ((N.le x y) /\ (N.le y z)) -> P x y z)) -> forall x : N, forall y : N, forall z : N, P x y z.
Axiom thm_num_WF : forall P : N -> Prop, (forall n : N, (forall m : N, (N.lt m n) -> P m) -> P n) -> forall n : N, P n.
Axiom thm_num_WOP : forall P : N -> Prop, (exists n : N, P n) = (exists n : N, (P n) /\ (forall m : N, (N.lt m n) -> ~ (P m))).
Axiom thm_num_MAX : forall P : N -> Prop, ((exists x : N, P x) /\ (exists M : N, forall x : N, (P x) -> N.le x M)) = (exists m : N, (P m) /\ (forall x : N, (P x) -> N.le x m)).
Axiom thm_LE_INDUCT : forall P : N -> N -> Prop, ((forall m : N, P m m) /\ (forall m : N, forall n : N, ((N.le m n) /\ (P m n)) -> P m (N.succ n))) -> forall m : N, forall n : N, (N.le m n) -> P m n.
Axiom thm_num_INDUCTION_DOWN : forall P : N -> Prop, forall m : N, ((forall n : N, (N.le m n) -> P n) /\ (forall n : N, ((N.lt n m) /\ (P (N.add n ((BIT1 N0))))) -> P n)) -> forall n : N, P n.
Axiom thm_EVEN : ((N.Even (N0)) = True) /\ (forall n : N, (N.Even (N.succ n)) = (~ (N.Even n))).
Axiom thm_ODD : ((N.Odd (N0)) = False) /\ (forall n : N, (N.Odd (N.succ n)) = (~ (N.Odd n))).
Axiom thm_NOT_EVEN : forall n : N, (~ (N.Even n)) = (N.Odd n).
Axiom thm_NOT_ODD : forall n : N, (~ (N.Odd n)) = (N.Even n).
Axiom thm_EVEN_OR_ODD : forall n : N, (N.Even n) \/ (N.Odd n).
Axiom thm_EVEN_AND_ODD : forall n : N, ~ ((N.Even n) /\ (N.Odd n)).
Axiom thm_EVEN_ADD : forall m : N, forall n : N, (N.Even (N.add m n)) = ((N.Even m) = (N.Even n)).
Axiom thm_EVEN_MULT : forall m : N, forall n : N, (N.Even (N.mul m n)) = ((N.Even m) \/ (N.Even n)).
Axiom thm_EVEN_EXP : forall m : N, forall n : N, (N.Even (N.pow m n)) = ((N.Even m) /\ (~ (n = (N0)))).
Axiom thm_ODD_ADD : forall m : N, forall n : N, (N.Odd (N.add m n)) = (~ ((N.Odd m) = (N.Odd n))).
Axiom thm_ODD_MULT : forall m : N, forall n : N, (N.Odd (N.mul m n)) = ((N.Odd m) /\ (N.Odd n)).
Axiom thm_ODD_EXP : forall m : N, forall n : N, (N.Odd (N.pow m n)) = ((N.Odd m) \/ (n = (N0))).
Axiom thm_EVEN_DOUBLE : forall n : N, N.Even (N.mul ((BIT0 (BIT1 N0))) n).
Axiom thm_ODD_DOUBLE : forall n : N, N.Odd (N.succ (N.mul ((BIT0 (BIT1 N0))) n)).
Axiom thm_EVEN_EXISTS_LEMMA : forall n : N, ((N.Even n) -> exists m : N, n = (N.mul ((BIT0 (BIT1 N0))) m)) /\ ((~ (N.Even n)) -> exists m : N, n = (N.succ (N.mul ((BIT0 (BIT1 N0))) m))).
Axiom thm_EVEN_EXISTS : forall n : N, (N.Even n) = (exists m : N, n = (N.mul ((BIT0 (BIT1 N0))) m)).
Axiom thm_ODD_EXISTS : forall n : N, (N.Odd n) = (exists m : N, n = (N.succ (N.mul ((BIT0 (BIT1 N0))) m))).
Axiom thm_EVEN_ODD_DECOMPOSITION : forall n : N, (exists k : N, exists m : N, (N.Odd m) /\ (n = (N.mul (N.pow ((BIT0 (BIT1 N0))) k) m))) = (~ (n = (N0))).
Axiom thm_SUB : (forall m : N, (N.sub m (N0)) = m) /\ (forall m : N, forall n : N, (N.sub m (N.succ n)) = (N.pred (N.sub m n))).
Axiom thm_SUB_0 : forall m : N, ((N.sub (N0) m) = (N0)) /\ ((N.sub m (N0)) = m).
Axiom thm_SUB_PRESUC : forall m : N, forall n : N, (N.pred (N.sub (N.succ m) n)) = (N.sub m n).
Axiom thm_SUB_SUC : forall m : N, forall n : N, (N.sub (N.succ m) (N.succ n)) = (N.sub m n).
Axiom thm_SUB_REFL : forall n : N, (N.sub n n) = (N0).
Axiom thm_ADD_SUB : forall m : N, forall n : N, (N.sub (N.add m n) n) = m.
Axiom thm_ADD_SUB2 : forall m : N, forall n : N, (N.sub (N.add m n) m) = n.
Axiom thm_SUB_EQ_0 : forall m : N, forall n : N, ((N.sub m n) = (N0)) = (N.le m n).
Axiom thm_ADD_SUBR2 : forall m : N, forall n : N, (N.sub m (N.add m n)) = (N0).
Axiom thm_ADD_SUBR : forall m : N, forall n : N, (N.sub n (N.add m n)) = (N0).
Axiom thm_SUB_ADD : forall m : N, forall n : N, (N.le n m) -> (N.add (N.sub m n) n) = m.
Axiom thm_SUB_ADD_LCANCEL : forall m : N, forall n : N, forall p : N, (N.sub (N.add m n) (N.add m p)) = (N.sub n p).
Axiom thm_SUB_ADD_RCANCEL : forall m : N, forall n : N, forall p : N, (N.sub (N.add m p) (N.add n p)) = (N.sub m n).
Axiom thm_LEFT_SUB_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul m (N.sub n p)) = (N.sub (N.mul m n) (N.mul m p)).
Axiom thm_RIGHT_SUB_DISTRIB : forall m : N, forall n : N, forall p : N, (N.mul (N.sub m n) p) = (N.sub (N.mul m p) (N.mul n p)).
Axiom thm_SUC_SUB1 : forall n : N, (N.sub (N.succ n) ((BIT1 N0))) = n.
Axiom thm_EVEN_SUB : forall m : N, forall n : N, (N.Even (N.sub m n)) = ((N.le m n) \/ ((N.Even m) = (N.Even n))).
Axiom thm_ODD_SUB : forall m : N, forall n : N, (N.Odd (N.sub m n)) = ((N.lt n m) /\ (~ ((N.Odd m) = (N.Odd n)))).
Axiom thm_FACT : ((fact (N0)) = ((BIT1 N0))) /\ (forall n : N, (fact (N.succ n)) = (N.mul (N.succ n) (fact n))).
Axiom thm_FACT_LT : forall n : N, N.lt (N0) (fact n).
Axiom thm_FACT_LE : forall n : N, N.le ((BIT1 N0)) (fact n).
Axiom thm_FACT_NZ : forall n : N, ~ ((fact n) = (N0)).
Axiom thm_FACT_MONO : forall m : N, forall n : N, (N.le m n) -> N.le (fact m) (fact n).
Axiom thm_EXP_LT_0 : forall n : N, forall x : N, (N.lt (N0) (N.pow x n)) = ((~ (x = (N0))) \/ (n = (N0))).
Axiom thm_LT_EXP : forall x : N, forall m : N, forall n : N, (N.lt (N.pow x m) (N.pow x n)) = (((N.le ((BIT0 (BIT1 N0))) x) /\ (N.lt m n)) \/ ((x = (N0)) /\ ((~ (m = (N0))) /\ (n = (N0))))).
Axiom thm_LE_EXP : forall x : N, forall m : N, forall n : N, (N.le (N.pow x m) (N.pow x n)) = (@COND Prop (x = (N0)) ((m = (N0)) -> n = (N0)) ((x = ((BIT1 N0))) \/ (N.le m n))).
Axiom thm_EQ_EXP : forall x : N, forall m : N, forall n : N, ((N.pow x m) = (N.pow x n)) = (@COND Prop (x = (N0)) ((m = (N0)) = (n = (N0))) ((x = ((BIT1 N0))) \/ (m = n))).
Axiom thm_EXP_MONO_LE_IMP : forall x : N, forall y : N, forall n : N, (N.le x y) -> N.le (N.pow x n) (N.pow y n).
Axiom thm_EXP_MONO_LT_IMP : forall x : N, forall y : N, forall n : N, ((N.lt x y) /\ (~ (n = (N0)))) -> N.lt (N.pow x n) (N.pow y n).
Axiom thm_EXP_MONO_LE : forall x : N, forall y : N, forall n : N, (N.le (N.pow x n) (N.pow y n)) = ((N.le x y) \/ (n = (N0))).
Axiom thm_EXP_MONO_LT : forall x : N, forall y : N, forall n : N, (N.lt (N.pow x n) (N.pow y n)) = ((N.lt x y) /\ (~ (n = (N0)))).
Axiom thm_EXP_MONO_EQ : forall x : N, forall y : N, forall n : N, ((N.pow x n) = (N.pow y n)) = ((x = y) \/ (n = (N0))).
Axiom thm_DIVMOD_EXIST : forall m : N, forall n : N, (~ (n = (N0))) -> exists q : N, exists r : N, (m = (N.add (N.mul q n) r)) /\ (N.lt r n).
Axiom thm_DIVMOD_EXIST_0 : forall m : N, forall n : N, exists q : N, exists r : N, @COND Prop (n = (N0)) ((q = (N0)) /\ (r = m)) ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)).
Axiom thm_DIVISION : forall m : N, forall n : N, (~ (n = (N0))) -> (m = (N.add (N.mul (N.div m n) n) (N.modulo m n))) /\ (N.lt (N.modulo m n) n).
Axiom thm_DIV_ZERO : forall n : N, (N.div n (N0)) = (N0).
Axiom thm_MOD_ZERO : forall n : N, (N.modulo n (N0)) = n.
Axiom thm_DIVISION_SIMP : (forall m : N, forall n : N, (N.add (N.mul (N.div m n) n) (N.modulo m n)) = m) /\ (forall m : N, forall n : N, (N.add (N.mul n (N.div m n)) (N.modulo m n)) = m).
Axiom thm_EQ_DIVMOD : forall p : N, forall m : N, forall n : N, (((N.div m p) = (N.div n p)) /\ ((N.modulo m p) = (N.modulo n p))) = (m = n).
Axiom thm_MOD_LT_EQ : forall m : N, forall n : N, (N.lt (N.modulo m n) n) = (~ (n = (N0))).
Axiom thm_MOD_LT_EQ_LT : forall m : N, forall n : N, (N.lt (N.modulo m n) n) = (N.lt (N0) n).
Axiom thm_DIVMOD_UNIQ_LEMMA : forall m : N, forall n : N, forall q1 : N, forall r1 : N, forall q2 : N, forall r2 : N, (((m = (N.add (N.mul q1 n) r1)) /\ (N.lt r1 n)) /\ ((m = (N.add (N.mul q2 n) r2)) /\ (N.lt r2 n))) -> (q1 = q2) /\ (r1 = r2).
Axiom thm_DIVMOD_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> ((N.div m n) = q) /\ ((N.modulo m n) = r).
Axiom thm_MOD_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> (N.modulo m n) = r.
Axiom thm_DIV_UNIQ : forall m : N, forall n : N, forall q : N, forall r : N, ((m = (N.add (N.mul q n) r)) /\ (N.lt r n)) -> (N.div m n) = q.
Axiom thm_MOD_0 : forall n : N, (N.modulo (N0) n) = (N0).
Axiom thm_DIV_0 : forall n : N, (N.div (N0) n) = (N0).
Axiom thm_MOD_MULT : forall m : N, forall n : N, (N.modulo (N.mul m n) m) = (N0).
Axiom thm_DIV_MULT : forall m : N, forall n : N, (~ (m = (N0))) -> (N.div (N.mul m n) m) = n.
Axiom thm_MOD_LT : forall m : N, forall n : N, (N.lt m n) -> (N.modulo m n) = m.
Axiom thm_MOD_EQ_SELF : forall m : N, forall n : N, ((N.modulo m n) = m) = ((n = (N0)) \/ (N.lt m n)).
Axiom thm_MOD_CASES : forall n : N, forall p : N, (N.lt n (N.mul ((BIT0 (BIT1 N0))) p)) -> (N.modulo n p) = (@COND N (N.lt n p) n (N.sub n p)).
Axiom thm_MOD_ADD_CASES : forall m : N, forall n : N, forall p : N, ((N.lt m p) /\ (N.lt n p)) -> (N.modulo (N.add m n) p) = (@COND N (N.lt (N.add m n) p) (N.add m n) (N.sub (N.add m n) p)).
Axiom thm_MOD_EQ : forall m : N, forall n : N, forall p : N, forall q : N, (m = (N.add n (N.mul q p))) -> (N.modulo m p) = (N.modulo n p).
Axiom thm_DIV_LE : forall m : N, forall n : N, N.le (N.div m n) m.
Axiom thm_DIV_MUL_LE : forall m : N, forall n : N, N.le (N.mul n (N.div m n)) m.
Axiom thm_MOD_LE_TWICE : forall m : N, forall n : N, ((N.lt (N0) m) /\ (N.le m n)) -> N.le (N.mul ((BIT0 (BIT1 N0))) (N.modulo n m)) n.
Axiom thm_MOD_1 : forall n : N, (N.modulo n ((BIT1 N0))) = (N0).
Axiom thm_DIV_1 : forall n : N, (N.div n ((BIT1 N0))) = n.
Axiom thm_DIV_LT : forall m : N, forall n : N, (N.lt m n) -> (N.div m n) = (N0).
Axiom thm_MOD_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.modulo m (N.mul n p)) n) = (N.modulo m n).
Axiom thm_MOD_MOD_REFL : forall m : N, forall n : N, (N.modulo (N.modulo m n) n) = (N.modulo m n).
Axiom thm_MOD_MOD_LE : forall m : N, forall n : N, forall p : N, ((~ (n = (N0))) /\ (N.le n p)) -> (N.modulo (N.modulo m n) p) = (N.modulo m n).
Axiom thm_MOD_EVEN_2 : forall m : N, forall n : N, (N.Even n) -> (N.modulo (N.modulo m n) ((BIT0 (BIT1 N0)))) = (N.modulo m ((BIT0 (BIT1 N0)))).
Axiom thm_DIV_MULT2 : forall m : N, forall n : N, forall p : N, (~ (m = (N0))) -> (N.div (N.mul m n) (N.mul m p)) = (N.div n p).
Axiom thm_MOD_MULT2 : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul m n) (N.mul m p)) = (N.mul m (N.modulo n p)).
Axiom thm_MOD_EXISTS : forall m : N, forall n : N, (exists q : N, m = (N.mul n q)) = (@COND Prop (n = (N0)) (m = (N0)) ((N.modulo m n) = (N0))).
Axiom thm_LE_RDIV_EQ : forall a : N, forall b : N, forall n : N, (~ (a = (N0))) -> (N.le n (N.div b a)) = (N.le (N.mul a n) b).
Axiom thm_RDIV_LT_EQ : forall a : N, forall b : N, forall n : N, (~ (a = (N0))) -> (N.lt (N.div b a) n) = (N.lt b (N.mul a n)).
Axiom thm_LE_LDIV_EQ : forall a : N, forall b : N, forall n : N, (~ (a = (N0))) -> (N.le (N.div b a) n) = (N.lt b (N.mul a (N.add n ((BIT1 N0))))).
Axiom thm_LDIV_LT_EQ : forall a : N, forall b : N, forall n : N, (~ (a = (N0))) -> (N.lt n (N.div b a)) = (N.le (N.mul a (N.add n ((BIT1 N0)))) b).
Axiom thm_LE_LDIV : forall a : N, forall b : N, forall n : N, ((~ (a = (N0))) /\ (N.le b (N.mul a n))) -> N.le (N.div b a) n.
Axiom thm_DIV_MONO : forall m : N, forall n : N, forall p : N, (N.le m n) -> N.le (N.div m p) (N.div n p).
Axiom thm_DIV_MONO_LT : forall m : N, forall n : N, forall p : N, ((~ (p = (N0))) /\ (N.le (N.add m p) n)) -> N.lt (N.div m p) (N.div n p).
Axiom thm_DIV_EQ_0 : forall m : N, forall n : N, (~ (n = (N0))) -> ((N.div m n) = (N0)) = (N.lt m n).
Axiom thm_MOD_DIV_EQ_0 : forall m : N, forall n : N, (~ (n = (N0))) -> (N.div (N.modulo m n) n) = (N0).
Axiom thm_MOD_EQ_0 : forall m : N, forall n : N, ((N.modulo m n) = (N0)) = (exists q : N, m = (N.mul q n)).
Axiom thm_DIV_EQ_SELF : forall m : N, forall n : N, ((N.div m n) = m) = ((m = (N0)) \/ (n = ((BIT1 N0)))).
Axiom thm_MOD_REFL : forall n : N, (N.modulo n n) = (N0).
Axiom thm_EVEN_MOD : forall n : N, (N.Even n) = ((N.modulo n ((BIT0 (BIT1 N0)))) = (N0)).
Axiom thm_ODD_MOD : forall n : N, (N.Odd n) = ((N.modulo n ((BIT0 (BIT1 N0)))) = ((BIT1 N0))).
Axiom thm_MOD_2_CASES : forall n : N, (N.modulo n ((BIT0 (BIT1 N0)))) = (@COND N (N.Even n) (N0) ((BIT1 N0))).
Axiom thm_EVEN_MOD_EVEN : forall m : N, forall n : N, (N.Even n) -> (N.Even (N.modulo m n)) = (N.Even m).
Axiom thm_ODD_MOD_EVEN : forall m : N, forall n : N, (N.Even n) -> (N.Odd (N.modulo m n)) = (N.Odd m).
Axiom thm_HALF_DOUBLE : (forall n : N, (N.div (N.mul ((BIT0 (BIT1 N0))) n) ((BIT0 (BIT1 N0)))) = n) /\ (forall n : N, (N.div (N.mul n ((BIT0 (BIT1 N0)))) ((BIT0 (BIT1 N0)))) = n).
Axiom thm_DOUBLE_HALF : (forall n : N, (N.Even n) -> (N.mul ((BIT0 (BIT1 N0))) (N.div n ((BIT0 (BIT1 N0))))) = n) /\ (forall n : N, (N.Even n) -> (N.mul (N.div n ((BIT0 (BIT1 N0)))) ((BIT0 (BIT1 N0)))) = n).
Axiom thm_MOD_MULT_RMOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul m (N.modulo p n)) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_MULT_LMOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul (N.modulo m n) p) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_MULT_MOD2 : forall m : N, forall n : N, forall p : N, (N.modulo (N.mul (N.modulo m n) (N.modulo p n)) n) = (N.modulo (N.mul m p) n).
Axiom thm_MOD_EXP_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.pow (N.modulo m n) p) n) = (N.modulo (N.pow m p) n).
Axiom thm_MOD_MULT_ADD : (forall m : N, forall n : N, forall p : N, (N.modulo (N.add (N.mul m n) p) n) = (N.modulo p n)) /\ ((forall m : N, forall n : N, forall p : N, (N.modulo (N.add (N.mul n m) p) n) = (N.modulo p n)) /\ ((forall m : N, forall n : N, forall p : N, (N.modulo (N.add p (N.mul m n)) n) = (N.modulo p n)) /\ (forall m : N, forall n : N, forall p : N, (N.modulo (N.add p (N.mul n m)) n) = (N.modulo p n)))).
Axiom thm_DIV_MULT_ADD : (forall a : N, forall b : N, forall n : N, (~ (n = (N0))) -> (N.div (N.add (N.mul a n) b) n) = (N.add a (N.div b n))) /\ ((forall a : N, forall b : N, forall n : N, (~ (n = (N0))) -> (N.div (N.add (N.mul n a) b) n) = (N.add a (N.div b n))) /\ ((forall a : N, forall b : N, forall n : N, (~ (n = (N0))) -> (N.div (N.add b (N.mul a n)) n) = (N.add (N.div b n) a)) /\ (forall a : N, forall b : N, forall n : N, (~ (n = (N0))) -> (N.div (N.add b (N.mul n a)) n) = (N.add (N.div b n) a)))).
Axiom thm_MOD_ADD_MOD : forall a : N, forall b : N, forall n : N, (N.modulo (N.add (N.modulo a n) (N.modulo b n)) n) = (N.modulo (N.add a b) n).
Axiom thm_DIV_ADD_MOD : forall a : N, forall b : N, forall n : N, (~ (n = (N0))) -> ((N.modulo (N.add a b) n) = (N.add (N.modulo a n) (N.modulo b n))) = ((N.div (N.add a b) n) = (N.add (N.div a n) (N.div b n))).
Axiom thm_MOD_ADD_EQ_EQ : forall n : N, forall x : N, forall y : N, ((N.modulo (N.add x y) n) = (N.add (N.modulo x n) (N.modulo y n))) = ((n = (N0)) \/ (N.lt (N.add (N.modulo x n) (N.modulo y n)) n)).
Axiom thm_DIV_ADD_EQ_EQ : forall n : N, forall x : N, forall y : N, ((N.div (N.add x y) n) = (N.add (N.div x n) (N.div y n))) = ((n = (N0)) \/ (N.lt (N.add (N.modulo x n) (N.modulo y n)) n)).
Axiom thm_DIV_ADD_EQ : forall n : N, forall x : N, forall y : N, (N.lt (N.add (N.modulo x n) (N.modulo y n)) n) -> (N.div (N.add x y) n) = (N.add (N.div x n) (N.div y n)).
Axiom thm_MOD_ADD_EQ : forall n : N, forall x : N, forall y : N, (N.lt (N.add (N.modulo x n) (N.modulo y n)) n) -> (N.modulo (N.add x y) n) = (N.add (N.modulo x n) (N.modulo y n)).
Axiom thm_DIV_REFL : forall n : N, (~ (n = (N0))) -> (N.div n n) = ((BIT1 N0)).
Axiom thm_MOD_LE : forall m : N, forall n : N, N.le (N.modulo m n) m.
Axiom thm_DIV_MONO2 : forall m : N, forall n : N, forall p : N, ((~ (p = (N0))) /\ (N.le p m)) -> N.le (N.div n m) (N.div n p).
Axiom thm_DIV_LE_EXCLUSION : forall a : N, forall b : N, forall c : N, forall d : N, ((~ (b = (N0))) /\ (N.lt (N.mul b c) (N.mul (N.add a ((BIT1 N0))) d))) -> N.le (N.div c d) (N.div a b).
Axiom thm_DIV_EQ_EXCLUSION : forall a : N, forall b : N, forall c : N, forall d : N, ((N.lt (N.mul b c) (N.mul (N.add a ((BIT1 N0))) d)) /\ (N.lt (N.mul a d) (N.mul (N.add c ((BIT1 N0))) b))) -> (N.div a b) = (N.div c d).
Axiom thm_MULT_DIV_LE : forall m : N, forall n : N, forall p : N, N.le (N.mul m (N.div n p)) (N.div (N.mul m n) p).
Axiom thm_DIV_DIV : forall m : N, forall n : N, forall p : N, (N.div (N.div m n) p) = (N.div m (N.mul n p)).
Axiom thm_DIV_MOD : forall m : N, forall n : N, forall p : N, (N.modulo (N.div m n) p) = (N.div (N.modulo m (N.mul n p)) n).
Axiom thm_MOD_MULT_MOD : forall m : N, forall n : N, forall p : N, (N.modulo m (N.mul n p)) = (N.add (N.mul n (N.modulo (N.div m n) p)) (N.modulo m n)).
Axiom thm_MOD_MOD_EXP_MIN : forall x : N, forall p : N, forall m : N, forall n : N, (N.modulo (N.modulo x (N.pow p m)) (N.pow p n)) = (N.modulo x (N.pow p (N.min m n))).
Axiom thm_MOD_EXP : forall m : N, forall n : N, forall p : N, (~ (m = (N0))) -> (N.modulo (N.pow m n) (N.pow m p)) = (@COND N ((N.le p n) \/ (m = ((BIT1 N0)))) (N0) (N.pow m n)).
Axiom thm_DIV_EXP : forall m : N, forall n : N, forall p : N, (~ (m = (N0))) -> (N.div (N.pow m n) (N.pow m p)) = (@COND N (N.le p n) (N.pow m (N.sub n p)) (@COND N (m = ((BIT1 N0))) ((BIT1 N0)) (N0))).
Axiom thm_FORALL_LT_MOD_THM : forall P : N -> Prop, forall n : N, (forall a : N, (N.lt a n) -> P a) = ((n = (N0)) \/ (forall a : N, P (N.modulo a n))).
Axiom thm_FORALL_MOD_THM : forall P : N -> Prop, forall n : N, (~ (n = (N0))) -> (forall a : N, P (N.modulo a n)) = (forall a : N, (N.lt a n) -> P a).
Axiom thm_EXISTS_LT_MOD_THM : forall P : N -> Prop, forall n : N, (exists a : N, (N.lt a n) /\ (P a)) = ((~ (n = (N0))) /\ (exists a : N, P (N.modulo a n))).
Axiom thm_EXISTS_MOD_THM : forall P : N -> Prop, forall n : N, (~ (n = (N0))) -> (exists a : N, P (N.modulo a n)) = (exists a : N, (N.lt a n) /\ (P a)).
Axiom thm_PRE_ELIM_THM : forall (n : N) (P : N -> Prop), (P (N.pred n)) = (forall m : N, ((n = (N.succ m)) \/ ((m = (N0)) /\ (n = (N0)))) -> P m).
Axiom thm_SUB_ELIM_THM : forall (a : N) (b : N) (P : N -> Prop), (P (N.sub a b)) = (forall d : N, ((a = (N.add b d)) \/ ((N.lt a b) /\ (d = (N0)))) -> P d).
Axiom thm_DIVMOD_ELIM_THM : forall (m : N) (n : N) (P : N -> N -> Prop), (P (N.div m n) (N.modulo m n)) = (forall q : N, forall r : N, (((n = (N0)) /\ ((q = (N0)) /\ (r = m))) \/ ((m = (N.add (N.mul q n) r)) /\ (N.lt r n))) -> P q r).
Axiom thm_minimal : forall P : N -> Prop, (minimal P) = (@ε N (fun n : N => (P n) /\ (forall m : N, (N.lt m n) -> ~ (P m)))).
Axiom thm_MINIMAL : forall P : N -> Prop, (exists n : N, P n) = ((P (minimal P)) /\ (forall m : N, (N.lt m (minimal P)) -> ~ (P m))).
Axiom thm_MINIMAL_UNIQUE : forall P : N -> Prop, forall n : N, ((P n) /\ (forall m : N, (N.lt m n) -> ~ (P m))) -> (minimal P) = n.
Axiom thm_LE_MINIMAL : forall P : N -> Prop, forall n : N, (exists r : N, P r) -> (N.le n (minimal P)) = (forall i : N, (P i) -> N.le n i).
Axiom thm_MINIMAL_LE : forall P : N -> Prop, forall n : N, (exists r : N, P r) -> (N.le (minimal P) n) = (exists i : N, (N.le i n) /\ (P i)).
Axiom thm_MINIMAL_UBOUND : forall P : N -> Prop, forall n : N, (P n) -> N.le (minimal P) n.
Axiom thm_MINIMAL_LBOUND : forall P : N -> Prop, forall n : N, ((exists r : N, P r) /\ (forall m : N, (N.lt m n) -> ~ (P m))) -> N.le n (minimal P).
Axiom thm_MINIMAL_MONO : forall P : N -> Prop, forall Q : N -> Prop, ((exists n : N, P n) /\ (forall n : N, (P n) -> Q n)) -> N.le (minimal Q) (minimal P).
Axiom thm_TRANSITIVE_STEPWISE_LT_EQ : forall R' : N -> N -> Prop, (forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) -> (forall m : N, forall n : N, (N.lt m n) -> R' m n) = (forall n : N, R' n (N.succ n)).
Axiom thm_TRANSITIVE_STEPWISE_LT : forall R' : N -> N -> Prop, ((forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : N, R' n (N.succ n))) -> forall m : N, forall n : N, (N.lt m n) -> R' m n.
Axiom thm_TRANSITIVE_STEPWISE_LE_EQ : forall R' : N -> N -> Prop, ((forall x : N, R' x x) /\ (forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z)) -> (forall m : N, forall n : N, (N.le m n) -> R' m n) = (forall n : N, R' n (N.succ n)).
Axiom thm_TRANSITIVE_STEPWISE_LE : forall R' : N -> N -> Prop, ((forall x : N, R' x x) /\ ((forall x : N, forall y : N, forall z : N, ((R' x y) /\ (R' y z)) -> R' x z) /\ (forall n : N, R' n (N.succ n)))) -> forall m : N, forall n : N, (N.le m n) -> R' m n.
Axiom thm_DEPENDENT_CHOICE_FIXED : forall {A : Type'}, forall P : N -> A -> Prop, forall R' : N -> A -> A -> Prop, forall a : A, ((P (N0) a) /\ (forall n : N, forall x : A, (P n x) -> exists y : A, (P (N.succ n) y) /\ (R' n x y))) -> exists f : N -> A, ((f (N0)) = a) /\ ((forall n : N, P n (f n)) /\ (forall n : N, R' n (f n) (f (N.succ n)))).
Axiom thm_DEPENDENT_CHOICE : forall {A : Type'}, forall P : N -> A -> Prop, forall R' : N -> A -> A -> Prop, ((exists a : A, P (N0) a) /\ (forall n : N, forall x : A, (P n x) -> exists y : A, (P (N.succ n) y) /\ (R' n x y))) -> exists f : N -> A, (forall n : N, P n (f n)) /\ (forall n : N, R' n (f n) (f (N.succ n))).
Axiom thm_WF : forall {A : Type'}, forall lt2 : A -> A -> Prop, (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y))).
Axiom thm_WF_EQ : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (exists x : A, P x) = (exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y)))).
Axiom thm_WF_IND : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (forall P : A -> Prop, (forall x : A, (forall y : A, (lt2 y x) -> P y) -> P x) -> forall x : A, P x).
Axiom thm_WF_DCHAIN : forall {A : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) = (~ (exists s : N -> A, forall n : N, lt2 (s (N.succ n)) (s n))).
Axiom thm_WF_DHAIN_TRANSITIVE : forall {A : Type'}, forall lt2 : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) -> (@well_founded A lt2) = (~ (exists s : N -> A, forall i : N, forall j : N, (N.lt i j) -> lt2 (s j) (s i))).
Axiom thm_WF_UREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> B, forall g : A -> B, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g.
Axiom thm_WF_UREC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> Prop) -> A -> Prop, (forall f : A -> Prop, forall g : A -> Prop, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> forall f : A -> Prop, forall g : A -> Prop, ((forall x : A, (f x) = (H f x)) /\ (forall x : A, (g x) = (H g x))) -> f = g) -> @well_founded A lt2.
Axiom thm_WF_REC_INVARIANT : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, forall S' : A -> B -> Prop, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> ((f z) = (g z)) /\ (S' z (f z))) -> ((H f x) = (H g x)) /\ (S' x (H f x))) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> B, forall x : A, (f x) = (H f x).
Axiom thm_WF_REC_WF : forall {A : Type'} (lt2 : A -> A -> Prop), (forall H : (A -> N) -> A -> N, (forall f : A -> N, forall g : A -> N, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> exists f : A -> N, forall x : A, (f x) = (H f x)) -> @well_founded A lt2.
Axiom thm_WF_EREC : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall H : (A -> B) -> A -> B, (forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) -> @ex1 (A -> B) (fun f : A -> B => forall x : A, (f x) = (H f x)).
Axiom thm_WF_REC_EXISTS : forall {A B : Type'} (lt2 : A -> A -> Prop), (@well_founded A lt2) -> forall P : (A -> B) -> A -> B -> Prop, ((forall f : A -> B, forall g : A -> B, forall x : A, forall y : B, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (P f x y) = (P g x y)) /\ (forall f : A -> B, forall x : A, (forall z : A, (lt2 z x) -> P f z (f z)) -> exists y : B, P f x y)) -> exists f : A -> B, forall x : A, P f x (f x).
Axiom thm_WF_SUBSET : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall lt3 : A -> A -> Prop, ((forall x : A, forall y : A, (lt2 x y) -> lt3 x y) /\ (@well_founded A lt3)) -> @well_founded A lt2.
Axiom thm_WF_RESTRICT : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall P : A -> Prop, (@well_founded A lt2) -> @well_founded A (fun x : A => fun y : A => (P x) /\ ((P y) /\ (lt2 x y))).
Axiom thm_WF_MEASURE_GEN : forall {A B : Type'}, forall lt2 : B -> B -> Prop, forall m : A -> B, (@well_founded B lt2) -> @well_founded A (fun x : A => fun x' : A => lt2 (m x) (m x')).
Axiom thm_WF_LEX_DEPENDENT : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : A -> B -> B -> Prop, ((@well_founded A R') /\ (forall a : A, @well_founded B (S' a))) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' r1 s1 s2))))))).
Axiom thm_WF_LEX : forall {A B : Type'}, forall R' : A -> A -> Prop, forall S' : B -> B -> Prop, ((@well_founded A R') /\ (@well_founded B S')) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @eq ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @eq Prop (f' (@pair A B r2 s2)) ((R' r1 r2) \/ ((r1 = r2) /\ (S' s1 s2))))))).
Axiom thm_WF_POINTWISE : forall {A B : Type'} (lt2 : A -> A -> Prop) (lt3 : B -> B -> Prop), ((@well_founded A lt2) /\ (@well_founded B lt3)) -> @well_founded (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall x1 : A, forall y1 : B, @eq ((prod A B) -> Prop) (f (@pair A B x1 y1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall x2 : A, forall y2 : B, @eq Prop (f' (@pair A B x2 y2)) ((lt2 x1 x2) /\ (lt3 y1 y2)))))).
Axiom thm_WF_num : @well_founded N N.lt.
Axiom thm_WF_REC_num : forall {A : Type'}, forall H : (N -> A) -> N -> A, (forall f : N -> A, forall g : N -> A, forall n : N, (forall m : N, (N.lt m n) -> (f m) = (g m)) -> (H f n) = (H g n)) -> exists f : N -> A, forall n : N, (f n) = (H f n).
Axiom thm_MEASURE : forall {A : Type'}, forall m : A -> N, (@MEASURE A m) = (fun x : A => fun y : A => N.lt (m x) (m y)).
Axiom thm_WF_MEASURE : forall {A : Type'}, forall m : A -> N, @well_founded A (@MEASURE A m).
Axiom thm_MEASURE_LE : forall {A : Type'} (a : A) (b : A), forall m : A -> N, (forall y : A, (@MEASURE A m y a) -> @MEASURE A m y b) = (N.le (m a) (m b)).
Axiom thm_WF_ANTISYM : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall x : A, forall y : A, (@well_founded A lt2) -> ~ ((lt2 x y) /\ (lt2 y x)).
Axiom thm_WF_REFL : forall {A : Type'} (lt2 : A -> A -> Prop), forall x : A, (@well_founded A lt2) -> ~ (lt2 x x).
Axiom thm_WF_FALSE : forall {A : Type'}, @well_founded A (fun x : A => fun y : A => False).
Axiom thm_MINIMAL_BAD_SEQUENCE : forall {A : Type'}, forall lt2 : A -> A -> Prop, forall bad : (N -> A) -> Prop, ((@well_founded A lt2) /\ ((forall x : N -> A, (~ (bad x)) -> exists n : N, forall y : N -> A, (forall k : N, (N.lt k n) -> (y k) = (x k)) -> ~ (bad y)) /\ (exists x : N -> A, bad x))) -> exists y : N -> A, (bad y) /\ (forall z : N -> A, forall n : N, ((bad z) /\ (forall k : N, (N.lt k n) -> (z k) = (y k))) -> ~ (lt2 (z n) (y n))).
Axiom thm_WF_REC_TAIL : forall {A B : Type'}, forall P : A -> Prop, forall g : A -> A, forall h : A -> B, exists f : A -> B, forall x : A, (f x) = (@COND B (P x) (f (g x)) (h x)).
Axiom thm_WF_REC_TAIL_GENERAL : forall {A B : Type'} (lt2 : A -> A -> Prop), forall P : (A -> B) -> A -> Prop, forall G : (A -> B) -> A -> A, forall H : (A -> B) -> A -> B, ((@well_founded A lt2) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> ((P f x) = (P g x)) /\ (((G f x) = (G g x)) /\ ((H f x) = (H g x)))) /\ ((forall f : A -> B, forall g : A -> B, forall x : A, (forall z : A, (lt2 z x) -> (f z) = (g z)) -> (H f x) = (H g x)) /\ (forall f : A -> B, forall x : A, forall y : A, ((P f x) /\ (lt2 y (G f x))) -> lt2 y x)))) -> exists f : A -> B, forall x : A, (f x) = (@COND B (P f x) (f (G f x)) (H f x)).
Axiom thm_ARITH_ZERO : (((N0)) = (N0)) /\ ((BIT0 N0) = N0).
Axiom thm_BIT0_0 : (BIT0 (N0)) = (N0).
Axiom thm_BIT1_0 : (BIT1 (N0)) = ((BIT1 N0)).
Axiom thm_ARITH_SUC : (forall n : N, (N.succ (n)) = ((N.succ n))) /\ (((N.succ N0) = (BIT1 N0)) /\ ((forall n : N, (N.succ (BIT0 n)) = (BIT1 n)) /\ (forall n : N, (N.succ (BIT1 n)) = (BIT0 (N.succ n))))).
Axiom thm_ARITH_PRE : (forall n : N, (N.pred (n)) = ((N.pred n))) /\ (((N.pred N0) = N0) /\ ((forall n : N, (N.pred (BIT0 n)) = (@COND N (n = N0) N0 (BIT1 (N.pred n)))) /\ (forall n : N, (N.pred (BIT1 n)) = (BIT0 n)))).
Axiom thm_ARITH_ADD : (forall m : N, forall n : N, (N.add (m) (n)) = ((N.add m n))) /\ (((N.add N0 N0) = N0) /\ ((forall n : N, (N.add N0 (BIT0 n)) = (BIT0 n)) /\ ((forall n : N, (N.add N0 (BIT1 n)) = (BIT1 n)) /\ ((forall n : N, (N.add (BIT0 n) N0) = (BIT0 n)) /\ ((forall n : N, (N.add (BIT1 n) N0) = (BIT1 n)) /\ ((forall m : N, forall n : N, (N.add (BIT0 m) (BIT0 n)) = (BIT0 (N.add m n))) /\ ((forall m : N, forall n : N, (N.add (BIT0 m) (BIT1 n)) = (BIT1 (N.add m n))) /\ ((forall m : N, forall n : N, (N.add (BIT1 m) (BIT0 n)) = (BIT1 (N.add m n))) /\ (forall m : N, forall n : N, (N.add (BIT1 m) (BIT1 n)) = (BIT0 (N.succ (N.add m n)))))))))))).
Axiom thm_ARITH_MULT : (forall m : N, forall n : N, (N.mul (m) (n)) = ((N.mul m n))) /\ (((N.mul N0 N0) = N0) /\ ((forall n : N, (N.mul N0 (BIT0 n)) = N0) /\ ((forall n : N, (N.mul N0 (BIT1 n)) = N0) /\ ((forall n : N, (N.mul (BIT0 n) N0) = N0) /\ ((forall n : N, (N.mul (BIT1 n) N0) = N0) /\ ((forall m : N, forall n : N, (N.mul (BIT0 m) (BIT0 n)) = (BIT0 (BIT0 (N.mul m n)))) /\ ((forall m : N, forall n : N, (N.mul (BIT0 m) (BIT1 n)) = (N.add (BIT0 m) (BIT0 (BIT0 (N.mul m n))))) /\ ((forall m : N, forall n : N, (N.mul (BIT1 m) (BIT0 n)) = (N.add (BIT0 n) (BIT0 (BIT0 (N.mul m n))))) /\ (forall m : N, forall n : N, (N.mul (BIT1 m) (BIT1 n)) = (N.add (BIT1 m) (N.add (BIT0 n) (BIT0 (BIT0 (N.mul m n)))))))))))))).
Axiom thm_ARITH_EXP : (forall m : N, forall n : N, (N.pow (m) (n)) = ((N.pow m n))) /\ (((N.pow N0 N0) = (BIT1 N0)) /\ ((forall m : N, (N.pow (BIT0 m) N0) = (BIT1 N0)) /\ ((forall m : N, (N.pow (BIT1 m) N0) = (BIT1 N0)) /\ ((forall n : N, (N.pow N0 (BIT0 n)) = (N.mul (N.pow N0 n) (N.pow N0 n))) /\ ((forall m : N, forall n : N, (N.pow (BIT0 m) (BIT0 n)) = (N.mul (N.pow (BIT0 m) n) (N.pow (BIT0 m) n))) /\ ((forall m : N, forall n : N, (N.pow (BIT1 m) (BIT0 n)) = (N.mul (N.pow (BIT1 m) n) (N.pow (BIT1 m) n))) /\ ((forall n : N, (N.pow N0 (BIT1 n)) = N0) /\ ((forall m : N, forall n : N, (N.pow (BIT0 m) (BIT1 n)) = (N.mul (BIT0 m) (N.mul (N.pow (BIT0 m) n) (N.pow (BIT0 m) n)))) /\ (forall m : N, forall n : N, (N.pow (BIT1 m) (BIT1 n)) = (N.mul (BIT1 m) (N.mul (N.pow (BIT1 m) n) (N.pow (BIT1 m) n)))))))))))).
Axiom thm_ARITH_EVEN : (forall n : N, (N.Even (n)) = (N.Even n)) /\ (((N.Even N0) = True) /\ ((forall n : N, (N.Even (BIT0 n)) = True) /\ (forall n : N, (N.Even (BIT1 n)) = False))).
Axiom thm_ARITH_ODD : (forall n : N, (N.Odd (n)) = (N.Odd n)) /\ (((N.Odd N0) = False) /\ ((forall n : N, (N.Odd (BIT0 n)) = False) /\ (forall n : N, (N.Odd (BIT1 n)) = True))).
Axiom thm_ARITH_LE : (forall m : N, forall n : N, (N.le (m) (n)) = (N.le m n)) /\ (((N.le N0 N0) = True) /\ ((forall n : N, (N.le (BIT0 n) N0) = (N.le n N0)) /\ ((forall n : N, (N.le (BIT1 n) N0) = False) /\ ((forall n : N, (N.le N0 (BIT0 n)) = True) /\ ((forall n : N, (N.le N0 (BIT1 n)) = True) /\ ((forall m : N, forall n : N, (N.le (BIT0 m) (BIT0 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.le (BIT0 m) (BIT1 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.le (BIT1 m) (BIT0 n)) = (N.lt m n)) /\ (forall m : N, forall n : N, (N.le (BIT1 m) (BIT1 n)) = (N.le m n)))))))))).
Axiom thm_ARITH_LT : (forall m : N, forall n : N, (N.lt (m) (n)) = (N.lt m n)) /\ (((N.lt N0 N0) = False) /\ ((forall n : N, (N.lt (BIT0 n) N0) = False) /\ ((forall n : N, (N.lt (BIT1 n) N0) = False) /\ ((forall n : N, (N.lt N0 (BIT0 n)) = (N.lt N0 n)) /\ ((forall n : N, (N.lt N0 (BIT1 n)) = True) /\ ((forall m : N, forall n : N, (N.lt (BIT0 m) (BIT0 n)) = (N.lt m n)) /\ ((forall m : N, forall n : N, (N.lt (BIT0 m) (BIT1 n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (N.lt (BIT1 m) (BIT0 n)) = (N.lt m n)) /\ (forall m : N, forall n : N, (N.lt (BIT1 m) (BIT1 n)) = (N.lt m n)))))))))).
Axiom thm_ARITH_EQ : (forall m : N, forall n : N, ((m) = (n)) = (m = n)) /\ (((N0 = N0) = True) /\ ((forall n : N, ((BIT0 n) = N0) = (n = N0)) /\ ((forall n : N, ((BIT1 n) = N0) = False) /\ ((forall n : N, (N0 = (BIT0 n)) = (N0 = n)) /\ ((forall n : N, (N0 = (BIT1 n)) = False) /\ ((forall m : N, forall n : N, ((BIT0 m) = (BIT0 n)) = (m = n)) /\ ((forall m : N, forall n : N, ((BIT0 m) = (BIT1 n)) = False) /\ ((forall m : N, forall n : N, ((BIT1 m) = (BIT0 n)) = False) /\ (forall m : N, forall n : N, ((BIT1 m) = (BIT1 n)) = (m = n)))))))))).
Axiom thm_ARITH_SUB : (forall m : N, forall n : N, (N.sub (m) (n)) = ((N.sub m n))) /\ (((N.sub N0 N0) = N0) /\ ((forall n : N, (N.sub N0 (BIT0 n)) = N0) /\ ((forall n : N, (N.sub N0 (BIT1 n)) = N0) /\ ((forall n : N, (N.sub (BIT0 n) N0) = (BIT0 n)) /\ ((forall n : N, (N.sub (BIT1 n) N0) = (BIT1 n)) /\ ((forall m : N, forall n : N, (N.sub (BIT0 m) (BIT0 n)) = (BIT0 (N.sub m n))) /\ ((forall m : N, forall n : N, (N.sub (BIT0 m) (BIT1 n)) = (N.pred (BIT0 (N.sub m n)))) /\ ((forall m : N, forall n : N, (N.sub (BIT1 m) (BIT0 n)) = (@COND N (N.le n m) (BIT1 (N.sub m n)) N0)) /\ (forall m : N, forall n : N, (N.sub (BIT1 m) (BIT1 n)) = (BIT0 (N.sub m n))))))))))).
Axiom thm_EXP_2_NE_0 : forall n : N, ~ ((N.pow ((BIT0 (BIT1 N0))) n) = (N0)).
Axiom thm_INJ_INVERSE2 : forall {A B C : Type'}, forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Axiom thm_NUMPAIR : forall x : N, forall y : N, (NUMPAIR x y) = (N.mul (N.pow ((BIT0 (BIT1 N0))) x) (N.add (N.mul ((BIT0 (BIT1 N0))) y) ((BIT1 N0)))).
Axiom thm_NUMPAIR_INJ_LEMMA : forall x1 : N, forall y1 : N, forall x2 : N, forall y2 : N, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) -> x1 = x2.
Axiom thm_NUMPAIR_INJ : forall x1 : N, forall y1 : N, forall x2 : N, forall y2 : N, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Axiom thm_NUMSUM : forall b : Prop, forall x : N, (NUMSUM b x) = (@COND N b (N.succ (N.mul ((BIT0 (BIT1 N0))) x)) (N.mul ((BIT0 (BIT1 N0))) x)).
Axiom thm_NUMSUM_INJ : forall b1 : Prop, forall x1 : N, forall b2 : Prop, forall x2 : N, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Axiom thm_INJN : forall {A : Type'}, forall m : N, (@INJN A m) = (fun n : N => fun a : A => n = m).
Axiom thm_INJN_INJ : forall {A : Type'}, forall n1 : N, forall n2 : N, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Axiom thm_INJA : forall {A : Type'}, forall a : A, (@INJA A a) = (fun n : N => fun b : A => b = a).
Axiom thm_INJA_INJ : forall {A : Type'}, forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Axiom thm_INJF : forall {A : Type'}, forall f : N -> N -> A -> Prop, (@INJF A f) = (fun n : N => f (NUMFST n) (NUMSND n)).
Axiom thm_INJF_INJ : forall {A : Type'}, forall f1 : N -> N -> A -> Prop, forall f2 : N -> N -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Axiom thm_INJP : forall {A : Type'}, forall f1 : N -> A -> Prop, forall f2 : N -> A -> Prop, (@INJP A f1 f2) = (fun n : N => fun a : A => @COND Prop (NUMLEFT n) (f1 (NUMRIGHT n) a) (f2 (NUMRIGHT n) a)).
Axiom thm_INJP_INJ : forall {A : Type'}, forall f1 : N -> A -> Prop, forall f1' : N -> A -> Prop, forall f2 : N -> A -> Prop, forall f2' : N -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Axiom thm_ZCONSTR : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (@ZCONSTR A c i r) = (@INJP A (@INJN A (N.succ c)) (@INJP A (@INJA A i) (@INJF A r))).
Axiom thm_ZBOT : forall {A : Type'}, (@ZBOT A) = (@INJP A (@INJN A (N0)) (@ε (N -> A -> Prop) (fun z : N -> A -> Prop => True))).
Axiom thm_ZCONSTR_ZBOT : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> N -> A -> Prop, ~ ((@ZCONSTR A c i r) = (@ZBOT A)).
Axiom thm_ZRECSPACE_RULES : forall {A : Type'}, (@ZRECSPACE A (@ZBOT A)) /\ (forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (forall n : N, @ZRECSPACE A (r n)) -> @ZRECSPACE A (@ZCONSTR A c i r)).
Axiom thm_ZRECSPACE_CASES : forall {A : Type'}, forall a : N -> A -> Prop, (@ZRECSPACE A a) = ((a = (@ZBOT A)) \/ (exists c : N, exists i : A, exists r : N -> N -> A -> Prop, (a = (@ZCONSTR A c i r)) /\ (forall n : N, @ZRECSPACE A (r n)))).
Axiom thm_ZRECSPACE_INDUCT : forall {A : Type'}, forall ZRECSPACE' : (N -> A -> Prop) -> Prop, ((ZRECSPACE' (@ZBOT A)) /\ (forall c : N, forall i : A, forall r : N -> N -> A -> Prop, (forall n : N, ZRECSPACE' (r n)) -> ZRECSPACE' (@ZCONSTR A c i r))) -> forall a : N -> A -> Prop, (@ZRECSPACE A a) -> ZRECSPACE' a.
Axiom thm_BOTTOM : forall {A : Type'}, (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Axiom thm_CONSTR : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> recspace A, (@CONSTR A c i r) = (@_mk_rec A (@ZCONSTR A c i (fun n : N => @_dest_rec A (r n)))).
Axiom thm_MK_REC_INJ : forall {A : Type'}, forall x : N -> A -> Prop, forall y : N -> A -> Prop, ((@_mk_rec A x) = (@_mk_rec A y)) -> ((@ZRECSPACE A x) /\ (@ZRECSPACE A y)) -> x = y.
Axiom thm_DEST_REC_INJ : forall {A : Type'}, forall x : recspace A, forall y : recspace A, ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Axiom thm_CONSTR_BOT : forall {A : Type'}, forall c : N, forall i : A, forall r : N -> recspace A, ~ ((@CONSTR A c i r) = (@BOTTOM A)).
Axiom thm_CONSTR_INJ : forall {A : Type'}, forall c1 : N, forall i1 : A, forall r1 : N -> recspace A, forall c2 : N, forall i2 : A, forall r2 : N -> recspace A, ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((c1 = c2) /\ ((i1 = i2) /\ (r1 = r2))).
Axiom thm_CONSTR_IND : forall {A : Type'}, forall P : (recspace A) -> Prop, ((P (@BOTTOM A)) /\ (forall c : N, forall i : A, forall r : N -> recspace A, (forall n : N, P (r n)) -> P (@CONSTR A c i r))) -> forall x : recspace A, P x.
Axiom thm_CONSTR_REC : forall {A B : Type'}, forall Fn : N -> A -> (N -> recspace A) -> (N -> B) -> B, exists f : (recspace A) -> B, forall c : N, forall i : A, forall r : N -> recspace A, (f (@CONSTR A c i r)) = (Fn c i r (fun n : N => f (r n))).
Axiom thm_FCONS : forall {A : Type'}, (forall a : A, forall f : N -> A, (@FCONS A a f (N0)) = a) /\ (forall a : A, forall f : N -> A, forall n : N, (@FCONS A a f (N.succ n)) = (f n)).
Axiom thm_FCONS_UNDO : forall {A : Type'}, forall f : N -> A, f = (@FCONS A (f (N0)) (@o N N A f N.succ)).
Axiom thm_FNIL : forall {A : Type'}, forall n : N, (@FNIL A n) = (@ε A (fun x : A => True)).
Axiom thm_sum_INDUCT : forall {A B : Type'}, forall P : (Datatypes.sum A B) -> Prop, ((forall a : A, P (@inl A B a)) /\ (forall a : B, P (@inr A B a))) -> forall x : Datatypes.sum A B, P x.
Axiom thm_sum_RECURSION : forall {A B Z' : Type'}, forall INL' : A -> Z', forall INR' : B -> Z', exists fn : (Datatypes.sum A B) -> Z', (forall a : A, (fn (@inl A B a)) = (INL' a)) /\ (forall a : B, (fn (@inr A B a)) = (INR' a)).
Axiom thm_OUTL : forall {A B : Type'} (x : A), (@OUTL A B (@inl A B x)) = x.
Axiom thm_OUTR : forall {A B : Type'} (y : B), (@OUTR A B (@inr A B y)) = y.
Axiom thm_option_INDUCT : forall {A : Type'}, forall P : (option A) -> Prop, ((P (@None A)) /\ (forall a : A, P (@Some A a))) -> forall x : option A, P x.
Axiom thm_option_RECURSION : forall {A Z' : Type'}, forall NONE' : Z', forall SOME' : A -> Z', exists fn : (option A) -> Z', ((fn (@None A)) = NONE') /\ (forall a : A, (fn (@Some A a)) = (SOME' a)).
Axiom thm_list_INDUCT : forall {A : Type'}, forall P : (list A) -> Prop, ((P (@nil A)) /\ (forall a0 : A, forall a1 : list A, (P a1) -> P (@cons A a0 a1))) -> forall x : list A, P x.
Axiom thm_list_RECURSION : forall {A Z' : Type'}, forall NIL' : Z', forall CONS' : A -> (list A) -> Z' -> Z', exists fn : (list A) -> Z', ((fn (@nil A)) = NIL') /\ (forall a0 : A, forall a1 : list A, (fn (@cons A a0 a1)) = (CONS' a0 a1 (fn a1))).
Axiom thm_FORALL_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (forall x : option A, P x) = ((P (@None A)) /\ (forall a : A, P (@Some A a))).
Axiom thm_EXISTS_OPTION_THM : forall {A : Type'}, forall P : (option A) -> Prop, (exists x : option A, P x) = ((P (@None A)) \/ (exists a : A, P (@Some A a))).
Axiom thm_option_DISTINCT : forall {A : Type'}, forall a : A, ~ ((@Some A a) = (@None A)).
Axiom thm_option_INJ : forall {A : Type'}, forall a : A, forall b : A, ((@Some A a) = (@Some A b)) = (a = b).
Axiom thm_ISO : forall {A B : Type'}, forall g : B -> A, forall f : A -> B, (@ExtensionalityFacts.is_inverse A B f g) = ((forall x : B, (f (g x)) = x) /\ (forall y : A, (g (f y)) = y)).
Axiom thm_ISO_REFL : forall {A : Type'}, @ExtensionalityFacts.is_inverse A A (fun x : A => x) (fun x : A => x).
Axiom thm_ISO_FUN : forall {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A'), ((@ExtensionalityFacts.is_inverse A A' f f') /\ (@ExtensionalityFacts.is_inverse B B' g g')) -> @ExtensionalityFacts.is_inverse (A -> B) (A' -> B') (fun h : A -> B => fun a' : A' => g (h (f' a'))) (fun h : A' -> B' => fun a : A => g' (h (f a))).
Axiom thm_ISO_USAGE : forall {A B : Type'} (g : B -> A) (f : A -> B), (@ExtensionalityFacts.is_inverse A B f g) -> (forall P : A -> Prop, (forall x : A, P x) = (forall x : B, P (g x))) /\ ((forall P : A -> Prop, (exists x : A, P x) = (exists x : B, P (g x))) /\ (forall a : A, forall b : B, (a = (g b)) = ((f a) = b))).
Axiom thm_HD : forall {A : Type'} (t : list A) (h : A), (@hd A (@cons A h t)) = h.
Axiom thm_TL : forall {A : Type'} (h : A) (t : list A), (@tl A (@cons A h t)) = t.
Axiom thm_APPEND : forall {A : Type'}, (forall l : list A, (@app A (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (@app A (@cons A h t) l) = (@cons A h (@app A t l))).
Axiom thm_REVERSE : forall {A : Type'} (l : list A) (x : A), ((@List.rev A (@nil A)) = (@nil A)) /\ ((@List.rev A (@cons A x l)) = (@app A (@List.rev A l) (@cons A x (@nil A)))).
Axiom thm_LENGTH : forall {A : Type'}, ((@LENGTH A (@nil A)) = (N0)) /\ (forall h : A, forall t : list A, (@LENGTH A (@cons A h t)) = (N.succ (@LENGTH A t))).
Axiom thm_MAP : forall {A B : Type'}, (forall f : A -> B, (@List.map A B f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (@List.map A B f (@cons A h t)) = (@cons B (f h) (@List.map A B f t))).
Axiom thm_LAST : forall {A : Type'} (h : A) (t : list A), (@LAST A (@cons A h t)) = (@COND A (t = (@nil A)) h (@LAST A t)).
Axiom thm_BUTLAST : forall {A : Type'} (h : A) (t : list A), ((@List.removelast A (@nil A)) = (@nil A)) /\ ((@List.removelast A (@cons A h t)) = (@COND (list A) (t = (@nil A)) (@nil A) (@cons A h (@List.removelast A t)))).
Axiom thm_REPLICATE : forall {A : Type'} (n : N) (x : A), ((@REPLICATE A (N0) x) = (@nil A)) /\ ((@REPLICATE A (N.succ n) x) = (@cons A x (@REPLICATE A n x))).
Axiom thm_NULL : forall {A : Type'} (h : A) (t : list A), ((@NULL A (@nil A)) = True) /\ ((@NULL A (@cons A h t)) = False).
Axiom thm_ALL : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@List.Forall A P (@nil A)) = True) /\ ((@List.Forall A P (@cons A h t)) = ((P h) /\ (@List.Forall A P t))).
Axiom thm_EX : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@EX A P (@nil A)) = False) /\ ((@EX A P (@cons A h t)) = ((P h) \/ (@EX A P t))).
Axiom thm_ITLIST : forall {A B : Type'} (h : A) (f : A -> B -> B) (t : list A) (b : B), ((@ITLIST A B f (@nil A) b) = b) /\ ((@ITLIST A B f (@cons A h t) b) = (f h (@ITLIST A B f t b))).
Axiom thm_MEM : forall {A : Type'} (h : A) (x : A) (t : list A), ((@List.In A x (@nil A)) = False) /\ ((@List.In A x (@cons A h t)) = ((x = h) \/ (@List.In A x t))).
Axiom thm_ALL2_DEF : forall {A B : Type'} (h1' : A) (P : A -> B -> Prop) (t1 : list A) (l2 : list B), ((@ALL2 A B P (@nil A) l2) = (l2 = (@nil B))) /\ ((@ALL2 A B P (@cons A h1' t1) l2) = (@COND Prop (l2 = (@nil B)) False ((P h1' (@hd B l2)) /\ (@ALL2 A B P t1 (@tl B l2))))).
Axiom thm_ALL2 : forall {A B : Type'} (h1' : A) (h2' : B) (P : A -> B -> Prop) (t1 : list A) (t2 : list B), ((@ALL2 A B P (@nil A) (@nil B)) = True) /\ (((@ALL2 A B P (@cons A h1' t1) (@nil B)) = False) /\ (((@ALL2 A B P (@nil A) (@cons B h2' t2)) = False) /\ ((@ALL2 A B P (@cons A h1' t1) (@cons B h2' t2)) = ((P h1' h2') /\ (@ALL2 A B P t1 t2))))).
Axiom thm_MAP2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C) (t1 : list A) (l : list B), ((@MAP2 A B C f (@nil A) l) = (@nil C)) /\ ((@MAP2 A B C f (@cons A h1' t1) l) = (@cons C (f h1' (@hd B l)) (@MAP2 A B C f t1 (@tl B l)))).
Axiom thm_MAP2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C) (t1 : list A) (t2 : list B), ((@MAP2 A B C f (@nil A) (@nil B)) = (@nil C)) /\ ((@MAP2 A B C f (@cons A h1' t1) (@cons B h2' t2)) = (@cons C (f h1' h2') (@MAP2 A B C f t1 t2))).
Axiom thm_EL : forall {A : Type'} (n : N) (l : list A), ((@EL A (N0) l) = (@hd A l)) /\ ((@EL A (N.succ n) l) = (@EL A n (@tl A l))).
Axiom thm_FILTER : forall {A : Type'} (h : A) (P : A -> Prop) (t : list A), ((@FILTER A P (@nil A)) = (@nil A)) /\ ((@FILTER A P (@cons A h t)) = (@COND (list A) (P h) (@cons A h (@FILTER A P t)) (@FILTER A P t))).
Axiom thm_ASSOC : forall {A B : Type'} (h : prod A B) (a : A) (t : list (prod A B)), (@ASSOC A B a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (@ASSOC A B a t)).
Axiom thm_ITLIST2_DEF : forall {A B C : Type'} (h1' : A) (f : A -> B -> C -> C) (t1 : list A) (l2 : list B) (b : C), ((@ITLIST2 A B C f (@nil A) l2 b) = b) /\ ((@ITLIST2 A B C f (@cons A h1' t1) l2 b) = (f h1' (@hd B l2) (@ITLIST2 A B C f t1 (@tl B l2) b))).
Axiom thm_ITLIST2 : forall {A B C : Type'} (h1' : A) (h2' : B) (f : A -> B -> C -> C) (t1 : list A) (t2 : list B) (b : C), ((@ITLIST2 A B C f (@nil A) (@nil B) b) = b) /\ ((@ITLIST2 A B C f (@cons A h1' t1) (@cons B h2' t2) b) = (f h1' h2' (@ITLIST2 A B C f t1 t2 b))).
Axiom thm_ZIP_DEF : forall {A B : Type'} (h1' : A) (t1 : list A) (l2 : list B), ((@ZIP A B (@nil A) l2) = (@nil (prod A B))) /\ ((@ZIP A B (@cons A h1' t1) l2) = (@cons (prod A B) (@pair A B h1' (@hd B l2)) (@ZIP A B t1 (@tl B l2)))).
Axiom thm_ZIP : forall {A B : Type'} (h1' : A) (h2' : B) (t1 : list A) (t2 : list B), ((@ZIP A B (@nil A) (@nil B)) = (@nil (prod A B))) /\ ((@ZIP A B (@cons A h1' t1) (@cons B h2' t2)) = (@cons (prod A B) (@pair A B h1' h2') (@ZIP A B t1 t2))).
Axiom thm_ALLPAIRS : forall {A B : Type'} (h : A) (f : A -> B -> Prop) (t : list A) (l : list B), ((@ALLPAIRS A B f (@nil A) l) = True) /\ ((@ALLPAIRS A B f (@cons A h t) l) = ((@List.Forall B (f h) l) /\ (@ALLPAIRS A B f t l))).
Axiom thm_PAIRWISE : forall {A : Type'} (h : A) (r : A -> A -> Prop) (t : list A), ((@List.ForallOrdPairs A r (@nil A)) = True) /\ ((@List.ForallOrdPairs A r (@cons A h t)) = ((@List.Forall A (r h) t) /\ (@List.ForallOrdPairs A r t))).
Axiom thm_list_of_seq : forall {A : Type'} (s : N -> A) (n : N), ((@list_of_seq A s (N0)) = (@nil A)) /\ ((@list_of_seq A s (N.succ n)) = (@app A (@list_of_seq A s n) (@cons A (s n) (@nil A)))).
Axiom thm_NOT_CONS_NIL : forall {A : Type'}, forall h : A, forall t : list A, ~ ((@cons A h t) = (@nil A)).
Axiom thm_LAST_CLAUSES : forall {A : Type'} (h : A) (k : A) (t : list A), ((@LAST A (@cons A h (@nil A))) = h) /\ ((@LAST A (@cons A h (@cons A k t))) = (@LAST A (@cons A k t))).
Axiom thm_APPEND_NIL : forall {A : Type'}, forall l : list A, (@app A l (@nil A)) = l.
Axiom thm_APPEND_ASSOC : forall {A : Type'}, forall l : list A, forall m : list A, forall n : list A, (@app A l (@app A m n)) = (@app A (@app A l m) n).
Axiom thm_REVERSE_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@List.rev A (@app A l m)) = (@app A (@List.rev A m) (@List.rev A l)).
Axiom thm_REVERSE_REVERSE : forall {A : Type'}, forall l : list A, (@List.rev A (@List.rev A l)) = l.
Axiom thm_REVERSE_EQ_EMPTY : forall {A : Type'}, forall l : list A, ((@List.rev A l) = (@nil A)) = (l = (@nil A)).
Axiom thm_CONS_11 : forall {A : Type'}, forall h1' : A, forall h2' : A, forall t1 : list A, forall t2 : list A, ((@cons A h1' t1) = (@cons A h2' t2)) = ((h1' = h2') /\ (t1 = t2)).
Axiom thm_list_CASES : forall {A : Type'}, forall l : list A, (l = (@nil A)) \/ (exists h : A, exists t : list A, l = (@cons A h t)).
Axiom thm_LIST_EQ : forall {A : Type'}, forall l1 : list A, forall l2 : list A, (l1 = l2) = (((@LENGTH A l1) = (@LENGTH A l2)) /\ (forall n : N, (N.lt n (@LENGTH A l2)) -> (@EL A n l1) = (@EL A n l2))).
Axiom thm_LENGTH_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@LENGTH A (@app A l m)) = (N.add (@LENGTH A l) (@LENGTH A m)).
Axiom thm_MAP_APPEND : forall {A B : Type'}, forall f : A -> B, forall l1 : list A, forall l2 : list A, (@List.map A B f (@app A l1 l2)) = (@app B (@List.map A B f l1) (@List.map A B f l2)).
Axiom thm_LENGTH_MAP : forall {A B : Type'}, forall l : list A, forall f : A -> B, (@LENGTH B (@List.map A B f l)) = (@LENGTH A l).
Axiom thm_LENGTH_EQ_NIL : forall {A : Type'}, forall l : list A, ((@LENGTH A l) = (N0)) = (l = (@nil A)).
Axiom thm_LENGTH_EQ_CONS : forall {A : Type'}, forall l : list A, forall n : N, ((@LENGTH A l) = (N.succ n)) = (exists h : A, exists t : list A, (l = (@cons A h t)) /\ ((@LENGTH A t) = n)).
Axiom thm_LENGTH_REVERSE : forall {A : Type'}, forall l : list A, (@LENGTH A (@List.rev A l)) = (@LENGTH A l).
Axiom thm_MAP_o : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall l : list A, (@List.map A C (@o A B C g f) l) = (@List.map B C g (@List.map A B f l)).
Axiom thm_MAP_EQ : forall {A B : Type'}, forall f : A -> B, forall g : A -> B, forall l : list A, (@List.Forall A (fun x : A => (f x) = (g x)) l) -> (@List.map A B f l) = (@List.map A B g l).
Axiom thm_ALL_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((@List.In A x l) /\ (P x)) -> Q x) /\ (@List.Forall A P l)) -> @List.Forall A Q l.
Axiom thm_NOT_EX : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (~ (@EX A P l)) = (@List.Forall A (fun x : A => ~ (P x)) l).
Axiom thm_NOT_ALL : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (~ (@List.Forall A P l)) = (@EX A (fun x : A => ~ (P x)) l).
Axiom thm_ALL_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@List.Forall B P (@List.map A B f l)) = (@List.Forall A (@o A B Prop P f) l).
Axiom thm_ALL_EQ : forall {A : Type'} (R' : A -> Prop) (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((@List.Forall A R' l) /\ (forall x : A, (R' x) -> (P x) = (Q x))) -> (@List.Forall A P l) = (@List.Forall A Q l).
Axiom thm_ALL_T : forall {A : Type'}, forall l : list A, @List.Forall A (fun x : A => True) l.
Axiom thm_MAP_EQ_ALL2 : forall {A B : Type'}, forall f : A -> B, forall l : list A, forall m : list A, (@ALL2 A A (fun x : A => fun y : A => (f x) = (f y)) l m) -> (@List.map A B f l) = (@List.map A B f m).
Axiom thm_ALL2_MAP : forall {A B : Type'}, forall P : B -> A -> Prop, forall f : A -> B, forall l : list A, (@ALL2 B A P (@List.map A B f l) l) = (@List.Forall A (fun a : A => P (f a) a) l).
Axiom thm_MAP_EQ_DEGEN : forall {A : Type'}, forall l : list A, forall f : A -> A, (@List.Forall A (fun x : A => (f x) = x) l) -> (@List.map A A f l) = l.
Axiom thm_ALL2_AND_RIGHT : forall {A B : Type'}, forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : A -> B -> Prop, (@ALL2 A B (fun x : A => fun y : B => (P x) /\ (Q x y)) l m) = ((@List.Forall A P l) /\ (@ALL2 A B Q l m)).
Axiom thm_ITLIST_APPEND : forall {A B : Type'}, forall f : A -> B -> B, forall a : B, forall l1 : list A, forall l2 : list A, (@ITLIST A B f (@app A l1 l2) a) = (@ITLIST A B f l1 (@ITLIST A B f l2 a)).
Axiom thm_ITLIST_EXTRA : forall {A B : Type'} (a : A) (b : B), forall f : A -> B -> B, forall l : list A, (@ITLIST A B f (@app A l (@cons A a (@nil A))) b) = (@ITLIST A B f l (f a b)).
Axiom thm_ALL_MP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((@List.Forall A (fun x : A => (P x) -> Q x) l) /\ (@List.Forall A P l)) -> @List.Forall A Q l.
Axiom thm_AND_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop), forall l : list A, ((@List.Forall A P l) /\ (@List.Forall A Q l)) = (@List.Forall A (fun x : A => (P x) /\ (Q x)) l).
Axiom thm_EX_IMP : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, ((forall x : A, ((@List.In A x l) /\ (P x)) -> Q x) /\ (@EX A P l)) -> @EX A Q l.
Axiom thm_ALL_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (forall x : A, (@List.In A x l) -> P x) = (@List.Forall A P l).
Axiom thm_LENGTH_REPLICATE : forall {A : Type'}, forall n : N, forall x : A, (@LENGTH A (@REPLICATE A n x)) = n.
Axiom thm_MEM_REPLICATE : forall {A : Type'}, forall n : N, forall x : A, forall y : A, (@List.In A x (@REPLICATE A n y)) = ((x = y) /\ (~ (n = (N0)))).
Axiom thm_EX_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@EX B P (@List.map A B f l)) = (@EX A (@o A B Prop P f) l).
Axiom thm_EXISTS_EX : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list B, (exists x : A, @EX B (P x) l) = (@EX B (fun s : B => exists x : A, P x s) l).
Axiom thm_FORALL_ALL : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list B, (forall x : A, @List.Forall B (P x) l) = (@List.Forall B (fun s : B => forall x : A, P x s) l).
Axiom thm_MEM_APPEND : forall {A : Type'}, forall x : A, forall l1 : list A, forall l2 : list A, (@List.In A x (@app A l1 l2)) = ((@List.In A x l1) \/ (@List.In A x l2)).
Axiom thm_MEM_MAP : forall {A B : Type'}, forall f : A -> B, forall y : B, forall l : list A, (@List.In B y (@List.map A B f l)) = (exists x : A, (@List.In A x l) /\ (y = (f x))).
Axiom thm_FILTER_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (@FILTER A P (@app A l1 l2)) = (@app A (@FILTER A P l1) (@FILTER A P l2)).
Axiom thm_FILTER_MAP : forall {A B : Type'}, forall P : B -> Prop, forall f : A -> B, forall l : list A, (@FILTER B P (@List.map A B f l)) = (@List.map A B f (@FILTER A (@o A B Prop P f) l)).
Axiom thm_MEM_FILTER : forall {A : Type'}, forall P : A -> Prop, forall l : list A, forall x : A, (@List.In A x (@FILTER A P l)) = ((P x) /\ (@List.In A x l)).
Axiom thm_EX_MEM : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (exists x : A, (P x) /\ (@List.In A x l)) = (@EX A P l).
Axiom thm_MAP_FST_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@LENGTH A l1) = (@LENGTH B l2)) -> (@List.map (prod A B) A (@fst A B) (@ZIP A B l1 l2)) = l1.
Axiom thm_MAP_SND_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@LENGTH A l1) = (@LENGTH B l2)) -> (@List.map (prod A B) B (@snd A B) (@ZIP A B l1 l2)) = l2.
Axiom thm_LENGTH_ZIP : forall {A B : Type'}, forall l1 : list A, forall l2 : list B, ((@LENGTH A l1) = (@LENGTH B l2)) -> (@LENGTH (prod A B) (@ZIP A B l1 l2)) = (@LENGTH B l2).
Axiom thm_MEM_ASSOC : forall {A B : Type'}, forall l : list (prod A B), forall x : A, (@List.In (prod A B) (@pair A B x (@ASSOC A B x l)) l) = (@List.In A x (@List.map (prod A B) A (@fst A B) l)).
Axiom thm_ALL_APPEND : forall {A : Type'}, forall P : A -> Prop, forall l1 : list A, forall l2 : list A, (@List.Forall A P (@app A l1 l2)) = ((@List.Forall A P l1) /\ (@List.Forall A P l2)).
Axiom thm_MEM_EL : forall {A : Type'}, forall l : list A, forall n : N, (N.lt n (@LENGTH A l)) -> @List.In A (@EL A n l) l.
Axiom thm_MEM_EXISTS_EL : forall {A : Type'}, forall l : list A, forall x : A, (@List.In A x l) = (exists i : N, (N.lt i (@LENGTH A l)) /\ (x = (@EL A i l))).
Axiom thm_ALL_EL : forall {A : Type'}, forall P : A -> Prop, forall l : list A, (forall i : N, (N.lt i (@LENGTH A l)) -> P (@EL A i l)) = (@List.Forall A P l).
Axiom thm_ALL2_MAP2 : forall {A B C D : Type'} (P : B -> D -> Prop), forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (@ALL2 B D P (@List.map A B f l) (@List.map C D g m)) = (@ALL2 A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_AND_ALL2 : forall {A B : Type'}, forall P : A -> B -> Prop, forall Q : A -> B -> Prop, forall l : list A, forall m : list B, ((@ALL2 A B P l m) /\ (@ALL2 A B Q l m)) = (@ALL2 A B (fun x : A => fun y : B => (P x y) /\ (Q x y)) l m).
Axiom thm_ALLPAIRS_SYM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list A, forall m : list B, (@ALLPAIRS A B P l m) = (@ALLPAIRS B A (fun x : B => fun y : A => P y x) m l).
Axiom thm_ALLPAIRS_MEM : forall {A B : Type'}, forall P : A -> B -> Prop, forall l : list A, forall m : list B, (forall x : A, forall y : B, ((@List.In A x l) /\ (@List.In B y m)) -> P x y) = (@ALLPAIRS A B P l m).
Axiom thm_ALLPAIRS_MAP : forall {A B C D : Type'}, forall P : B -> D -> Prop, forall f : A -> B, forall g : C -> D, forall l : list A, forall m : list C, (@ALLPAIRS B D P (@List.map A B f l) (@List.map C D g m)) = (@ALLPAIRS A C (fun x : A => fun y : C => P (f x) (g y)) l m).
Axiom thm_ALLPAIRS_EQ : forall {A B : Type'} (R' : A -> B -> Prop) (R'' : A -> B -> Prop), forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : B -> Prop, ((@List.Forall A P l) /\ ((@List.Forall B Q m) /\ (forall p : A, forall q : B, ((P p) /\ (Q q)) -> (R' p q) = (R'' p q)))) -> (@ALLPAIRS A B R' l m) = (@ALLPAIRS A B R'' l m).
Axiom thm_ALL2_ALL : forall {A : Type'}, forall P : A -> A -> Prop, forall l : list A, (@ALL2 A A P l l) = (@List.Forall A (fun x : A => P x x) l).
Axiom thm_APPEND_EQ_NIL : forall {A : Type'}, forall l : list A, forall m : list A, ((@app A l m) = (@nil A)) = ((l = (@nil A)) /\ (m = (@nil A))).
Axiom thm_APPEND_LCANCEL : forall {A : Type'}, forall l1 : list A, forall l2 : list A, forall l3 : list A, ((@app A l1 l2) = (@app A l1 l3)) = (l2 = l3).
Axiom thm_APPEND_RCANCEL : forall {A : Type'}, forall l1 : list A, forall l2 : list A, forall l3 : list A, ((@app A l1 l3) = (@app A l2 l3)) = (l1 = l2).
Axiom thm_LENGTH_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : list A, forall m : list B, ((@LENGTH A l) = (@LENGTH B m)) -> (@LENGTH C (@MAP2 A B C f l m)) = (@LENGTH B m).
Axiom thm_EL_MAP2 : forall {A B C : Type'}, forall f : A -> B -> C, forall l : list A, forall m : list B, forall k : N, ((N.lt k (@LENGTH A l)) /\ (N.lt k (@LENGTH B m))) -> (@EL C k (@MAP2 A B C f l m)) = (f (@EL A k l) (@EL B k m)).
Axiom thm_MAP_EQ_NIL : forall {A B : Type'}, forall f : A -> B, forall l : list A, ((@List.map A B f l) = (@nil B)) = (l = (@nil A)).
Axiom thm_INJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall l : list A, forall m : list A, ((@List.map A B f l) = (@List.map A B f m)) -> l = m) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
Axiom thm_SURJECTIVE_MAP : forall {A B : Type'}, forall f : A -> B, (forall m : list B, exists l : list A, (@List.map A B f l) = m) = (forall y : B, exists x : A, (f x) = y).
Axiom thm_MAP_ID : forall {A : Type'}, forall l : list A, (@List.map A A (fun x : A => x) l) = l.
Axiom thm_MAP_I : forall {A : Type'}, (@List.map A A (@I A)) = (@I (list A)).
Axiom thm_BUTLAST_CLAUSES : forall {A : Type'}, ((@List.removelast A (@nil A)) = (@nil A)) /\ ((forall a : A, (@List.removelast A (@cons A a (@nil A))) = (@nil A)) /\ (forall a : A, forall h : A, forall t : list A, (@List.removelast A (@cons A a (@cons A h t))) = (@cons A a (@List.removelast A (@cons A h t))))).
Axiom thm_BUTLAST_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@List.removelast A (@app A l m)) = (@COND (list A) (m = (@nil A)) (@List.removelast A l) (@app A l (@List.removelast A m))).
Axiom thm_APPEND_BUTLAST_LAST : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@app A (@List.removelast A l) (@cons A (@LAST A l) (@nil A))) = l.
Axiom thm_LAST_APPEND : forall {A : Type'}, forall p : list A, forall q : list A, (@LAST A (@app A p q)) = (@COND A (q = (@nil A)) (@LAST A p) (@LAST A q)).
Axiom thm_LENGTH_TL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@LENGTH A (@tl A l)) = (N.sub (@LENGTH A l) ((BIT1 N0))).
Axiom thm_LAST_REVERSE : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@LAST A (@List.rev A l)) = (@hd A l).
Axiom thm_HD_REVERSE : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@hd A (@List.rev A l)) = (@LAST A l).
Axiom thm_EL_APPEND : forall {A : Type'}, forall k : N, forall l : list A, forall m : list A, (@EL A k (@app A l m)) = (@COND A (N.lt k (@LENGTH A l)) (@EL A k l) (@EL A (N.sub k (@LENGTH A l)) m)).
Axiom thm_EL_TL : forall {A : Type'} (l : list A), forall n : N, (@EL A n (@tl A l)) = (@EL A (N.add n ((BIT1 N0))) l).
Axiom thm_EL_CONS : forall {A : Type'}, forall n : N, forall h : A, forall t : list A, (@EL A n (@cons A h t)) = (@COND A (n = (N0)) h (@EL A (N.sub n ((BIT1 N0))) t)).
Axiom thm_LAST_EL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@LAST A l) = (@EL A (N.sub (@LENGTH A l) ((BIT1 N0))) l).
Axiom thm_HD_APPEND : forall {A : Type'}, forall l : list A, forall m : list A, (@hd A (@app A l m)) = (@COND A (l = (@nil A)) (@hd A m) (@hd A l)).
Axiom thm_CONS_HD_TL : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> l = (@cons A (@hd A l) (@tl A l)).
Axiom thm_EL_MAP : forall {A B : Type'}, forall f : A -> B, forall n : N, forall l : list A, (N.lt n (@LENGTH A l)) -> (@EL B n (@List.map A B f l)) = (f (@EL A n l)).
Axiom thm_MAP_REVERSE : forall {A B : Type'}, forall f : A -> B, forall l : list A, (@List.rev B (@List.map A B f l)) = (@List.map A B f (@List.rev A l)).
Axiom thm_ALL_FILTER : forall {A : Type'}, forall P : A -> Prop, forall Q : A -> Prop, forall l : list A, (@List.Forall A P (@FILTER A Q l)) = (@List.Forall A (fun x : A => (Q x) -> P x) l).
Axiom thm_APPEND_SING : forall {A : Type'}, forall h : A, forall t : list A, (@app A (@cons A h (@nil A)) t) = (@cons A h t).
Axiom thm_MEM_APPEND_DECOMPOSE_LEFT : forall {A : Type'}, forall x : A, forall l : list A, (@List.In A x l) = (exists l1 : list A, exists l2 : list A, (~ (@List.In A x l1)) /\ (l = (@app A l1 (@cons A x l2)))).
Axiom thm_MEM_APPEND_DECOMPOSE : forall {A : Type'}, forall x : A, forall l : list A, (@List.In A x l) = (exists l1 : list A, exists l2 : list A, l = (@app A l1 (@cons A x l2))).
Axiom thm_PAIRWISE_APPEND : forall {A : Type'}, forall R' : A -> A -> Prop, forall l : list A, forall m : list A, (@List.ForallOrdPairs A R' (@app A l m)) = ((@List.ForallOrdPairs A R' l) /\ ((@List.ForallOrdPairs A R' m) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ (@List.In A y m)) -> R' x y))).
Axiom thm_PAIRWISE_MAP : forall {A B : Type'}, forall R' : B -> B -> Prop, forall f : A -> B, forall l : list A, (@List.ForallOrdPairs B R' (@List.map A B f l)) = (@List.ForallOrdPairs A (fun x : A => fun y : A => R' (f x) (f y)) l).
Axiom thm_PAIRWISE_IMPLIES : forall {A : Type'}, forall R' : A -> A -> Prop, forall R'' : A -> A -> Prop, forall l : list A, ((@List.ForallOrdPairs A R' l) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ ((@List.In A y l) /\ (R' x y))) -> R'' x y)) -> @List.ForallOrdPairs A R'' l.
Axiom thm_PAIRWISE_TRANSITIVE : forall {A : Type'}, forall R' : A -> A -> Prop, forall x : A, forall y : A, forall l : list A, (forall x' : A, forall y' : A, forall z : A, ((R' x' y') /\ (R' y' z)) -> R' x' z) -> (@List.ForallOrdPairs A R' (@cons A x (@cons A y l))) = ((R' x y) /\ (@List.ForallOrdPairs A R' (@cons A y l))).
Axiom thm_LENGTH_LIST_OF_SEQ : forall {A : Type'}, forall s : N -> A, forall n : N, (@LENGTH A (@list_of_seq A s n)) = n.
Axiom thm_EL_LIST_OF_SEQ : forall {A : Type'}, forall s : N -> A, forall m : N, forall n : N, (N.lt m n) -> (@EL A m (@list_of_seq A s n)) = (s m).
Axiom thm_LIST_OF_SEQ_EQ_NIL : forall {A : Type'}, forall s : N -> A, forall n : N, ((@list_of_seq A s n) = (@nil A)) = (n = (N0)).
Axiom thm_MONO_ALL : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A), (forall x : A, (P x) -> Q x) -> (@List.Forall A P l) -> @List.Forall A Q l.
Axiom thm_MONO_ALL2 : forall {A B : Type'} (P : A -> B -> Prop) (Q : A -> B -> Prop) (l : list A) (l' : list B), (forall x : A, forall y : B, (P x y) -> Q x y) -> (@ALL2 A B P l l') -> @ALL2 A B Q l l'.
Axiom thm_char_INDUCT : forall P : Ascii.ascii -> Prop, (forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, P (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) -> forall x : Ascii.ascii, P x.
Axiom thm_char_RECURSION : forall {Z' : Type'}, forall f : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Z', exists fn : Ascii.ascii -> Z', forall a0 : Prop, forall a1 : Prop, forall a2 : Prop, forall a3 : Prop, forall a4 : Prop, forall a5 : Prop, forall a6 : Prop, forall a7 : Prop, (fn (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) = (f a0 a1 a2 a3 a4 a5 a6 a7).
Axiom thm_dist : forall n : N, forall m : N, (dist (@pair N N m n)) = (N.add (N.sub m n) (N.sub n m)).
Axiom thm_DIST_REFL : forall n : N, (dist (@pair N N n n)) = (N0).
Axiom thm_DIST_LZERO : forall n : N, (dist (@pair N N (N0) n)) = n.
Axiom thm_DIST_RZERO : forall n : N, (dist (@pair N N n (N0))) = n.
Axiom thm_DIST_SYM : forall m : N, forall n : N, (dist (@pair N N m n)) = (dist (@pair N N n m)).
Axiom thm_DIST_LADD : forall m : N, forall p : N, forall n : N, (dist (@pair N N (N.add m n) (N.add m p))) = (dist (@pair N N n p)).
Axiom thm_DIST_RADD : forall m : N, forall p : N, forall n : N, (dist (@pair N N (N.add m p) (N.add n p))) = (dist (@pair N N m n)).
Axiom thm_DIST_LADD_0 : forall m : N, forall n : N, (dist (@pair N N (N.add m n) m)) = n.
Axiom thm_DIST_RADD_0 : forall m : N, forall n : N, (dist (@pair N N m (N.add m n))) = n.
Axiom thm_DIST_LMUL : forall m : N, forall n : N, forall p : N, (N.mul m (dist (@pair N N n p))) = (dist (@pair N N (N.mul m n) (N.mul m p))).
Axiom thm_DIST_RMUL : forall m : N, forall n : N, forall p : N, (N.mul (dist (@pair N N m n)) p) = (dist (@pair N N (N.mul m p) (N.mul n p))).
Axiom thm_DIST_EQ_0 : forall m : N, forall n : N, ((dist (@pair N N m n)) = (N0)) = (m = n).
Axiom thm_DIST_ELIM_THM : forall (y : N) (x : N) (P : N -> Prop), (P (dist (@pair N N x y))) = (forall d : N, ((x = (N.add y d)) -> P d) /\ ((y = (N.add x d)) -> P d)).
Axiom thm_DIST_TRIANGLE_LE : forall m : N, forall n : N, forall p : N, forall q : N, (N.le (N.add (dist (@pair N N m n)) (dist (@pair N N n p))) q) -> N.le (dist (@pair N N m p)) q.
Axiom thm_DIST_TRIANGLES_LE : forall m : N, forall n : N, forall p : N, forall q : N, forall r : N, forall s : N, ((N.le (dist (@pair N N m n)) r) /\ (N.le (dist (@pair N N p q)) s)) -> N.le (dist (@pair N N m p)) (N.add (dist (@pair N N n q)) (N.add r s)).
Axiom thm_BOUNDS_LINEAR : forall A : N, forall B : N, forall C : N, (forall n : N, N.le (N.mul A n) (N.add (N.mul B n) C)) = (N.le A B).
Axiom thm_BOUNDS_LINEAR_0 : forall A : N, forall B : N, (forall n : N, N.le (N.mul A n) B) = (A = (N0)).
Axiom thm_BOUNDS_DIVIDED : forall P : N -> N, (exists B : N, forall n : N, N.le (P n) B) = (exists A : N, exists B : N, forall n : N, N.le (N.mul n (P n)) (N.add (N.mul A n) B)).
Axiom thm_BOUNDS_NOTZERO : forall P : N -> N -> N, forall A : N, forall B : N, (((P (N0) (N0)) = (N0)) /\ (forall m : N, forall n : N, N.le (P m n) (N.add (N.mul A (N.add m n)) B))) -> exists B' : N, forall m : N, forall n : N, N.le (P m n) (N.mul B' (N.add m n)).
Axiom thm_BOUNDS_IGNORE : forall P : N -> N, forall Q : N -> N, (exists B : N, forall i : N, N.le (P i) (N.add (Q i) B)) = (exists B : N, exists N' : N, forall i : N, (N.le N' i) -> N.le (P i) (N.add (Q i) B)).
Axiom thm_is_nadd : forall x : N -> N, (is_nadd x) = (exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (x n)) (N.mul n (x m)))) (N.mul B (N.add m n))).
Axiom thm_is_nadd_0 : is_nadd (fun n : N => N0).
Axiom thm_NADD_CAUCHY : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (dest_nadd x n)) (N.mul n (dest_nadd x m)))) (N.mul B (N.add m n)).
Axiom thm_NADD_BOUND : forall x : nadd, exists A : N, exists B : N, forall n : N, N.le (dest_nadd x n) (N.add (N.mul A n) B).
Axiom thm_NADD_MULTIPLICATIVE : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.mul m n)) (N.mul m (dest_nadd x n)))) (N.add (N.mul B m) B).
Axiom thm_NADD_ADDITIVE : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.add m n)) (N.add (dest_nadd x m) (dest_nadd x n)))) B.
Axiom thm_NADD_SUC : forall x : nadd, exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.succ n)) (dest_nadd x n))) B.
Axiom thm_NADD_DIST_LEMMA : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x (N.add m n)) (dest_nadd x m))) (N.mul B n).
Axiom thm_NADD_DIST : forall x : nadd, exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (dest_nadd x m) (dest_nadd x n))) (N.mul B (dist (@pair N N m n))).
Axiom thm_NADD_ALTMUL : forall x : nadd, forall y : nadd, exists A : N, exists B : N, forall n : N, N.le (dist (@pair N N (N.mul n (dest_nadd x (dest_nadd y n))) (N.mul (dest_nadd x n) (dest_nadd y n)))) (N.add (N.mul A n) B).
Axiom thm_nadd_eq : forall x : nadd, forall y : nadd, (nadd_eq x y) = (exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd x n) (dest_nadd y n))) B).
Axiom thm_NADD_EQ_REFL : forall x : nadd, nadd_eq x x.
Axiom thm_NADD_EQ_SYM : forall x : nadd, forall y : nadd, (nadd_eq x y) = (nadd_eq y x).
Axiom thm_NADD_EQ_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_eq x y) /\ (nadd_eq y z)) -> nadd_eq x z.
Axiom thm_nadd_of_num : forall k : N, (nadd_of_num k) = (mk_nadd (fun n : N => N.mul k n)).
Axiom thm_NADD_OF_NUM : forall k : N, (dest_nadd (nadd_of_num k)) = (fun n : N => N.mul k n).
Axiom thm_NADD_OF_NUM_WELLDEF : forall m : N, forall n : N, (m = n) -> nadd_eq (nadd_of_num m) (nadd_of_num n).
Axiom thm_NADD_OF_NUM_EQ : forall m : N, forall n : N, (nadd_eq (nadd_of_num m) (nadd_of_num n)) = (m = n).
Axiom thm_nadd_le : forall x : nadd, forall y : nadd, (nadd_le x y) = (exists B : N, forall n : N, N.le (dest_nadd x n) (N.add (dest_nadd y n) B)).
Axiom thm_NADD_LE_WELLDEF_LEMMA : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ ((nadd_eq y y') /\ (nadd_le x y))) -> nadd_le x' y'.
Axiom thm_NADD_LE_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> (nadd_le x y) = (nadd_le x' y').
Axiom thm_NADD_LE_REFL : forall x : nadd, nadd_le x x.
Axiom thm_NADD_LE_TRANS : forall x : nadd, forall y : nadd, forall z : nadd, ((nadd_le x y) /\ (nadd_le y z)) -> nadd_le x z.
Axiom thm_NADD_LE_ANTISYM : forall x : nadd, forall y : nadd, ((nadd_le x y) /\ (nadd_le y x)) = (nadd_eq x y).
Axiom thm_NADD_LE_TOTAL_LEMMA : forall x : nadd, forall y : nadd, (~ (nadd_le x y)) -> forall B : N, exists n : N, (~ (n = (N0))) /\ (N.lt (N.add (dest_nadd y n) B) (dest_nadd x n)).
Axiom thm_NADD_LE_TOTAL : forall x : nadd, forall y : nadd, (nadd_le x y) \/ (nadd_le y x).
Axiom thm_NADD_ARCH : forall x : nadd, exists n : N, nadd_le x (nadd_of_num n).
Axiom thm_NADD_OF_NUM_LE : forall m : N, forall n : N, (nadd_le (nadd_of_num m) (nadd_of_num n)) = (N.le m n).
Axiom thm_nadd_add : forall x : nadd, forall y : nadd, (nadd_add x y) = (mk_nadd (fun n : N => N.add (dest_nadd x n) (dest_nadd y n))).
Axiom thm_NADD_ADD : forall x : nadd, forall y : nadd, (dest_nadd (nadd_add x y)) = (fun n : N => N.add (dest_nadd x n) (dest_nadd y n)).
Axiom thm_NADD_ADD_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_add x y) (nadd_add x' y').
Axiom thm_NADD_ADD_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_add x y) (nadd_add y x).
Axiom thm_NADD_ADD_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z).
Axiom thm_NADD_ADD_LID : forall x : nadd, nadd_eq (nadd_add (nadd_of_num (N0)) x) x.
Axiom thm_NADD_ADD_LCANCEL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_eq (nadd_add x y) (nadd_add x z)) -> nadd_eq y z.
Axiom thm_NADD_LE_ADD : forall x : nadd, forall y : nadd, nadd_le x (nadd_add x y).
Axiom thm_NADD_LE_EXISTS : forall x : nadd, forall y : nadd, (nadd_le x y) -> exists d : nadd, nadd_eq y (nadd_add x d).
Axiom thm_NADD_OF_NUM_ADD : forall m : N, forall n : N, nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (N.add m n)).
Axiom thm_nadd_mul : forall x : nadd, forall y : nadd, (nadd_mul x y) = (mk_nadd (fun n : N => dest_nadd x (dest_nadd y n))).
Axiom thm_NADD_MUL : forall x : nadd, forall y : nadd, (dest_nadd (nadd_mul x y)) = (fun n : N => dest_nadd x (dest_nadd y n)).
Axiom thm_NADD_MUL_SYM : forall x : nadd, forall y : nadd, nadd_eq (nadd_mul x y) (nadd_mul y x).
Axiom thm_NADD_MUL_ASSOC : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z).
Axiom thm_NADD_MUL_LID : forall x : nadd, nadd_eq (nadd_mul (nadd_of_num ((BIT1 N0))) x) x.
Axiom thm_NADD_LDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z)).
Axiom thm_NADD_MUL_WELLDEF_LEMMA : forall x : nadd, forall y : nadd, forall y' : nadd, (nadd_eq y y') -> nadd_eq (nadd_mul x y) (nadd_mul x y').
Axiom thm_NADD_MUL_WELLDEF : forall x : nadd, forall x' : nadd, forall y : nadd, forall y' : nadd, ((nadd_eq x x') /\ (nadd_eq y y')) -> nadd_eq (nadd_mul x y) (nadd_mul x' y').
Axiom thm_NADD_OF_NUM_MUL : forall m : N, forall n : N, nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (N.mul m n)).
Axiom thm_NADD_LE_0 : forall x : nadd, nadd_le (nadd_of_num (N0)) x.
Axiom thm_NADD_EQ_IMP_LE : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_le x y.
Axiom thm_NADD_LE_LMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le y z) -> nadd_le (nadd_mul x y) (nadd_mul x z).
Axiom thm_NADD_LE_RMUL : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le x y) -> nadd_le (nadd_mul x z) (nadd_mul y z).
Axiom thm_NADD_LE_RADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x z) (nadd_add y z)) = (nadd_le x y).
Axiom thm_NADD_LE_LADD : forall x : nadd, forall y : nadd, forall z : nadd, (nadd_le (nadd_add x y) (nadd_add x z)) = (nadd_le y z).
Axiom thm_NADD_RDISTRIB : forall x : nadd, forall y : nadd, forall z : nadd, nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)).
Axiom thm_NADD_ARCH_MULT : forall x : nadd, forall k : N, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists N' : N, nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N') x).
Axiom thm_NADD_ARCH_ZERO : forall x : nadd, forall k : nadd, (forall n : N, nadd_le (nadd_mul (nadd_of_num n) x) k) -> nadd_eq x (nadd_of_num (N0)).
Axiom thm_NADD_ARCH_LEMMA : forall x : nadd, forall y : nadd, forall z : nadd, (forall n : N, nadd_le (nadd_mul (nadd_of_num n) x) (nadd_add (nadd_mul (nadd_of_num n) y) z)) -> nadd_le x y.
Axiom thm_NADD_COMPLETE : forall P : nadd -> Prop, ((exists x : nadd, P x) /\ (exists M : nadd, forall x : nadd, (P x) -> nadd_le x M)) -> exists M : nadd, (forall x : nadd, (P x) -> nadd_le x M) /\ (forall M' : nadd, (forall x : nadd, (P x) -> nadd_le x M') -> nadd_le M M').
Axiom thm_NADD_UBOUND : forall x : nadd, exists B : N, exists N' : N, forall n : N, (N.le N' n) -> N.le (dest_nadd x n) (N.mul B n).
Axiom thm_NADD_NONZERO : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists N' : N, forall n : N, (N.le N' n) -> ~ ((dest_nadd x n) = (N0)).
Axiom thm_NADD_LBOUND : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists A : N, exists N' : N, forall n : N, (N.le N' n) -> N.le n (N.mul A (dest_nadd x n)).
Axiom thm_nadd_rinv : forall x : nadd, (nadd_rinv x) = (fun n : N => N.div (N.mul n n) (dest_nadd x n)).
Axiom thm_NADD_MUL_LINV_LEMMA0 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists A : N, exists B : N, forall n : N, N.le (nadd_rinv x n) (N.add (N.mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA1 : forall x : nadd, forall n : N, (~ ((dest_nadd x n) = (N0))) -> N.le (dist (@pair N N (N.mul (dest_nadd x n) (nadd_rinv x n)) (N.mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA2 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists N' : N, forall n : N, (N.le N' n) -> N.le (dist (@pair N N (N.mul (dest_nadd x n) (nadd_rinv x n)) (N.mul n n))) (dest_nadd x n).
Axiom thm_NADD_MUL_LINV_LEMMA3 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists N' : N, forall m : N, forall n : N, (N.le N' n) -> N.le (dist (@pair N N (N.mul m (N.mul (dest_nadd x m) (N.mul (dest_nadd x n) (nadd_rinv x n)))) (N.mul m (N.mul (dest_nadd x m) (N.mul n n))))) (N.mul m (N.mul (dest_nadd x m) (dest_nadd x n))).
Axiom thm_NADD_MUL_LINV_LEMMA4 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.add (N.mul (N.mul m n) (dist (@pair N N (N.mul m (dest_nadd x n)) (N.mul n (dest_nadd x m))))) (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA5 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.mul B (N.mul (N.mul m n) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA6 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (N.mul (N.mul m n) (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m))))) (N.mul B (N.mul (N.mul m n) (N.add m n))).
Axiom thm_NADD_MUL_LINV_LEMMA7 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists B : N, exists N' : N, forall m : N, forall n : N, ((N.le N' m) /\ (N.le N' n)) -> N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.mul B (N.add m n)).
Axiom thm_NADD_MUL_LINV_LEMMA7a : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> forall N' : N, exists A : N, exists B : N, forall m : N, forall n : N, (N.le m N') -> N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.add (N.mul A n) B).
Axiom thm_NADD_MUL_LINV_LEMMA8 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (nadd_rinv x n)) (N.mul n (nadd_rinv x m)))) (N.mul B (N.add m n)).
Axiom thm_nadd_inv : forall x : nadd, (nadd_inv x) = (@COND nadd (nadd_eq x (nadd_of_num (N0))) (nadd_of_num (N0)) (mk_nadd (nadd_rinv x))).
Axiom thm_NADD_INV : forall x : nadd, (dest_nadd (nadd_inv x)) = (@COND (N -> N) (nadd_eq x (nadd_of_num (N0))) (fun n : N => N0) (nadd_rinv x)).
Axiom thm_NADD_MUL_LINV : forall x : nadd, (~ (nadd_eq x (nadd_of_num (N0)))) -> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num ((BIT1 N0))).
Axiom thm_NADD_INV_0 : nadd_eq (nadd_inv (nadd_of_num (N0))) (nadd_of_num (N0)).
Axiom thm_NADD_INV_WELLDEF : forall x : nadd, forall y : nadd, (nadd_eq x y) -> nadd_eq (nadd_inv x) (nadd_inv y).
Axiom thm_HREAL_OF_NUM_EQ : forall m : N, forall n : N, ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
Axiom thm_HREAL_OF_NUM_LE : forall m : N, forall n : N, (hreal_le (hreal_of_num m) (hreal_of_num n)) = (N.le m n).
Axiom thm_HREAL_OF_NUM_ADD : forall m : N, forall n : N, (hreal_add (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (N.add m n)).
Axiom thm_HREAL_OF_NUM_MUL : forall m : N, forall n : N, (hreal_mul (hreal_of_num m) (hreal_of_num n)) = (hreal_of_num (N.mul m n)).
Axiom thm_HREAL_LE_REFL : forall x : hreal, hreal_le x x.
Axiom thm_HREAL_LE_TRANS : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_le x y) /\ (hreal_le y z)) -> hreal_le x z.
Axiom thm_HREAL_LE_ANTISYM : forall x : hreal, forall y : hreal, ((hreal_le x y) /\ (hreal_le y x)) = (x = y).
Axiom thm_HREAL_LE_TOTAL : forall x : hreal, forall y : hreal, (hreal_le x y) \/ (hreal_le y x).
Axiom thm_HREAL_LE_ADD : forall x : hreal, forall y : hreal, hreal_le x (hreal_add x y).
Axiom thm_HREAL_LE_EXISTS : forall x : hreal, forall y : hreal, (hreal_le x y) -> exists d : hreal, y = (hreal_add x d).
Axiom thm_HREAL_ARCH : forall x : hreal, exists n : N, hreal_le x (hreal_of_num n).
Axiom thm_HREAL_ADD_SYM : forall x : hreal, forall y : hreal, (hreal_add x y) = (hreal_add y x).
Axiom thm_HREAL_ADD_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_add x (hreal_add y z)) = (hreal_add (hreal_add x y) z).
Axiom thm_HREAL_ADD_LID : forall x : hreal, (hreal_add (hreal_of_num (N0)) x) = x.
Axiom thm_HREAL_ADD_LCANCEL : forall x : hreal, forall y : hreal, forall z : hreal, ((hreal_add x y) = (hreal_add x z)) -> y = z.
Axiom thm_HREAL_MUL_SYM : forall x : hreal, forall y : hreal, (hreal_mul x y) = (hreal_mul y x).
Axiom thm_HREAL_MUL_ASSOC : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_mul y z)) = (hreal_mul (hreal_mul x y) z).
Axiom thm_HREAL_MUL_LID : forall x : hreal, (hreal_mul (hreal_of_num ((BIT1 N0))) x) = x.
Axiom thm_HREAL_ADD_LDISTRIB : forall x : hreal, forall y : hreal, forall z : hreal, (hreal_mul x (hreal_add y z)) = (hreal_add (hreal_mul x y) (hreal_mul x z)).
Axiom thm_HREAL_MUL_LINV : forall x : hreal, (~ (x = (hreal_of_num (N0)))) -> (hreal_mul (hreal_inv x) x) = (hreal_of_num ((BIT1 N0))).
Axiom thm_HREAL_INV_0 : (hreal_inv (hreal_of_num (N0))) = (hreal_of_num (N0)).
Axiom thm_HREAL_LE_EXISTS_DEF : forall m : hreal, forall n : hreal, (hreal_le m n) = (exists d : hreal, n = (hreal_add m d)).
Axiom thm_HREAL_EQ_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m n) = (hreal_add m p)) = (n = p).
Axiom thm_HREAL_EQ_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, ((hreal_add m p) = (hreal_add n p)) = (m = n).
Axiom thm_HREAL_LE_ADD_LCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m n) (hreal_add m p)) = (hreal_le n p).
Axiom thm_HREAL_LE_ADD_RCANCEL : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_le (hreal_add m p) (hreal_add n p)) = (hreal_le m n).
Axiom thm_HREAL_ADD_RID : forall n : hreal, (hreal_add n (hreal_of_num (N0))) = n.
Axiom thm_HREAL_ADD_RDISTRIB : forall m : hreal, forall n : hreal, forall p : hreal, (hreal_mul (hreal_add m n) p) = (hreal_add (hreal_mul m p) (hreal_mul n p)).
Axiom thm_HREAL_MUL_LZERO : forall m : hreal, (hreal_mul (hreal_of_num (N0)) m) = (hreal_of_num (N0)).
Axiom thm_HREAL_MUL_RZERO : forall m : hreal, (hreal_mul m (hreal_of_num (N0))) = (hreal_of_num (N0)).
Axiom thm_HREAL_ADD_AC : forall (n : hreal) (m : hreal) (p : hreal), ((hreal_add m n) = (hreal_add n m)) /\ (((hreal_add (hreal_add m n) p) = (hreal_add m (hreal_add n p))) /\ ((hreal_add m (hreal_add n p)) = (hreal_add n (hreal_add m p)))).
Axiom thm_HREAL_LE_ADD2 : forall a : hreal, forall b : hreal, forall c : hreal, forall d : hreal, ((hreal_le a b) /\ (hreal_le c d)) -> hreal_le (hreal_add a c) (hreal_add b d).
Axiom thm_HREAL_LE_MUL_RCANCEL_IMP : forall a : hreal, forall b : hreal, forall c : hreal, (hreal_le a b) -> hreal_le (hreal_mul a c) (hreal_mul b c).
Axiom thm_treal_of_num : forall n : N, (treal_of_num n) = (@pair hreal hreal (hreal_of_num n) (hreal_of_num (N0))).
Axiom thm_treal_neg : forall y : hreal, forall x : hreal, (treal_neg (@pair hreal hreal x y)) = (@pair hreal hreal y x).
Axiom thm_treal_add : forall x1 : hreal, forall x2 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_add (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add x1 x2) (hreal_add y1 y2)).
Axiom thm_treal_mul : forall x1 : hreal, forall y2 : hreal, forall y1 : hreal, forall x2 : hreal, (treal_mul (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (@pair hreal hreal (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2)) (hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))).
Axiom thm_treal_le : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = (hreal_le (hreal_add x1 y2) (hreal_add x2 y1)).
Axiom thm_treal_inv : forall y : hreal, forall x : hreal, (treal_inv (@pair hreal hreal x y)) = (@COND (prod hreal hreal) (x = y) (@pair hreal hreal (hreal_of_num (N0)) (hreal_of_num (N0))) (@COND (prod hreal hreal) (hreal_le y x) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => x = (hreal_add y d)))) (hreal_of_num (N0))) (@pair hreal hreal (hreal_of_num (N0)) (hreal_inv (@ε hreal (fun d : hreal => y = (hreal_add x d))))))).
Axiom thm_treal_eq : forall x1 : hreal, forall y2 : hreal, forall x2 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Axiom thm_TREAL_EQ_REFL : forall x : prod hreal hreal, treal_eq x x.
Axiom thm_TREAL_EQ_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) = (treal_eq y x).
Axiom thm_TREAL_EQ_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_eq x y) /\ (treal_eq y z)) -> treal_eq x z.
Axiom thm_TREAL_EQ_AP : forall x : prod hreal hreal, forall y : prod hreal hreal, (x = y) -> treal_eq x y.
Axiom thm_TREAL_OF_NUM_EQ : forall m : N, forall n : N, (treal_eq (treal_of_num m) (treal_of_num n)) = (m = n).
Axiom thm_TREAL_OF_NUM_LE : forall m : N, forall n : N, (treal_le (treal_of_num m) (treal_of_num n)) = (N.le m n).
Axiom thm_TREAL_OF_NUM_ADD : forall m : N, forall n : N, treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (N.add m n)).
Axiom thm_TREAL_OF_NUM_MUL : forall m : N, forall n : N, treal_eq (treal_mul (treal_of_num m) (treal_of_num n)) (treal_of_num (N.mul m n)).
Axiom thm_TREAL_ADD_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_add x y) = (treal_add y x).
Axiom thm_TREAL_MUL_SYM_EQ : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_mul x y) = (treal_mul y x).
Axiom thm_TREAL_ADD_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_add x y) (treal_add y x).
Axiom thm_TREAL_ADD_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z).
Axiom thm_TREAL_ADD_LID : forall x : prod hreal hreal, treal_eq (treal_add (treal_of_num (N0)) x) x.
Axiom thm_TREAL_ADD_LINV : forall x : prod hreal hreal, treal_eq (treal_add (treal_neg x) x) (treal_of_num (N0)).
Axiom thm_TREAL_MUL_SYM : forall x : prod hreal hreal, forall y : prod hreal hreal, treal_eq (treal_mul x y) (treal_mul y x).
Axiom thm_TREAL_MUL_ASSOC : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z).
Axiom thm_TREAL_MUL_LID : forall x : prod hreal hreal, treal_eq (treal_mul (treal_of_num ((BIT1 N0))) x) x.
Axiom thm_TREAL_ADD_LDISTRIB : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)).
Axiom thm_TREAL_LE_REFL : forall x : prod hreal hreal, treal_le x x.
Axiom thm_TREAL_LE_ANTISYM : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le x y) /\ (treal_le y x)) = (treal_eq x y).
Axiom thm_TREAL_LE_TRANS : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, ((treal_le x y) /\ (treal_le y z)) -> treal_le x z.
Axiom thm_TREAL_LE_TOTAL : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_le x y) \/ (treal_le y x).
Axiom thm_TREAL_LE_LADD_IMP : forall x : prod hreal hreal, forall y : prod hreal hreal, forall z : prod hreal hreal, (treal_le y z) -> treal_le (treal_add x y) (treal_add x z).
Axiom thm_TREAL_LE_MUL : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le (treal_of_num (N0)) x) /\ (treal_le (treal_of_num (N0)) y)) -> treal_le (treal_of_num (N0)) (treal_mul x y).
Axiom thm_TREAL_INV_0 : treal_eq (treal_inv (treal_of_num (N0))) (treal_of_num (N0)).
Axiom thm_TREAL_MUL_LINV : forall x : prod hreal hreal, (~ (treal_eq x (treal_of_num (N0)))) -> treal_eq (treal_mul (treal_inv x) x) (treal_of_num ((BIT1 N0))).
Axiom thm_TREAL_OF_NUM_WELLDEF : forall m : N, forall n : N, (m = n) -> treal_eq (treal_of_num m) (treal_of_num n).
Axiom thm_TREAL_NEG_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_neg x1) (treal_neg x2).
Axiom thm_TREAL_ADD_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_add x1 y) (treal_add x2 y).
Axiom thm_TREAL_ADD_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_add x1 y1) (treal_add x2 y2).
Axiom thm_TREAL_MUL_WELLDEFR : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x1 x2) -> treal_eq (treal_mul x1 y) (treal_mul x2 y).
Axiom thm_TREAL_MUL_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> treal_eq (treal_mul x1 y1) (treal_mul x2 y2).
Axiom thm_TREAL_EQ_IMP_LE : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_le x y.
Axiom thm_TREAL_LE_WELLDEF : forall x1 : prod hreal hreal, forall x2 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x1 x2) /\ (treal_eq y1 y2)) -> (treal_le x1 y1) = (treal_le x2 y2).
Axiom thm_TREAL_INV_WELLDEF : forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) -> treal_eq (treal_inv x) (treal_inv y).
Axiom thm_REAL_ADD_SYM : forall x : real, forall y : real, (real_add x y) = (real_add y x).
Axiom thm_REAL_ADD_ASSOC : forall x : real, forall y : real, forall z : real, (real_add x (real_add y z)) = (real_add (real_add x y) z).
Axiom thm_REAL_ADD_LID : forall x : real, (real_add (real_of_num (N0)) x) = x.
Axiom thm_REAL_ADD_LINV : forall x : real, (real_add (real_neg x) x) = (real_of_num (N0)).
Axiom thm_REAL_MUL_SYM : forall x : real, forall y : real, (real_mul x y) = (real_mul y x).
Axiom thm_REAL_MUL_ASSOC : forall x : real, forall y : real, forall z : real, (real_mul x (real_mul y z)) = (real_mul (real_mul x y) z).
Axiom thm_REAL_MUL_LID : forall x : real, (real_mul (real_of_num ((BIT1 N0))) x) = x.
Axiom thm_REAL_ADD_LDISTRIB : forall x : real, forall y : real, forall z : real, (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z)).
Axiom thm_REAL_LE_REFL : forall x : real, real_le x x.
Axiom thm_REAL_LE_ANTISYM : forall x : real, forall y : real, ((real_le x y) /\ (real_le y x)) = (x = y).
Axiom thm_REAL_LE_TRANS : forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le y z)) -> real_le x z.
Axiom thm_REAL_LE_TOTAL : forall x : real, forall y : real, (real_le x y) \/ (real_le y x).
Axiom thm_REAL_LE_LADD_IMP : forall x : real, forall y : real, forall z : real, (real_le y z) -> real_le (real_add x y) (real_add x z).
Axiom thm_REAL_LE_MUL : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le (real_of_num (N0)) y)) -> real_le (real_of_num (N0)) (real_mul x y).
Axiom thm_REAL_INV_0 : (real_inv (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_REAL_MUL_LINV : forall x : real, (~ (x = (real_of_num (N0)))) -> (real_mul (real_inv x) x) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_OF_NUM_EQ : forall m : N, forall n : N, ((real_of_num m) = (real_of_num n)) = (m = n).
Axiom thm_REAL_OF_NUM_LE : forall m : N, forall n : N, (real_le (real_of_num m) (real_of_num n)) = (N.le m n).
Axiom thm_REAL_OF_NUM_ADD : forall m : N, forall n : N, (real_add (real_of_num m) (real_of_num n)) = (real_of_num (N.add m n)).
Axiom thm_REAL_OF_NUM_MUL : forall m : N, forall n : N, (real_mul (real_of_num m) (real_of_num n)) = (real_of_num (N.mul m n)).
Axiom thm_real_sub : forall x : real, forall y : real, (real_sub x y) = (real_add x (real_neg y)).
Axiom thm_real_lt : forall y : real, forall x : real, (real_lt x y) = (~ (real_le y x)).
Axiom thm_real_ge : forall y : real, forall x : real, (real_ge x y) = (real_le y x).
Axiom thm_real_gt : forall y : real, forall x : real, (real_gt x y) = (real_lt y x).
Axiom thm_real_abs : forall x : real, (real_abs x) = (@COND real (real_le (real_of_num (N0)) x) x (real_neg x)).
Axiom thm_real_pow : forall (x : real), ((real_pow x (N0)) = (real_of_num ((BIT1 N0)))) /\ (forall n : N, (real_pow x (N.succ n)) = (real_mul x (real_pow x n))).
Axiom thm_real_div : forall x : real, forall y : real, (real_div x y) = (real_mul x (real_inv y)).
Axiom thm_real_max : forall n : real, forall m : real, (real_max m n) = (@COND real (real_le m n) n m).
Axiom thm_real_min : forall m : real, forall n : real, (real_min m n) = (@COND real (real_le m n) m n).
Axiom thm_REAL_HREAL_LEMMA1 : exists r : hreal -> real, (forall x : real, (real_le (real_of_num (N0)) x) = (exists y : hreal, x = (r y))) /\ (forall y : hreal, forall z : hreal, (hreal_le y z) = (real_le (r y) (r z))).
Axiom thm_REAL_HREAL_LEMMA2 : exists h : real -> hreal, exists r : hreal -> real, (forall x : hreal, (h (r x)) = x) /\ ((forall x : real, (real_le (real_of_num (N0)) x) -> (r (h x)) = x) /\ ((forall x : hreal, real_le (real_of_num (N0)) (r x)) /\ (forall x : hreal, forall y : hreal, (hreal_le x y) = (real_le (r x) (r y))))).
Axiom thm_REAL_COMPLETE_SOMEPOS : forall P : real -> Prop, ((exists x : real, (P x) /\ (real_le (real_of_num (N0)) x)) /\ (exists M : real, forall x : real, (P x) -> real_le x M)) -> exists M : real, (forall x : real, (P x) -> real_le x M) /\ (forall M' : real, (forall x : real, (P x) -> real_le x M') -> real_le M M').
Axiom thm_REAL_COMPLETE : forall P : real -> Prop, ((exists x : real, P x) /\ (exists M : real, forall x : real, (P x) -> real_le x M)) -> exists M : real, (forall x : real, (P x) -> real_le x M) /\ (forall M' : real, (forall x : real, (P x) -> real_le x M') -> real_le M M').
Axiom thm_REAL_ADD_AC : forall (n : real) (m : real) (p : real), ((real_add m n) = (real_add n m)) /\ (((real_add (real_add m n) p) = (real_add m (real_add n p))) /\ ((real_add m (real_add n p)) = (real_add n (real_add m p)))).
Axiom thm_REAL_ADD_RINV : forall x : real, (real_add x (real_neg x)) = (real_of_num (N0)).
Axiom thm_REAL_EQ_ADD_LCANCEL : forall x : real, forall y : real, forall z : real, ((real_add x y) = (real_add x z)) = (y = z).
Axiom thm_REAL_EQ_ADD_RCANCEL : forall x : real, forall y : real, forall z : real, ((real_add x z) = (real_add y z)) = (x = y).
Axiom thm_REAL_MUL_RZERO : forall x : real, (real_mul x (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_REAL_MUL_LZERO : forall x : real, (real_mul (real_of_num (N0)) x) = (real_of_num (N0)).
Axiom thm_REAL_NEG_NEG : forall x : real, (real_neg (real_neg x)) = x.
Axiom thm_REAL_MUL_RNEG : forall x : real, forall y : real, (real_mul x (real_neg y)) = (real_neg (real_mul x y)).
Axiom thm_REAL_MUL_LNEG : forall x : real, forall y : real, (real_mul (real_neg x) y) = (real_neg (real_mul x y)).
Axiom thm_REAL_NEG_ADD : forall x : real, forall y : real, (real_neg (real_add x y)) = (real_add (real_neg x) (real_neg y)).
Axiom thm_REAL_ADD_RID : forall x : real, (real_add x (real_of_num (N0))) = x.
Axiom thm_REAL_NEG_0 : (real_neg (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_REAL_LE_LNEG : forall x : real, forall y : real, (real_le (real_neg x) y) = (real_le (real_of_num (N0)) (real_add x y)).
Axiom thm_REAL_LE_NEG2 : forall x : real, forall y : real, (real_le (real_neg x) (real_neg y)) = (real_le y x).
Axiom thm_REAL_LE_RNEG : forall x : real, forall y : real, (real_le x (real_neg y)) = (real_le (real_add x y) (real_of_num (N0))).
Axiom thm_REAL_OF_NUM_POW : forall x : N, forall n : N, (real_pow (real_of_num x) n) = (real_of_num (N.pow x n)).
Axiom thm_REAL_POW_NEG : forall x : real, forall n : N, (real_pow (real_neg x) n) = (@COND real (N.Even n) (real_pow x n) (real_neg (real_pow x n))).
Axiom thm_REAL_ABS_NUM : forall n : N, (real_abs (real_of_num n)) = (real_of_num n).
Axiom thm_REAL_ABS_NEG : forall x : real, (real_abs (real_neg x)) = (real_abs x).
Axiom thm_REAL_LTE_TOTAL : forall x : real, forall y : real, (real_lt x y) \/ (real_le y x).
Axiom thm_REAL_LET_TOTAL : forall x : real, forall y : real, (real_le x y) \/ (real_lt y x).
Axiom thm_REAL_LT_IMP_LE : forall x : real, forall y : real, (real_lt x y) -> real_le x y.
Axiom thm_REAL_LTE_TRANS : forall x : real, forall y : real, forall z : real, ((real_lt x y) /\ (real_le y z)) -> real_lt x z.
Axiom thm_REAL_LET_TRANS : forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_lt y z)) -> real_lt x z.
Axiom thm_REAL_LT_TRANS : forall x : real, forall y : real, forall z : real, ((real_lt x y) /\ (real_lt y z)) -> real_lt x z.
Axiom thm_REAL_LE_ADD : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le (real_of_num (N0)) y)) -> real_le (real_of_num (N0)) (real_add x y).
Axiom thm_REAL_LTE_ANTISYM : forall x : real, forall y : real, ~ ((real_lt x y) /\ (real_le y x)).
Axiom thm_REAL_SUB_LE : forall x : real, forall y : real, (real_le (real_of_num (N0)) (real_sub x y)) = (real_le y x).
Axiom thm_REAL_NEG_SUB : forall x : real, forall y : real, (real_neg (real_sub x y)) = (real_sub y x).
Axiom thm_REAL_LE_LT : forall x : real, forall y : real, (real_le x y) = ((real_lt x y) \/ (x = y)).
Axiom thm_REAL_SUB_LT : forall x : real, forall y : real, (real_lt (real_of_num (N0)) (real_sub x y)) = (real_lt y x).
Axiom thm_REAL_NOT_LT : forall x : real, forall y : real, (~ (real_lt x y)) = (real_le y x).
Axiom thm_REAL_SUB_0 : forall x : real, forall y : real, ((real_sub x y) = (real_of_num (N0))) = (x = y).
Axiom thm_REAL_LT_LE : forall x : real, forall y : real, (real_lt x y) = ((real_le x y) /\ (~ (x = y))).
Axiom thm_REAL_LT_REFL : forall x : real, ~ (real_lt x x).
Axiom thm_REAL_LTE_ADD : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_le (real_of_num (N0)) y)) -> real_lt (real_of_num (N0)) (real_add x y).
Axiom thm_REAL_LET_ADD : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) -> real_lt (real_of_num (N0)) (real_add x y).
Axiom thm_REAL_LT_ADD : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) -> real_lt (real_of_num (N0)) (real_add x y).
Axiom thm_REAL_ENTIRE : forall x : real, forall y : real, ((real_mul x y) = (real_of_num (N0))) = ((x = (real_of_num (N0))) \/ (y = (real_of_num (N0)))).
Axiom thm_REAL_LE_NEGTOTAL : forall x : real, (real_le (real_of_num (N0)) x) \/ (real_le (real_of_num (N0)) (real_neg x)).
Axiom thm_REAL_LE_SQUARE : forall x : real, real_le (real_of_num (N0)) (real_mul x x).
Axiom thm_REAL_MUL_RID : forall x : real, (real_mul x (real_of_num ((BIT1 N0)))) = x.
Axiom thm_REAL_POW_2 : forall x : real, (real_pow x ((BIT0 (BIT1 N0)))) = (real_mul x x).
Axiom thm_REAL_POLY_CLAUSES : (forall x : real, forall y : real, forall z : real, (real_add x (real_add y z)) = (real_add (real_add x y) z)) /\ ((forall x : real, forall y : real, (real_add x y) = (real_add y x)) /\ ((forall x : real, (real_add (real_of_num (N0)) x) = x) /\ ((forall x : real, forall y : real, forall z : real, (real_mul x (real_mul y z)) = (real_mul (real_mul x y) z)) /\ ((forall x : real, forall y : real, (real_mul x y) = (real_mul y x)) /\ ((forall x : real, (real_mul (real_of_num ((BIT1 N0))) x) = x) /\ ((forall x : real, (real_mul (real_of_num (N0)) x) = (real_of_num (N0))) /\ ((forall x : real, forall y : real, forall z : real, (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z))) /\ ((forall x : real, (real_pow x (N0)) = (real_of_num ((BIT1 N0)))) /\ (forall x : real, forall n : N, (real_pow x (N.succ n)) = (real_mul x (real_pow x n))))))))))).
Axiom thm_REAL_POLY_NEG_CLAUSES : (forall x : real, (real_neg x) = (real_mul (real_neg (real_of_num ((BIT1 N0)))) x)) /\ (forall x : real, forall y : real, (real_sub x y) = (real_add x (real_mul (real_neg (real_of_num ((BIT1 N0)))) y))).
Axiom thm_REAL_POS : forall n : N, real_le (real_of_num (N0)) (real_of_num n).
Axiom thm_REAL_LT_NZ : forall n : N, (~ ((real_of_num n) = (real_of_num (N0)))) = (real_lt (real_of_num (N0)) (real_of_num n)).
Axiom thm_REAL_POS_LT : forall n : N, real_lt (real_of_num (N0)) (real_of_num (N.succ n)).
Axiom thm_REAL_OF_NUM_LT : forall m : N, forall n : N, (real_lt (real_of_num m) (real_of_num n)) = (N.lt m n).
Axiom thm_REAL_OF_NUM_GE : forall m : N, forall n : N, (real_ge (real_of_num m) (real_of_num n)) = (N.ge m n).
Axiom thm_REAL_OF_NUM_GT : forall m : N, forall n : N, (real_gt (real_of_num m) (real_of_num n)) = (N.gt m n).
Axiom thm_REAL_OF_NUM_MAX : forall m : N, forall n : N, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (N.max m n)).
Axiom thm_REAL_OF_NUM_MIN : forall m : N, forall n : N, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (N.min m n)).
Axiom thm_REAL_OF_NUM_SUC : forall n : N, (real_add (real_of_num n) (real_of_num ((BIT1 N0)))) = (real_of_num (N.succ n)).
Axiom thm_REAL_OF_NUM_SUB : forall m : N, forall n : N, (N.le m n) -> (real_sub (real_of_num n) (real_of_num m)) = (real_of_num (N.sub n m)).
Axiom thm_REAL_OF_NUM_SUB_CASES : forall m : N, forall n : N, (real_sub (real_of_num m) (real_of_num n)) = (@COND real (N.le n m) (real_of_num (N.sub m n)) (real_neg (real_of_num (N.sub n m)))).
Axiom thm_REAL_OF_NUM_CLAUSES : (forall m : N, forall n : N, ((real_of_num m) = (real_of_num n)) = (m = n)) /\ ((forall m : N, forall n : N, (real_ge (real_of_num m) (real_of_num n)) = (N.ge m n)) /\ ((forall m : N, forall n : N, (real_gt (real_of_num m) (real_of_num n)) = (N.gt m n)) /\ ((forall m : N, forall n : N, (real_le (real_of_num m) (real_of_num n)) = (N.le m n)) /\ ((forall m : N, forall n : N, (real_lt (real_of_num m) (real_of_num n)) = (N.lt m n)) /\ ((forall m : N, forall n : N, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (N.max m n))) /\ ((forall m : N, forall n : N, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (N.min m n))) /\ ((forall m : N, forall n : N, (real_add (real_of_num m) (real_of_num n)) = (real_of_num (N.add m n))) /\ ((forall m : N, forall n : N, (real_mul (real_of_num m) (real_of_num n)) = (real_of_num (N.mul m n))) /\ (forall x : N, forall n : N, (real_pow (real_of_num x) n) = (real_of_num (N.pow x n))))))))))).
Axiom thm_REAL_MUL_AC : forall (n : real) (m : real) (p : real), ((real_mul m n) = (real_mul n m)) /\ (((real_mul (real_mul m n) p) = (real_mul m (real_mul n p))) /\ ((real_mul m (real_mul n p)) = (real_mul n (real_mul m p)))).
Axiom thm_REAL_ADD_RDISTRIB : forall x : real, forall y : real, forall z : real, (real_mul (real_add x y) z) = (real_add (real_mul x z) (real_mul y z)).
Axiom thm_REAL_LT_LADD_IMP : forall x : real, forall y : real, forall z : real, (real_lt y z) -> real_lt (real_add x y) (real_add x z).
Axiom thm_REAL_LT_MUL : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) -> real_lt (real_of_num (N0)) (real_mul x y).
Axiom thm_REAL_EQ_ADD_LCANCEL_0 : forall x : real, forall y : real, ((real_add x y) = x) = (y = (real_of_num (N0))).
Axiom thm_REAL_EQ_ADD_RCANCEL_0 : forall x : real, forall y : real, ((real_add x y) = y) = (x = (real_of_num (N0))).
Axiom thm_REAL_LNEG_UNIQ : forall x : real, forall y : real, ((real_add x y) = (real_of_num (N0))) = (x = (real_neg y)).
Axiom thm_REAL_RNEG_UNIQ : forall x : real, forall y : real, ((real_add x y) = (real_of_num (N0))) = (y = (real_neg x)).
Axiom thm_REAL_NEG_LMUL : forall x : real, forall y : real, (real_neg (real_mul x y)) = (real_mul (real_neg x) y).
Axiom thm_REAL_NEG_RMUL : forall x : real, forall y : real, (real_neg (real_mul x y)) = (real_mul x (real_neg y)).
Axiom thm_REAL_NEG_MUL2 : forall x : real, forall y : real, (real_mul (real_neg x) (real_neg y)) = (real_mul x y).
Axiom thm_REAL_LT_LADD : forall x : real, forall y : real, forall z : real, (real_lt (real_add x y) (real_add x z)) = (real_lt y z).
Axiom thm_REAL_LT_RADD : forall x : real, forall y : real, forall z : real, (real_lt (real_add x z) (real_add y z)) = (real_lt x y).
Axiom thm_REAL_LT_ANTISYM : forall x : real, forall y : real, ~ ((real_lt x y) /\ (real_lt y x)).
Axiom thm_REAL_LT_GT : forall x : real, forall y : real, (real_lt x y) -> ~ (real_lt y x).
Axiom thm_REAL_NOT_EQ : forall x : real, forall y : real, (~ (x = y)) = ((real_lt x y) \/ (real_lt y x)).
Axiom thm_REAL_NOT_LE : forall x : real, forall y : real, (~ (real_le x y)) = (real_lt y x).
Axiom thm_REAL_LET_ANTISYM : forall x : real, forall y : real, ~ ((real_le x y) /\ (real_lt y x)).
Axiom thm_REAL_NEG_LT0 : forall x : real, (real_lt (real_neg x) (real_of_num (N0))) = (real_lt (real_of_num (N0)) x).
Axiom thm_REAL_NEG_GT0 : forall x : real, (real_lt (real_of_num (N0)) (real_neg x)) = (real_lt x (real_of_num (N0))).
Axiom thm_REAL_NEG_LE0 : forall x : real, (real_le (real_neg x) (real_of_num (N0))) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_NEG_GE0 : forall x : real, (real_le (real_of_num (N0)) (real_neg x)) = (real_le x (real_of_num (N0))).
Axiom thm_REAL_LT_TOTAL : forall x : real, forall y : real, (x = y) \/ ((real_lt x y) \/ (real_lt y x)).
Axiom thm_REAL_LT_NEGTOTAL : forall x : real, (x = (real_of_num (N0))) \/ ((real_lt (real_of_num (N0)) x) \/ (real_lt (real_of_num (N0)) (real_neg x))).
Axiom thm_REAL_LE_01 : real_le (real_of_num (N0)) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_LT_01 : real_lt (real_of_num (N0)) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_LE_LADD : forall x : real, forall y : real, forall z : real, (real_le (real_add x y) (real_add x z)) = (real_le y z).
Axiom thm_REAL_LE_RADD : forall x : real, forall y : real, forall z : real, (real_le (real_add x z) (real_add y z)) = (real_le x y).
Axiom thm_REAL_LT_ADD2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_lt w x) /\ (real_lt y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_LE_ADD2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le w x) /\ (real_le y z)) -> real_le (real_add w y) (real_add x z).
Axiom thm_REAL_LT_LNEG : forall x : real, forall y : real, (real_lt (real_neg x) y) = (real_lt (real_of_num (N0)) (real_add x y)).
Axiom thm_REAL_LT_RNEG : forall x : real, forall y : real, (real_lt x (real_neg y)) = (real_lt (real_add x y) (real_of_num (N0))).
Axiom thm_REAL_LT_ADDNEG : forall x : real, forall y : real, forall z : real, (real_lt y (real_add x (real_neg z))) = (real_lt (real_add y z) x).
Axiom thm_REAL_LT_ADDNEG2 : forall x : real, forall y : real, forall z : real, (real_lt (real_add x (real_neg y)) z) = (real_lt x (real_add z y)).
Axiom thm_REAL_LT_ADD1 : forall x : real, forall y : real, (real_le x y) -> real_lt x (real_add y (real_of_num ((BIT1 N0)))).
Axiom thm_REAL_SUB_ADD : forall x : real, forall y : real, (real_add (real_sub x y) y) = x.
Axiom thm_REAL_SUB_ADD2 : forall x : real, forall y : real, (real_add y (real_sub x y)) = x.
Axiom thm_REAL_SUB_REFL : forall x : real, (real_sub x x) = (real_of_num (N0)).
Axiom thm_REAL_LE_DOUBLE : forall x : real, (real_le (real_of_num (N0)) (real_add x x)) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_LE_NEGL : forall x : real, (real_le (real_neg x) x) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_LE_NEGR : forall x : real, (real_le x (real_neg x)) = (real_le x (real_of_num (N0))).
Axiom thm_REAL_NEG_EQ_0 : forall x : real, ((real_neg x) = (real_of_num (N0))) = (x = (real_of_num (N0))).
Axiom thm_REAL_ADD_SUB : forall x : real, forall y : real, (real_sub (real_add x y) x) = y.
Axiom thm_REAL_NEG_EQ : forall x : real, forall y : real, ((real_neg x) = y) = (x = (real_neg y)).
Axiom thm_REAL_NEG_MINUS1 : forall x : real, (real_neg x) = (real_mul (real_neg (real_of_num ((BIT1 N0)))) x).
Axiom thm_REAL_LT_IMP_NE : forall x : real, forall y : real, (real_lt x y) -> ~ (x = y).
Axiom thm_REAL_LE_ADDR : forall x : real, forall y : real, (real_le x (real_add x y)) = (real_le (real_of_num (N0)) y).
Axiom thm_REAL_LE_ADDL : forall x : real, forall y : real, (real_le y (real_add x y)) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_LT_ADDR : forall x : real, forall y : real, (real_lt x (real_add x y)) = (real_lt (real_of_num (N0)) y).
Axiom thm_REAL_LT_ADDL : forall x : real, forall y : real, (real_lt y (real_add x y)) = (real_lt (real_of_num (N0)) x).
Axiom thm_REAL_SUB_SUB : forall x : real, forall y : real, (real_sub (real_sub x y) x) = (real_neg y).
Axiom thm_REAL_LT_ADD_SUB : forall x : real, forall y : real, forall z : real, (real_lt (real_add x y) z) = (real_lt x (real_sub z y)).
Axiom thm_REAL_LT_SUB_RADD : forall x : real, forall y : real, forall z : real, (real_lt (real_sub x y) z) = (real_lt x (real_add z y)).
Axiom thm_REAL_LT_SUB_LADD : forall x : real, forall y : real, forall z : real, (real_lt x (real_sub y z)) = (real_lt (real_add x z) y).
Axiom thm_REAL_LE_SUB_LADD : forall x : real, forall y : real, forall z : real, (real_le x (real_sub y z)) = (real_le (real_add x z) y).
Axiom thm_REAL_LE_SUB_RADD : forall x : real, forall y : real, forall z : real, (real_le (real_sub x y) z) = (real_le x (real_add z y)).
Axiom thm_REAL_ADD2_SUB2 : forall a : real, forall b : real, forall c : real, forall d : real, (real_sub (real_add a b) (real_add c d)) = (real_add (real_sub a c) (real_sub b d)).
Axiom thm_REAL_SUB_LZERO : forall x : real, (real_sub (real_of_num (N0)) x) = (real_neg x).
Axiom thm_REAL_SUB_RZERO : forall x : real, (real_sub x (real_of_num (N0))) = x.
Axiom thm_REAL_LET_ADD2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le w x) /\ (real_lt y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_LTE_ADD2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_lt w x) /\ (real_le y z)) -> real_lt (real_add w y) (real_add x z).
Axiom thm_REAL_SUB_LNEG : forall x : real, forall y : real, (real_sub (real_neg x) y) = (real_neg (real_add x y)).
Axiom thm_REAL_SUB_RNEG : forall x : real, forall y : real, (real_sub x (real_neg y)) = (real_add x y).
Axiom thm_REAL_SUB_NEG2 : forall x : real, forall y : real, (real_sub (real_neg x) (real_neg y)) = (real_sub y x).
Axiom thm_REAL_SUB_TRIANGLE : forall a : real, forall b : real, forall c : real, (real_add (real_sub a b) (real_sub b c)) = (real_sub a c).
Axiom thm_REAL_EQ_SUB_LADD : forall x : real, forall y : real, forall z : real, (x = (real_sub y z)) = ((real_add x z) = y).
Axiom thm_REAL_EQ_SUB_RADD : forall x : real, forall y : real, forall z : real, ((real_sub x y) = z) = (x = (real_add z y)).
Axiom thm_REAL_SUB_SUB2 : forall x : real, forall y : real, (real_sub x (real_sub x y)) = y.
Axiom thm_REAL_ADD_SUB2 : forall x : real, forall y : real, (real_sub x (real_add x y)) = (real_neg y).
Axiom thm_REAL_EQ_IMP_LE : forall x : real, forall y : real, (x = y) -> real_le x y.
Axiom thm_REAL_LT_IMP_NZ : forall x : real, (real_lt (real_of_num (N0)) x) -> ~ (x = (real_of_num (N0))).
Axiom thm_REAL_DIFFSQ : forall x : real, forall y : real, (real_mul (real_add x y) (real_sub x y)) = (real_sub (real_mul x x) (real_mul y y)).
Axiom thm_REAL_EQ_NEG2 : forall x : real, forall y : real, ((real_neg x) = (real_neg y)) = (x = y).
Axiom thm_REAL_LT_NEG2 : forall x : real, forall y : real, (real_lt (real_neg x) (real_neg y)) = (real_lt y x).
Axiom thm_REAL_SUB_LDISTRIB : forall x : real, forall y : real, forall z : real, (real_mul x (real_sub y z)) = (real_sub (real_mul x y) (real_mul x z)).
Axiom thm_REAL_SUB_RDISTRIB : forall x : real, forall y : real, forall z : real, (real_mul (real_sub x y) z) = (real_sub (real_mul x z) (real_mul y z)).
Axiom thm_REAL_ABS_ZERO : forall x : real, ((real_abs x) = (real_of_num (N0))) = (x = (real_of_num (N0))).
Axiom thm_REAL_ABS_0 : (real_abs (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_REAL_ABS_1 : (real_abs (real_of_num ((BIT1 N0)))) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_ABS_TRIANGLE : forall x : real, forall y : real, real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y)).
Axiom thm_REAL_ABS_TRIANGLE_LE : forall x : real, forall y : real, forall z : real, (real_le (real_add (real_abs x) (real_abs (real_sub y x))) z) -> real_le (real_abs y) z.
Axiom thm_REAL_ABS_TRIANGLE_LT : forall x : real, forall y : real, forall z : real, (real_lt (real_add (real_abs x) (real_abs (real_sub y x))) z) -> real_lt (real_abs y) z.
Axiom thm_REAL_ABS_POS : forall x : real, real_le (real_of_num (N0)) (real_abs x).
Axiom thm_REAL_ABS_SUB : forall x : real, forall y : real, (real_abs (real_sub x y)) = (real_abs (real_sub y x)).
Axiom thm_REAL_ABS_NZ : forall x : real, (~ (x = (real_of_num (N0)))) = (real_lt (real_of_num (N0)) (real_abs x)).
Axiom thm_REAL_ABS_ABS : forall x : real, (real_abs (real_abs x)) = (real_abs x).
Axiom thm_REAL_ABS_LE : forall x : real, real_le x (real_abs x).
Axiom thm_REAL_ABS_REFL : forall x : real, ((real_abs x) = x) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_ABS_BETWEEN : forall x : real, forall y : real, forall d : real, ((real_lt (real_of_num (N0)) d) /\ ((real_lt (real_sub x d) y) /\ (real_lt y (real_add x d)))) = (real_lt (real_abs (real_sub y x)) d).
Axiom thm_REAL_ABS_BOUND : forall x : real, forall y : real, forall d : real, (real_lt (real_abs (real_sub x y)) d) -> real_lt y (real_add x d).
Axiom thm_REAL_ABS_STILLNZ : forall x : real, forall y : real, (real_lt (real_abs (real_sub x y)) (real_abs y)) -> ~ (x = (real_of_num (N0))).
Axiom thm_REAL_ABS_CASES : forall x : real, (x = (real_of_num (N0))) \/ (real_lt (real_of_num (N0)) (real_abs x)).
Axiom thm_REAL_ABS_BETWEEN1 : forall x : real, forall y : real, forall z : real, ((real_lt x z) /\ (real_lt (real_abs (real_sub y x)) (real_sub z x))) -> real_lt y z.
Axiom thm_REAL_ABS_SIGN : forall x : real, forall y : real, (real_lt (real_abs (real_sub x y)) y) -> real_lt (real_of_num (N0)) x.
Axiom thm_REAL_ABS_SIGN2 : forall x : real, forall y : real, (real_lt (real_abs (real_sub x y)) (real_neg y)) -> real_lt x (real_of_num (N0)).
Axiom thm_REAL_ABS_CIRCLE : forall x : real, forall y : real, forall h : real, (real_lt (real_abs h) (real_sub (real_abs y) (real_abs x))) -> real_lt (real_abs (real_add x h)) (real_abs y).
Axiom thm_REAL_SUB_ABS : forall x : real, forall y : real, real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y)).
Axiom thm_REAL_ABS_SUB_ABS : forall x : real, forall y : real, real_le (real_abs (real_sub (real_abs x) (real_abs y))) (real_abs (real_sub x y)).
Axiom thm_REAL_ABS_BETWEEN2 : forall x0 : real, forall x : real, forall y0 : real, forall y : real, ((real_lt x0 y0) /\ ((real_lt (real_mul (real_of_num ((BIT0 (BIT1 N0)))) (real_abs (real_sub x x0))) (real_sub y0 x0)) /\ (real_lt (real_mul (real_of_num ((BIT0 (BIT1 N0)))) (real_abs (real_sub y y0))) (real_sub y0 x0)))) -> real_lt x y.
Axiom thm_REAL_ABS_BOUNDS : forall x : real, forall k : real, (real_le (real_abs x) k) = ((real_le (real_neg k) x) /\ (real_le x k)).
Axiom thm_REAL_BOUNDS_LE : forall x : real, forall k : real, ((real_le (real_neg k) x) /\ (real_le x k)) = (real_le (real_abs x) k).
Axiom thm_REAL_BOUNDS_LT : forall x : real, forall k : real, ((real_lt (real_neg k) x) /\ (real_lt x k)) = (real_lt (real_abs x) k).
Axiom thm_REAL_MIN_MAX : forall x : real, forall y : real, (real_min x y) = (real_neg (real_max (real_neg x) (real_neg y))).
Axiom thm_REAL_MAX_MIN : forall x : real, forall y : real, (real_max x y) = (real_neg (real_min (real_neg x) (real_neg y))).
Axiom thm_REAL_MAX_MAX : forall x : real, forall y : real, (real_le x (real_max x y)) /\ (real_le y (real_max x y)).
Axiom thm_REAL_MIN_MIN : forall x : real, forall y : real, (real_le (real_min x y) x) /\ (real_le (real_min x y) y).
Axiom thm_REAL_MAX_SYM : forall x : real, forall y : real, (real_max x y) = (real_max y x).
Axiom thm_REAL_MIN_SYM : forall x : real, forall y : real, (real_min x y) = (real_min y x).
Axiom thm_REAL_LE_MAX : forall x : real, forall y : real, forall z : real, (real_le z (real_max x y)) = ((real_le z x) \/ (real_le z y)).
Axiom thm_REAL_LE_MIN : forall x : real, forall y : real, forall z : real, (real_le z (real_min x y)) = ((real_le z x) /\ (real_le z y)).
Axiom thm_REAL_LT_MAX : forall x : real, forall y : real, forall z : real, (real_lt z (real_max x y)) = ((real_lt z x) \/ (real_lt z y)).
Axiom thm_REAL_LT_MIN : forall x : real, forall y : real, forall z : real, (real_lt z (real_min x y)) = ((real_lt z x) /\ (real_lt z y)).
Axiom thm_REAL_MAX_LE : forall x : real, forall y : real, forall z : real, (real_le (real_max x y) z) = ((real_le x z) /\ (real_le y z)).
Axiom thm_REAL_MIN_LE : forall x : real, forall y : real, forall z : real, (real_le (real_min x y) z) = ((real_le x z) \/ (real_le y z)).
Axiom thm_REAL_MAX_LT : forall x : real, forall y : real, forall z : real, (real_lt (real_max x y) z) = ((real_lt x z) /\ (real_lt y z)).
Axiom thm_REAL_MIN_LT : forall x : real, forall y : real, forall z : real, (real_lt (real_min x y) z) = ((real_lt x z) \/ (real_lt y z)).
Axiom thm_REAL_MAX_ASSOC : forall x : real, forall y : real, forall z : real, (real_max x (real_max y z)) = (real_max (real_max x y) z).
Axiom thm_REAL_MIN_ASSOC : forall x : real, forall y : real, forall z : real, (real_min x (real_min y z)) = (real_min (real_min x y) z).
Axiom thm_REAL_MAX_ACI : forall (z : real) (x : real) (y : real), ((real_max x y) = (real_max y x)) /\ (((real_max (real_max x y) z) = (real_max x (real_max y z))) /\ (((real_max x (real_max y z)) = (real_max y (real_max x z))) /\ (((real_max x x) = x) /\ ((real_max x (real_max x y)) = (real_max x y))))).
Axiom thm_REAL_MIN_ACI : forall (z : real) (x : real) (y : real), ((real_min x y) = (real_min y x)) /\ (((real_min (real_min x y) z) = (real_min x (real_min y z))) /\ (((real_min x (real_min y z)) = (real_min y (real_min x z))) /\ (((real_min x x) = x) /\ ((real_min x (real_min x y)) = (real_min x y))))).
Axiom thm_REAL_ABS_MUL : forall x : real, forall y : real, (real_abs (real_mul x y)) = (real_mul (real_abs x) (real_abs y)).
Axiom thm_REAL_POW_LE : forall x : real, forall n : N, (real_le (real_of_num (N0)) x) -> real_le (real_of_num (N0)) (real_pow x n).
Axiom thm_REAL_POW_LT : forall x : real, forall n : N, (real_lt (real_of_num (N0)) x) -> real_lt (real_of_num (N0)) (real_pow x n).
Axiom thm_REAL_ABS_POW : forall x : real, forall n : N, (real_abs (real_pow x n)) = (real_pow (real_abs x) n).
Axiom thm_REAL_LE_LMUL : forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (N0)) x) /\ (real_le y z)) -> real_le (real_mul x y) (real_mul x z).
Axiom thm_REAL_LE_RMUL : forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le (real_of_num (N0)) z)) -> real_le (real_mul x z) (real_mul y z).
Axiom thm_REAL_LT_LMUL : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt y z)) -> real_lt (real_mul x y) (real_mul x z).
Axiom thm_REAL_LT_RMUL : forall x : real, forall y : real, forall z : real, ((real_lt x y) /\ (real_lt (real_of_num (N0)) z)) -> real_lt (real_mul x z) (real_mul y z).
Axiom thm_REAL_EQ_MUL_LCANCEL : forall x : real, forall y : real, forall z : real, ((real_mul x y) = (real_mul x z)) = ((x = (real_of_num (N0))) \/ (y = z)).
Axiom thm_REAL_EQ_MUL_RCANCEL : forall x : real, forall y : real, forall z : real, ((real_mul x z) = (real_mul y z)) = ((x = y) \/ (z = (real_of_num (N0)))).
Axiom thm_REAL_MUL_LINV_UNIQ : forall x : real, forall y : real, ((real_mul x y) = (real_of_num ((BIT1 N0)))) -> (real_inv y) = x.
Axiom thm_REAL_MUL_RINV_UNIQ : forall x : real, forall y : real, ((real_mul x y) = (real_of_num ((BIT1 N0)))) -> (real_inv x) = y.
Axiom thm_REAL_INV_INV : forall x : real, (real_inv (real_inv x)) = x.
Axiom thm_REAL_EQ_INV2 : forall x : real, forall y : real, ((real_inv x) = (real_inv y)) = (x = y).
Axiom thm_REAL_INV_EQ_0 : forall x : real, ((real_inv x) = (real_of_num (N0))) = (x = (real_of_num (N0))).
Axiom thm_REAL_LT_INV : forall x : real, (real_lt (real_of_num (N0)) x) -> real_lt (real_of_num (N0)) (real_inv x).
Axiom thm_REAL_LT_INV_EQ : forall x : real, (real_lt (real_of_num (N0)) (real_inv x)) = (real_lt (real_of_num (N0)) x).
Axiom thm_REAL_INV_NEG : forall x : real, (real_inv (real_neg x)) = (real_neg (real_inv x)).
Axiom thm_REAL_LE_INV_EQ : forall x : real, (real_le (real_of_num (N0)) (real_inv x)) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_LE_INV : forall x : real, (real_le (real_of_num (N0)) x) -> real_le (real_of_num (N0)) (real_inv x).
Axiom thm_REAL_MUL_RINV : forall x : real, (~ (x = (real_of_num (N0)))) -> (real_mul x (real_inv x)) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_INV_1 : (real_inv (real_of_num ((BIT1 N0)))) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_INV_EQ_1 : forall x : real, ((real_inv x) = (real_of_num ((BIT1 N0)))) = (x = (real_of_num ((BIT1 N0)))).
Axiom thm_REAL_DIV_1 : forall x : real, (real_div x (real_of_num ((BIT1 N0)))) = x.
Axiom thm_REAL_DIV_REFL : forall x : real, (~ (x = (real_of_num (N0)))) -> (real_div x x) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_DIV_RMUL : forall x : real, forall y : real, (~ (y = (real_of_num (N0)))) -> (real_mul (real_div x y) y) = x.
Axiom thm_REAL_DIV_LMUL : forall x : real, forall y : real, (~ (y = (real_of_num (N0)))) -> (real_mul y (real_div x y)) = x.
Axiom thm_REAL_DIV_EQ_1 : forall x : real, forall y : real, ((real_div x y) = (real_of_num ((BIT1 N0)))) = ((x = y) /\ ((~ (x = (real_of_num (N0)))) /\ (~ (y = (real_of_num (N0)))))).
Axiom thm_REAL_ABS_INV : forall x : real, (real_abs (real_inv x)) = (real_inv (real_abs x)).
Axiom thm_REAL_ABS_DIV : forall x : real, forall y : real, (real_abs (real_div x y)) = (real_div (real_abs x) (real_abs y)).
Axiom thm_REAL_INV_MUL : forall x : real, forall y : real, (real_inv (real_mul x y)) = (real_mul (real_inv x) (real_inv y)).
Axiom thm_REAL_INV_DIV : forall x : real, forall y : real, (real_inv (real_div x y)) = (real_div y x).
Axiom thm_REAL_POW_MUL : forall x : real, forall y : real, forall n : N, (real_pow (real_mul x y) n) = (real_mul (real_pow x n) (real_pow y n)).
Axiom thm_REAL_POW_INV : forall x : real, forall n : N, (real_pow (real_inv x) n) = (real_inv (real_pow x n)).
Axiom thm_REAL_INV_POW : forall x : real, forall n : N, (real_inv (real_pow x n)) = (real_pow (real_inv x) n).
Axiom thm_REAL_POW_DIV : forall x : real, forall y : real, forall n : N, (real_pow (real_div x y) n) = (real_div (real_pow x n) (real_pow y n)).
Axiom thm_REAL_DIV_EQ_0 : forall x : real, forall y : real, ((real_div x y) = (real_of_num (N0))) = ((x = (real_of_num (N0))) \/ (y = (real_of_num (N0)))).
Axiom thm_REAL_POW_ADD : forall x : real, forall m : N, forall n : N, (real_pow x (N.add m n)) = (real_mul (real_pow x m) (real_pow x n)).
Axiom thm_REAL_POW_NZ : forall x : real, forall n : N, (~ (x = (real_of_num (N0)))) -> ~ ((real_pow x n) = (real_of_num (N0))).
Axiom thm_REAL_POW_SUB : forall x : real, forall m : N, forall n : N, ((~ (x = (real_of_num (N0)))) /\ (N.le m n)) -> (real_pow x (N.sub n m)) = (real_div (real_pow x n) (real_pow x m)).
Axiom thm_REAL_LT_LCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt (real_mul x y) (real_mul x z))) -> real_lt y z.
Axiom thm_REAL_LT_RCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (N0)) z) /\ (real_lt (real_mul x z) (real_mul y z))) -> real_lt x y.
Axiom thm_REAL_LE_LCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (N0)) x) /\ (real_le (real_mul x y) (real_mul x z))) -> real_le y z.
Axiom thm_REAL_LE_RCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (N0)) z) /\ (real_le (real_mul x z) (real_mul y z))) -> real_le x y.
Axiom thm_REAL_LE_RMUL_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_le (real_mul x z) (real_mul y z)) = (real_le x y).
Axiom thm_REAL_LE_LMUL_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_le (real_mul z x) (real_mul z y)) = (real_le x y).
Axiom thm_REAL_LT_RMUL_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_lt (real_mul x z) (real_mul y z)) = (real_lt x y).
Axiom thm_REAL_LT_LMUL_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_lt (real_mul z x) (real_mul z y)) = (real_lt x y).
Axiom thm_REAL_LE_MUL_EQ : (forall x : real, forall y : real, (real_lt (real_of_num (N0)) x) -> (real_le (real_of_num (N0)) (real_mul x y)) = (real_le (real_of_num (N0)) y)) /\ (forall x : real, forall y : real, (real_lt (real_of_num (N0)) y) -> (real_le (real_of_num (N0)) (real_mul x y)) = (real_le (real_of_num (N0)) x)).
Axiom thm_REAL_LT_MUL_EQ : (forall x : real, forall y : real, (real_lt (real_of_num (N0)) x) -> (real_lt (real_of_num (N0)) (real_mul x y)) = (real_lt (real_of_num (N0)) y)) /\ (forall x : real, forall y : real, (real_lt (real_of_num (N0)) y) -> (real_lt (real_of_num (N0)) (real_mul x y)) = (real_lt (real_of_num (N0)) x)).
Axiom thm_REAL_MUL_POS_LT : forall x : real, forall y : real, (real_lt (real_of_num (N0)) (real_mul x y)) = (((real_lt (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) \/ ((real_lt x (real_of_num (N0))) /\ (real_lt y (real_of_num (N0))))).
Axiom thm_REAL_MUL_POS_LE : forall x : real, forall y : real, (real_le (real_of_num (N0)) (real_mul x y)) = ((x = (real_of_num (N0))) \/ ((y = (real_of_num (N0))) \/ (((real_lt (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) \/ ((real_lt x (real_of_num (N0))) /\ (real_lt y (real_of_num (N0))))))).
Axiom thm_REAL_LE_RDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_le x (real_div y z)) = (real_le (real_mul x z) y).
Axiom thm_REAL_LE_LDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_le (real_div x z) y) = (real_le x (real_mul y z)).
Axiom thm_REAL_LT_RDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_lt x (real_div y z)) = (real_lt (real_mul x z) y).
Axiom thm_REAL_LT_LDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_lt (real_div x z) y) = (real_lt x (real_mul y z)).
Axiom thm_REAL_EQ_RDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (x = (real_div y z)) = ((real_mul x z) = y).
Axiom thm_REAL_EQ_LDIV_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> ((real_div x z) = y) = (x = (real_mul y z)).
Axiom thm_REAL_LT_DIV2_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_lt (real_div x z) (real_div y z)) = (real_lt x y).
Axiom thm_REAL_LE_DIV2_EQ : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (N0)) z) -> (real_le (real_div x z) (real_div y z)) = (real_le x y).
Axiom thm_REAL_MUL_2 : forall x : real, (real_mul (real_of_num ((BIT0 (BIT1 N0)))) x) = (real_add x x).
Axiom thm_REAL_POW_EQ_0 : forall x : real, forall n : N, ((real_pow x n) = (real_of_num (N0))) = ((x = (real_of_num (N0))) /\ (~ (n = (N0)))).
Axiom thm_REAL_LE_MUL2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (N0)) w) /\ ((real_le w x) /\ ((real_le (real_of_num (N0)) y) /\ (real_le y z)))) -> real_le (real_mul w y) (real_mul x z).
Axiom thm_REAL_LT_MUL2 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (N0)) w) /\ ((real_lt w x) /\ ((real_le (real_of_num (N0)) y) /\ (real_lt y z)))) -> real_lt (real_mul w y) (real_mul x z).
Axiom thm_REAL_LT_SQUARE : forall x : real, (real_lt (real_of_num (N0)) (real_mul x x)) = (~ (x = (real_of_num (N0)))).
Axiom thm_REAL_POW_1 : forall x : real, (real_pow x ((BIT1 N0))) = x.
Axiom thm_REAL_POW_ONE : forall n : N, (real_pow (real_of_num ((BIT1 N0))) n) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_LT_INV2 : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt x y)) -> real_lt (real_inv y) (real_inv x).
Axiom thm_REAL_LE_INV2 : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_le x y)) -> real_le (real_inv y) (real_inv x).
Axiom thm_REAL_LT_LINV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) y) /\ (real_lt (real_inv y) x)) -> real_lt (real_inv x) y.
Axiom thm_REAL_LT_RINV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt x (real_inv y))) -> real_lt y (real_inv x).
Axiom thm_REAL_LE_LINV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) y) /\ (real_le (real_inv y) x)) -> real_le (real_inv x) y.
Axiom thm_REAL_LE_RINV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_le x (real_inv y))) -> real_le y (real_inv x).
Axiom thm_REAL_INV_LE_1 : forall x : real, (real_le (real_of_num ((BIT1 N0))) x) -> real_le (real_inv x) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_INV_1_LE : forall x : real, ((real_lt (real_of_num (N0)) x) /\ (real_le x (real_of_num ((BIT1 N0))))) -> real_le (real_of_num ((BIT1 N0))) (real_inv x).
Axiom thm_REAL_INV_LT_1 : forall x : real, (real_lt (real_of_num ((BIT1 N0))) x) -> real_lt (real_inv x) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_INV_1_LT : forall x : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt x (real_of_num ((BIT1 N0))))) -> real_lt (real_of_num ((BIT1 N0))) (real_inv x).
Axiom thm_REAL_SUB_INV : forall x : real, forall y : real, ((~ (x = (real_of_num (N0)))) /\ (~ (y = (real_of_num (N0))))) -> (real_sub (real_inv x) (real_inv y)) = (real_div (real_sub y x) (real_mul x y)).
Axiom thm_REAL_DOWN : forall d : real, (real_lt (real_of_num (N0)) d) -> exists e : real, (real_lt (real_of_num (N0)) e) /\ (real_lt e d).
Axiom thm_REAL_DOWN2 : forall d1 : real, forall d2 : real, ((real_lt (real_of_num (N0)) d1) /\ (real_lt (real_of_num (N0)) d2)) -> exists e : real, (real_lt (real_of_num (N0)) e) /\ ((real_lt e d1) /\ (real_lt e d2)).
Axiom thm_REAL_POW_LE2 : forall n : N, forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le x y)) -> real_le (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LE_1 : forall n : N, forall x : real, (real_le (real_of_num ((BIT1 N0))) x) -> real_le (real_of_num ((BIT1 N0))) (real_pow x n).
Axiom thm_REAL_POW_1_LE : forall n : N, forall x : real, ((real_le (real_of_num (N0)) x) /\ (real_le x (real_of_num ((BIT1 N0))))) -> real_le (real_pow x n) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_POW_MONO : forall m : N, forall n : N, forall x : real, ((real_le (real_of_num ((BIT1 N0))) x) /\ (N.le m n)) -> real_le (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_LT2 : forall n : N, forall x : real, forall y : real, ((~ (n = (N0))) /\ ((real_le (real_of_num (N0)) x) /\ (real_lt x y))) -> real_lt (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LT_1 : forall n : N, forall x : real, ((~ (n = (N0))) /\ (real_lt (real_of_num ((BIT1 N0))) x)) -> real_lt (real_of_num ((BIT1 N0))) (real_pow x n).
Axiom thm_REAL_POW_1_LT : forall n : N, forall x : real, ((~ (n = (N0))) /\ ((real_le (real_of_num (N0)) x) /\ (real_lt x (real_of_num ((BIT1 N0)))))) -> real_lt (real_pow x n) (real_of_num ((BIT1 N0))).
Axiom thm_REAL_POW_MONO_LT : forall m : N, forall n : N, forall x : real, ((real_lt (real_of_num ((BIT1 N0))) x) /\ (N.lt m n)) -> real_lt (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_POW : forall x : real, forall m : N, forall n : N, (real_pow (real_pow x m) n) = (real_pow x (N.mul m n)).
Axiom thm_REAL_EQ_RCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((~ (z = (real_of_num (N0)))) /\ ((real_mul x z) = (real_mul y z))) -> x = y.
Axiom thm_REAL_EQ_LCANCEL_IMP : forall x : real, forall y : real, forall z : real, ((~ (z = (real_of_num (N0)))) /\ ((real_mul z x) = (real_mul z y))) -> x = y.
Axiom thm_REAL_LT_DIV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) x) /\ (real_lt (real_of_num (N0)) y)) -> real_lt (real_of_num (N0)) (real_div x y).
Axiom thm_REAL_LE_DIV : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le (real_of_num (N0)) y)) -> real_le (real_of_num (N0)) (real_div x y).
Axiom thm_REAL_DIV_POW2 : forall x : real, forall m : N, forall n : N, (~ (x = (real_of_num (N0)))) -> (real_div (real_pow x m) (real_pow x n)) = (@COND real (N.le n m) (real_pow x (N.sub m n)) (real_inv (real_pow x (N.sub n m)))).
Axiom thm_REAL_DIV_POW2_ALT : forall x : real, forall m : N, forall n : N, (~ (x = (real_of_num (N0)))) -> (real_div (real_pow x m) (real_pow x n)) = (@COND real (N.lt n m) (real_pow x (N.sub m n)) (real_inv (real_pow x (N.sub n m)))).
Axiom thm_REAL_LT_POW2 : forall n : N, real_lt (real_of_num (N0)) (real_pow (real_of_num ((BIT0 (BIT1 N0)))) n).
Axiom thm_REAL_LE_POW2 : forall n : N, real_le (real_of_num ((BIT1 N0))) (real_pow (real_of_num ((BIT0 (BIT1 N0)))) n).
Axiom thm_REAL_POW2_ABS : forall x : real, (real_pow (real_abs x) ((BIT0 (BIT1 N0)))) = (real_pow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LE_SQUARE_ABS : forall x : real, forall y : real, (real_le (real_abs x) (real_abs y)) = (real_le (real_pow x ((BIT0 (BIT1 N0)))) (real_pow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_LT_SQUARE_ABS : forall x : real, forall y : real, (real_lt (real_abs x) (real_abs y)) = (real_lt (real_pow x ((BIT0 (BIT1 N0)))) (real_pow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_EQ_SQUARE_ABS : forall x : real, forall y : real, ((real_abs x) = (real_abs y)) = ((real_pow x ((BIT0 (BIT1 N0)))) = (real_pow y ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_LE_POW_2 : forall x : real, real_le (real_of_num (N0)) (real_pow x ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_LT_POW_2 : forall x : real, (real_lt (real_of_num (N0)) (real_pow x ((BIT0 (BIT1 N0))))) = (~ (x = (real_of_num (N0)))).
Axiom thm_REAL_SOS_EQ_0 : forall x : real, forall y : real, ((real_add (real_pow x ((BIT0 (BIT1 N0)))) (real_pow y ((BIT0 (BIT1 N0))))) = (real_of_num (N0))) = ((x = (real_of_num (N0))) /\ (y = (real_of_num (N0)))).
Axiom thm_REAL_POW_ZERO : forall n : N, (real_pow (real_of_num (N0)) n) = (@COND real (n = (N0)) (real_of_num ((BIT1 N0))) (real_of_num (N0))).
Axiom thm_REAL_POW_MONO_INV : forall m : N, forall n : N, forall x : real, ((real_le (real_of_num (N0)) x) /\ ((real_le x (real_of_num ((BIT1 N0)))) /\ (N.le n m))) -> real_le (real_pow x m) (real_pow x n).
Axiom thm_REAL_POW_LE2_REV : forall n : N, forall x : real, forall y : real, ((~ (n = (N0))) /\ ((real_le (real_of_num (N0)) y) /\ (real_le (real_pow x n) (real_pow y n)))) -> real_le x y.
Axiom thm_REAL_POW_LT2_REV : forall n : N, forall x : real, forall y : real, ((real_le (real_of_num (N0)) y) /\ (real_lt (real_pow x n) (real_pow y n))) -> real_lt x y.
Axiom thm_REAL_POW_EQ : forall n : N, forall x : real, forall y : real, ((~ (n = (N0))) /\ ((real_le (real_of_num (N0)) x) /\ ((real_le (real_of_num (N0)) y) /\ ((real_pow x n) = (real_pow y n))))) -> x = y.
Axiom thm_REAL_POW_EQ_ABS : forall n : N, forall x : real, forall y : real, ((~ (n = (N0))) /\ ((real_pow x n) = (real_pow y n))) -> (real_abs x) = (real_abs y).
Axiom thm_REAL_POW_EQ_1_IMP : forall x : real, forall n : N, ((~ (n = (N0))) /\ ((real_pow x n) = (real_of_num ((BIT1 N0))))) -> (real_abs x) = (real_of_num ((BIT1 N0))).
Axiom thm_REAL_POW_EQ_1 : forall x : real, forall n : N, ((real_pow x n) = (real_of_num ((BIT1 N0)))) = ((((real_abs x) = (real_of_num ((BIT1 N0)))) /\ ((real_lt x (real_of_num (N0))) -> N.Even n)) \/ (n = (N0))).
Axiom thm_REAL_POW_LT2_ODD : forall n : N, forall x : real, forall y : real, ((real_lt x y) /\ (N.Odd n)) -> real_lt (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LE2_ODD : forall n : N, forall x : real, forall y : real, ((real_le x y) /\ (N.Odd n)) -> real_le (real_pow x n) (real_pow y n).
Axiom thm_REAL_POW_LT2_ODD_EQ : forall n : N, forall x : real, forall y : real, (N.Odd n) -> (real_lt (real_pow x n) (real_pow y n)) = (real_lt x y).
Axiom thm_REAL_POW_LE2_ODD_EQ : forall n : N, forall x : real, forall y : real, (N.Odd n) -> (real_le (real_pow x n) (real_pow y n)) = (real_le x y).
Axiom thm_REAL_POW_EQ_ODD_EQ : forall n : N, forall x : real, forall y : real, (N.Odd n) -> ((real_pow x n) = (real_pow y n)) = (x = y).
Axiom thm_REAL_POW_EQ_ODD : forall n : N, forall x : real, forall y : real, ((N.Odd n) /\ ((real_pow x n) = (real_pow y n))) -> x = y.
Axiom thm_REAL_POW_EQ_EQ : forall n : N, forall x : real, forall y : real, ((real_pow x n) = (real_pow y n)) = (@COND Prop (N.Even n) ((n = (N0)) \/ ((real_abs x) = (real_abs y))) (x = y)).
Axiom thm_REAL_EVENPOW_ABS : forall x : real, forall n : N, (N.Even n) -> (real_pow (real_abs x) n) = (real_pow x n).
Axiom thm_REAL_OF_NUM_MOD : forall m : N, forall n : N, (real_of_num (N.modulo m n)) = (real_sub (real_of_num m) (real_mul (real_of_num (N.div m n)) (real_of_num n))).
Axiom thm_REAL_OF_NUM_DIV : forall m : N, forall n : N, (real_of_num (N.div m n)) = (real_sub (real_div (real_of_num m) (real_of_num n)) (real_div (real_of_num (N.modulo m n)) (real_of_num n))).
Axiom thm_REAL_CONVEX_BOUND2_LT : forall (b : real), forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_lt x a) /\ ((real_lt y b) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_lt (real_add (real_mul u x) (real_mul v y)) (real_add (real_mul u a) (real_mul v b)).
Axiom thm_REAL_CONVEX_BOUND2_LE : forall (b : real), forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_le x a) /\ ((real_le y b) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_le (real_add (real_mul u x) (real_mul v y)) (real_add (real_mul u a) (real_mul v b)).
Axiom thm_REAL_CONVEX_BOUND_LT : forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_lt x a) /\ ((real_lt y a) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_lt (real_add (real_mul u x) (real_mul v y)) a.
Axiom thm_REAL_CONVEX_BOUND_LE : forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_le x a) /\ ((real_le y a) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_le (real_add (real_mul u x) (real_mul v y)) a.
Axiom thm_REAL_CONVEX_BOUND_GT : forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_lt a x) /\ ((real_lt a y) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_lt a (real_add (real_mul u x) (real_mul v y)).
Axiom thm_REAL_CONVEX_BOUND_GE : forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_le a x) /\ ((real_le a y) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))) -> real_le a (real_add (real_mul u x) (real_mul v y)).
Axiom thm_REAL_CONVEX_BOUNDS_LE : forall x : real, forall y : real, forall a : real, forall b : real, forall u : real, forall v : real, ((real_le a x) /\ ((real_le x b) /\ ((real_le a y) /\ ((real_le y b) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))))) -> (real_le a (real_add (real_mul u x) (real_mul v y))) /\ (real_le (real_add (real_mul u x) (real_mul v y)) b).
Axiom thm_REAL_CONVEX_BOUNDS_LT : forall x : real, forall y : real, forall a : real, forall b : real, forall u : real, forall v : real, ((real_lt a x) /\ ((real_lt x b) /\ ((real_lt a y) /\ ((real_lt y b) /\ ((real_le (real_of_num (N0)) u) /\ ((real_le (real_of_num (N0)) v) /\ ((real_add u v) = (real_of_num ((BIT1 N0)))))))))) -> (real_lt a (real_add (real_mul u x) (real_mul v y))) /\ (real_lt (real_add (real_mul u x) (real_mul v y)) b).
Axiom thm_REAL_ARCH_SIMPLE : forall x : real, exists n : N, real_le x (real_of_num n).
Axiom thm_REAL_ARCH_LT : forall x : real, exists n : N, real_lt x (real_of_num n).
Axiom thm_REAL_ARCH : forall x : real, (real_lt (real_of_num (N0)) x) -> forall y : real, exists n : N, real_lt y (real_mul (real_of_num n) x).
Axiom thm_REAL_ARCH_INV : forall e : real, (real_lt (real_of_num (N0)) e) = (exists n : N, (~ (n = (N0))) /\ ((real_lt (real_of_num (N0)) (real_inv (real_of_num n))) /\ (real_lt (real_inv (real_of_num n)) e))).
Axiom thm_REAL_POW_LBOUND : forall x : real, forall n : N, (real_le (real_of_num (N0)) x) -> real_le (real_add (real_of_num ((BIT1 N0))) (real_mul (real_of_num n) x)) (real_pow (real_add (real_of_num ((BIT1 N0))) x) n).
Axiom thm_REAL_ARCH_POW : forall x : real, forall y : real, (real_lt (real_of_num ((BIT1 N0))) x) -> exists n : N, real_lt y (real_pow x n).
Axiom thm_REAL_ARCH_POW2 : forall x : real, exists n : N, real_lt x (real_pow (real_of_num ((BIT0 (BIT1 N0)))) n).
Axiom thm_REAL_ARCH_POW_INV : forall x : real, forall y : real, ((real_lt (real_of_num (N0)) y) /\ (real_lt x (real_of_num ((BIT1 N0))))) -> exists n : N, real_lt (real_pow x n) y.
Axiom thm_real_sgn : forall x : real, (real_sgn x) = (@COND real (real_lt (real_of_num (N0)) x) (real_of_num ((BIT1 N0))) (@COND real (real_lt x (real_of_num (N0))) (real_neg (real_of_num ((BIT1 N0)))) (real_of_num (N0)))).
Axiom thm_REAL_SGN_0 : (real_sgn (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_REAL_SGN_NEG : forall x : real, (real_sgn (real_neg x)) = (real_neg (real_sgn x)).
Axiom thm_REAL_SGN_ABS : forall x : real, (real_mul (real_sgn x) (real_abs x)) = x.
Axiom thm_REAL_SGN_ABS_ALT : forall x : real, (real_mul (real_sgn x) x) = (real_abs x).
Axiom thm_REAL_EQ_SGN_ABS : forall x : real, forall y : real, (x = y) = (((real_sgn x) = (real_sgn y)) /\ ((real_abs x) = (real_abs y))).
Axiom thm_REAL_ABS_SGN : forall x : real, (real_abs (real_sgn x)) = (real_sgn (real_abs x)).
Axiom thm_REAL_SGN : forall x : real, (real_sgn x) = (real_div x (real_abs x)).
Axiom thm_REAL_SGN_MUL : forall x : real, forall y : real, (real_sgn (real_mul x y)) = (real_mul (real_sgn x) (real_sgn y)).
Axiom thm_REAL_SGN_INV : forall x : real, (real_sgn (real_inv x)) = (real_sgn x).
Axiom thm_REAL_SGN_DIV : forall x : real, forall y : real, (real_sgn (real_div x y)) = (real_div (real_sgn x) (real_sgn y)).
Axiom thm_REAL_SGN_EQ : (forall x : real, ((real_sgn x) = (real_of_num (N0))) = (x = (real_of_num (N0)))) /\ ((forall x : real, ((real_sgn x) = (real_of_num ((BIT1 N0)))) = (real_gt x (real_of_num (N0)))) /\ (forall x : real, ((real_sgn x) = (real_neg (real_of_num ((BIT1 N0))))) = (real_lt x (real_of_num (N0))))).
Axiom thm_REAL_SGN_CASES : forall x : real, ((real_sgn x) = (real_of_num (N0))) \/ (((real_sgn x) = (real_of_num ((BIT1 N0)))) \/ ((real_sgn x) = (real_neg (real_of_num ((BIT1 N0)))))).
Axiom thm_REAL_SGN_INEQS : (forall x : real, (real_le (real_of_num (N0)) (real_sgn x)) = (real_le (real_of_num (N0)) x)) /\ ((forall x : real, (real_lt (real_of_num (N0)) (real_sgn x)) = (real_lt (real_of_num (N0)) x)) /\ ((forall x : real, (real_ge (real_of_num (N0)) (real_sgn x)) = (real_ge (real_of_num (N0)) x)) /\ ((forall x : real, (real_gt (real_of_num (N0)) (real_sgn x)) = (real_gt (real_of_num (N0)) x)) /\ ((forall x : real, ((real_of_num (N0)) = (real_sgn x)) = ((real_of_num (N0)) = x)) /\ ((forall x : real, (real_le (real_sgn x) (real_of_num (N0))) = (real_le x (real_of_num (N0)))) /\ ((forall x : real, (real_lt (real_sgn x) (real_of_num (N0))) = (real_lt x (real_of_num (N0)))) /\ ((forall x : real, (real_ge (real_sgn x) (real_of_num (N0))) = (real_ge x (real_of_num (N0)))) /\ ((forall x : real, (real_gt (real_sgn x) (real_of_num (N0))) = (real_gt x (real_of_num (N0)))) /\ (forall x : real, ((real_sgn x) = (real_of_num (N0))) = (x = (real_of_num (N0)))))))))))).
Axiom thm_REAL_SGN_POW : forall x : real, forall n : N, (real_sgn (real_pow x n)) = (real_pow (real_sgn x) n).
Axiom thm_REAL_SGN_POW_2 : forall x : real, (real_sgn (real_pow x ((BIT0 (BIT1 N0))))) = (real_sgn (real_abs x)).
Axiom thm_REAL_SGN_REAL_SGN : forall x : real, (real_sgn (real_sgn x)) = (real_sgn x).
Axiom thm_REAL_INV_SGN : forall x : real, (real_inv (real_sgn x)) = (real_sgn x).
Axiom thm_REAL_SGN_EQ_INEQ : forall x : real, forall y : real, ((real_sgn x) = (real_sgn y)) = ((x = y) \/ (real_lt (real_abs (real_sub x y)) (real_max (real_abs x) (real_abs y)))).
Axiom thm_REAL_SGNS_EQ : forall x : real, forall y : real, ((real_sgn x) = (real_sgn y)) = (((x = (real_of_num (N0))) = (y = (real_of_num (N0)))) /\ (((real_gt x (real_of_num (N0))) = (real_gt y (real_of_num (N0)))) /\ ((real_lt x (real_of_num (N0))) = (real_lt y (real_of_num (N0)))))).
Axiom thm_REAL_SGNS_EQ_ALT : forall x : real, forall y : real, ((real_sgn x) = (real_sgn y)) = (((x = (real_of_num (N0))) -> y = (real_of_num (N0))) /\ (((real_gt x (real_of_num (N0))) -> real_gt y (real_of_num (N0))) /\ ((real_lt x (real_of_num (N0))) -> real_lt y (real_of_num (N0))))).
Axiom thm_REAL_WLOG_LE : forall (P : real -> real -> Prop), ((forall x : real, forall y : real, (P x y) = (P y x)) /\ (forall x : real, forall y : real, (real_le x y) -> P x y)) -> forall x : real, forall y : real, P x y.
Axiom thm_REAL_WLOG_LT : forall (P : real -> real -> Prop), ((forall x : real, P x x) /\ ((forall x : real, forall y : real, (P x y) = (P y x)) /\ (forall x : real, forall y : real, (real_lt x y) -> P x y))) -> forall x : real, forall y : real, P x y.
Axiom thm_REAL_WLOG_LE_3 : forall P : real -> real -> real -> Prop, ((forall x : real, forall y : real, forall z : real, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le y z)) -> P x y z)) -> forall x : real, forall y : real, forall z : real, P x y z.
Axiom thm_sqrt : forall x : real, (sqrt x) = (@ε real (fun y : real => ((real_sgn y) = (real_sgn x)) /\ ((real_pow y ((BIT0 (BIT1 N0)))) = (real_abs x)))).
Axiom thm_SQRT_UNIQUE : forall x : real, forall y : real, ((real_le (real_of_num (N0)) y) /\ ((real_pow y ((BIT0 (BIT1 N0)))) = x)) -> (sqrt x) = y.
Axiom thm_POW_2_SQRT : forall x : real, (real_le (real_of_num (N0)) x) -> (sqrt (real_pow x ((BIT0 (BIT1 N0))))) = x.
Axiom thm_SQRT_0 : (sqrt (real_of_num (N0))) = (real_of_num (N0)).
Axiom thm_SQRT_1 : (sqrt (real_of_num ((BIT1 N0)))) = (real_of_num ((BIT1 N0))).
Axiom thm_POW_2_SQRT_ABS : forall x : real, (sqrt (real_pow x ((BIT0 (BIT1 N0))))) = (real_abs x).
Axiom thm_SQRT_WORKS_GEN : forall x : real, ((real_sgn (sqrt x)) = (real_sgn x)) /\ ((real_pow (sqrt x) ((BIT0 (BIT1 N0)))) = (real_abs x)).
Axiom thm_SQRT_UNIQUE_GEN : forall x : real, forall y : real, (((real_sgn y) = (real_sgn x)) /\ ((real_pow y ((BIT0 (BIT1 N0)))) = (real_abs x))) -> (sqrt x) = y.
Axiom thm_SQRT_NEG : forall x : real, (sqrt (real_neg x)) = (real_neg (sqrt x)).
Axiom thm_REAL_SGN_SQRT : forall x : real, (real_sgn (sqrt x)) = (real_sgn x).
Axiom thm_SQRT_WORKS : forall x : real, (real_le (real_of_num (N0)) x) -> (real_le (real_of_num (N0)) (sqrt x)) /\ ((real_pow (sqrt x) ((BIT0 (BIT1 N0)))) = x).
Axiom thm_REAL_POS_EQ_SQUARE : forall x : real, (real_le (real_of_num (N0)) x) = (exists y : real, (real_pow y ((BIT0 (BIT1 N0)))) = x).
Axiom thm_SQRT_POS_LE : forall x : real, (real_le (real_of_num (N0)) x) -> real_le (real_of_num (N0)) (sqrt x).
Axiom thm_SQRT_POW_2 : forall x : real, (real_le (real_of_num (N0)) x) -> (real_pow (sqrt x) ((BIT0 (BIT1 N0)))) = x.
Axiom thm_SQRT_POW2 : forall x : real, ((real_pow (sqrt x) ((BIT0 (BIT1 N0)))) = x) = (real_le (real_of_num (N0)) x).
Axiom thm_SQRT_MUL : forall x : real, forall y : real, (sqrt (real_mul x y)) = (real_mul (sqrt x) (sqrt y)).
Axiom thm_SQRT_INV : forall x : real, (sqrt (real_inv x)) = (real_inv (sqrt x)).
Axiom thm_SQRT_DIV : forall x : real, forall y : real, (sqrt (real_div x y)) = (real_div (sqrt x) (sqrt y)).
Axiom thm_SQRT_LT_0 : forall x : real, (real_lt (real_of_num (N0)) (sqrt x)) = (real_lt (real_of_num (N0)) x).
Axiom thm_SQRT_EQ_0 : forall x : real, ((sqrt x) = (real_of_num (N0))) = (x = (real_of_num (N0))).
Axiom thm_SQRT_LE_0 : forall x : real, (real_le (real_of_num (N0)) (sqrt x)) = (real_le (real_of_num (N0)) x).
Axiom thm_REAL_ABS_SQRT : forall x : real, (real_abs (sqrt x)) = (sqrt (real_abs x)).
Axiom thm_SQRT_MONO_LT : forall x : real, forall y : real, (real_lt x y) -> real_lt (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LE : forall x : real, forall y : real, (real_le x y) -> real_le (sqrt x) (sqrt y).
Axiom thm_SQRT_MONO_LT_EQ : forall x : real, forall y : real, (real_lt (sqrt x) (sqrt y)) = (real_lt x y).
Axiom thm_SQRT_MONO_LE_EQ : forall x : real, forall y : real, (real_le (sqrt x) (sqrt y)) = (real_le x y).
Axiom thm_SQRT_INJ : forall x : real, forall y : real, ((sqrt x) = (sqrt y)) = (x = y).
Axiom thm_SQRT_EQ_1 : forall x : real, ((sqrt x) = (real_of_num ((BIT1 N0)))) = (x = (real_of_num ((BIT1 N0)))).
Axiom thm_SQRT_POS_LT : forall x : real, (real_lt (real_of_num (N0)) x) -> real_lt (real_of_num (N0)) (sqrt x).
Axiom thm_REAL_LE_LSQRT : forall x : real, forall y : real, ((real_le (real_of_num (N0)) y) /\ (real_le x (real_pow y ((BIT0 (BIT1 N0)))))) -> real_le (sqrt x) y.
Axiom thm_REAL_LE_RSQRT : forall x : real, forall y : real, (real_le (real_pow x ((BIT0 (BIT1 N0)))) y) -> real_le x (sqrt y).
Axiom thm_REAL_LT_LSQRT : forall x : real, forall y : real, ((real_le (real_of_num (N0)) y) /\ (real_lt x (real_pow y ((BIT0 (BIT1 N0)))))) -> real_lt (sqrt x) y.
Axiom thm_REAL_LT_RSQRT : forall x : real, forall y : real, (real_lt (real_pow x ((BIT0 (BIT1 N0)))) y) -> real_lt x (sqrt y).
Axiom thm_SQRT_EVEN_POW2 : forall n : N, (N.Even n) -> (sqrt (real_pow (real_of_num ((BIT0 (BIT1 N0)))) n)) = (real_pow (real_of_num ((BIT0 (BIT1 N0)))) (N.div n ((BIT0 (BIT1 N0))))).
Axiom thm_REAL_DIV_SQRT : forall x : real, (real_le (real_of_num (N0)) x) -> (real_div x (sqrt x)) = (sqrt x).
Axiom thm_REAL_RSQRT_LE : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ ((real_le (real_of_num (N0)) y) /\ (real_le x (sqrt y)))) -> real_le (real_pow x ((BIT0 (BIT1 N0)))) y.
Axiom thm_REAL_LSQRT_LE : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le (sqrt x) y)) -> real_le x (real_pow y ((BIT0 (BIT1 N0)))).
Axiom thm_REAL_SQRT_POW_2 : forall x : real, (real_pow (sqrt x) ((BIT0 (BIT1 N0)))) = (real_abs x).
Axiom thm_REAL_ABS_LE_SQRT_POS : forall x : real, forall y : real, ((real_le (real_of_num (N0)) x) /\ (real_le (real_of_num (N0)) y)) -> real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_abs (real_sub x y))).
Axiom thm_REAL_ABS_LE_SQRT : forall x : real, forall y : real, real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_mul (real_of_num ((BIT0 (BIT1 N0)))) (real_abs (real_sub x y)))).
