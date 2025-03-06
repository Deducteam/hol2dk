(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

Record Type' := { type :> Type; el : type }.

Definition Prop' : Type' := {| type := Prop; el := True |}.
Canonical Prop'.

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

(****************************************************************************)
(* Proof of some HOL-Light rules. *)
(****************************************************************************)

Axiom or_intro1: forall {p:Prop} (h : p) (q:Prop), p \/ q.

Axiom or_intro2: forall (p:Prop) {q:Prop} (h : q), p \/ q.

Axiom or_elim: forall {p q : Prop} (h : p \/ q) {r : Prop} (h1: p -> r) (h2: q -> r), r.

Axiom ex_elim: forall {a} {p : a -> Prop}
  (h1 : exists x, p x) {r : Prop} (h2 : forall x : a, (p x) -> r), r.

Axiom MK_COMB :
  forall {a b : Type} {s t : a -> b} {u v : a} (h1 : s = t) (h2 : u = v),
    (s u) = (t v).

Axiom EQ_MP : forall {p q : Prop} (e : p = q) (h : p), q.

(****************************************************************************)
(* Coq axioms necessary to handle HOL-Light proofs. *)
(****************************************************************************)

Axiom ε : forall {A : Type'}, (type A -> Prop) -> type A.

Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.

Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Axiom axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.

Axiom axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).

(****************************************************************************)
(* Alignment of connectives. *)
(****************************************************************************)

Definition imp (p q : Prop) : Prop := p -> q.

Axiom imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).

Axiom ex1: forall {A : Type'}, (A -> Prop) -> Prop.

Axiom ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).

Axiom F_def : False = (forall p : Prop, p).

Axiom not_def : not = (fun p : Prop => p -> False).

Axiom or_def : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).

Axiom ex_def : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).

Axiom all_def : forall {A : Type'}, (@all A) = (fun P : A -> Prop => P = (fun x : A => True)).

Axiom and_def : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).

Axiom T_def : True = ((fun p : Prop => p) = (fun p : Prop => p)).

(****************************************************************************)
(* Miscellaneous. *)
(****************************************************************************)

Axiom COND : forall {A : Type'}, Prop -> A -> A -> A.

Axiom COND_def : forall {A : Type'}, (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).

Axiom GEQ : forall {A : Type'}, A -> A -> Prop.

Axiom GEQ_def : forall {A : Type'}, (@eq A) = (fun a : A => fun b : A => a = b).

Axiom GABS_def : forall {A : Type'}, (@ε A) = (fun P : A -> Prop => @ε A P).

Axiom _UNGUARDED_PATTERN_def : and = (fun p : Prop => fun r : Prop => p /\ r).

Axiom _FALSITY__def : False = False.

Axiom hashek_def : True = True.

Module Import ExtensionalityFacts.
  Axiom is_inverse: forall A B : Type, (A -> B) -> (B -> A) -> Prop.
End ExtensionalityFacts.

Axiom ISO_def: forall {A B : Type'}, (@is_inverse A B) = (fun _17569 : A -> B => fun _17570 : B -> A => (forall x : B, (_17569 (_17570 x)) = x) /\ (forall y : A, (_17570 (_17569 y)) = y)).

(****************************************************************************)
(* Alignment of the unit type. *)
(****************************************************************************)

Definition unit' := {| type := unit; el := tt |}.
Canonical unit'.

Axiom one_ABS : Prop -> unit.

Axiom one_REP : unit -> Prop.

Axiom axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a.

Axiom axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).

Axiom one_def : tt = @ε unit (fun y0 : unit => True).

(****************************************************************************)
(* Alignment of the product type constructor. *)
(****************************************************************************)

Definition prod' (a b : Type') := {| type := prod a b; el := pair (el a) (el b) |}.
Canonical prod'.

Axiom mk_pair : forall {A B : Type'}, A -> B -> A -> B -> Prop.

Axiom mk_pair_def : forall {A B : Type'}, (@mk_pair A B) = (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).

Axiom ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B.

Axiom REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop.

Axiom pair_def: forall {A B : Type'}, (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).

Axiom FST_def: forall {A B : Type'}, (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).

Axiom SND_def: forall {A B : Type'}, (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).

Axiom axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.

Axiom axiom_5 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).

(****************************************************************************)
(* Alignment of the infinite type ind. *)
(****************************************************************************)

Axiom ind : Type'.

Axiom ONE_ONE : forall {A B : Type'}, (A -> B) -> Prop.

Axiom ONE_ONE_def : forall {A B : Type'}, (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).

Axiom ONTO : forall {A B : Type'}, (A -> B) -> Prop.

Axiom ONTO_def : forall {A B : Type'}, (@ONTO A B) = (fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x)).

Axiom axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).

Axiom IND_SUC : ind -> ind.

Axiom IND_SUC_def : IND_SUC = (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))).

Axiom IND_0 : ind.

Axiom IND_0_def : IND_0 = (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))).

Axiom NUM_REP : ind -> Prop.

Axiom NUM_REP_def : NUM_REP = (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a).

(****************************************************************************)
(* Alignment of the type of natural numbers. *)
(****************************************************************************)

Axiom N : Type.

Axiom N0 : N.

Module N.
  Axiom succ : N -> N.
  Axiom pred : N -> N.
  Axiom double : N -> N.
  Axiom mul : N -> N -> N.
  Axiom add : N -> N -> N.
  Axiom sub : N -> N -> N.
  Axiom lt : N -> N -> Prop.
  Axiom le : N -> N -> Prop.
  Axiom gt : N -> N -> Prop.
  Axiom ge : N -> N -> Prop.
  Axiom pow : N -> N -> N.
  Axiom max : N -> N -> N.
  Axiom min : N -> N -> N.
  Axiom div : N -> N -> N.
  Axiom modulo : N -> N -> N.
  Axiom Even : N -> Prop.
  Axiom Odd : N -> Prop.
End N.

Definition N' := {| type := N; el := N0 |}.
Canonical N'.

Axiom dest_num : N -> ind.

Axiom mk_num : ind -> N.

Axiom axiom_7 : forall (a : N), (mk_num (dest_num a)) = a.

Axiom axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).

Axiom _0_def : N0 = (mk_num IND_0).

Axiom SUC_def : N.succ = (fun _2104 : N => mk_num (IND_SUC (dest_num _2104))).

(****************************************************************************)
(* Alignment of mathematical functions on natural numbers with N. *)
(****************************************************************************)

Axiom NUMERAL : N -> N.

Axiom NUMERAL_def : NUMERAL = (fun _2128 : N => _2128).

Axiom BIT0 : N -> N.

Axiom BIT0_def : BIT0 = @ε (arr N N') (fun y0 : N -> N => ((y0 (NUMERAL N0)) = (NUMERAL N0)) /\ (forall y1 : N, (y0 (N.succ y1)) = (N.succ (N.succ (y0 y1))))).

Axiom BIT1 : N -> N.

Axiom BIT1_def : BIT1 = (fun _2143 : N => N.succ (BIT0 _2143)).

Axiom PRE_def : N.pred = (@ε (arr (prod N (prod N N)) (arr N N')) (fun PRE' : (prod N (prod N N)) -> N -> N' => forall _2151 : prod N (prod N N), ((PRE' _2151 (NUMERAL N0)) = (NUMERAL N0)) /\ (forall n : N, (PRE' _2151 (N.succ n)) = n)) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))).

Axiom add_def : N.add = (@ε (arr N (arr N (arr N N'))) (fun add' : N -> N -> N -> N => forall _2155 : N, (forall n : N, (add' _2155 (NUMERAL N0) n) = n) /\ (forall m : N, forall n : N, (add' _2155 (N.succ m) n) = (N.succ (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))).

Axiom mul_def : N.mul = (@ε (arr N (arr N (arr N N'))) (fun mul' : N -> N -> N -> N => forall _2186 : N, (forall n : N, (mul' _2186 (NUMERAL N0) n) = (NUMERAL N0)) /\ (forall m : N, forall n : N, (mul' _2186 (N.succ m) n) = (N.add (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))).

Axiom EXP_def : N.pow = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun EXP' : (prod N (prod N N)) -> N -> N -> N => forall _2224 : prod N (prod N N), (forall m : N, EXP' _2224 m (NUMERAL N0) = NUMERAL (BIT1 N0)) /\ (forall m : N, forall n : N, (EXP' _2224 m (N.succ n)) = (N.mul m (EXP' _2224 m n)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).

Axiom le_def : N.le = (@ε (arr (prod N N) (arr N (arr N Prop'))) (fun le' : (prod N N) -> N -> N -> Prop => forall _2241 : prod N N, (forall m : N, (le' _2241 m (NUMERAL N0)) = (m = (NUMERAL N0))) /\ (forall m : N, forall n : N, (le' _2241 m (N.succ n)) = ((m = (N.succ n)) \/ (le' _2241 m n)))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0))))))))).

Axiom lt_def : N.lt = (@ε (arr N (arr N (arr N Prop'))) (fun lt : N -> N -> N -> Prop => forall _2248 : N, (forall m : N, (lt _2248 m (NUMERAL N0)) = False) /\ (forall m : N, forall n : N, (lt _2248 m (N.succ n)) = ((m = n) \/ (lt _2248 m n)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))).

Axiom ge_def : N.ge = (fun _2249 : N => fun _2250 : N => N.le _2250 _2249).

Axiom gt_def : N.gt = (fun _2261 : N => fun _2262 : N => N.lt _2262 _2261).

Axiom MAX_def : N.max = (fun _2273 : N => fun _2274 : N => @COND N (N.le _2273 _2274) _2274 _2273).

Axiom MIN_def : N.min = (fun _2285 : N => fun _2286 : N => @COND N (N.le _2285 _2286) _2285 _2286).

Axiom minus_def : N.sub = (@ε (arr N (arr N (arr N N'))) (fun pair' : N -> N -> N -> N => forall _2766 : N, (forall m : N, (pair' _2766 m (NUMERAL N0)) = m) /\ (forall m : N, forall n : N, (pair' _2766 m (N.succ n)) = (N.pred (pair' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))).

Axiom fact : N -> N.

Axiom FACT_def : fact = @ε ((prod N (prod N (prod N N))) -> N -> N) (fun FACT' : (prod N (prod N (prod N N))) -> N -> N => forall _2944 : prod N (prod N (prod N N)), ((FACT' _2944 (NUMERAL N0)) = (NUMERAL (BIT1 N0))) /\ (forall n : N, (FACT' _2944 (N.succ n)) = (N.mul (N.succ n) (FACT' _2944 n)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).

Axiom DIV_def : N.div = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun q : (prod N (prod N N)) -> N -> N -> N => forall _3086 : prod N (prod N N), exists r : N -> N -> N, forall m : N, forall n : N, @COND Prop (n = (NUMERAL N0)) (((q _3086 m n) = (NUMERAL N0)) /\ ((r m n) = m)) ((m = (N.add (N.mul (q _3086 m n) n) (r m n))) /\ (N.lt (r m n) n))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).

Axiom MOD_def : N.modulo = (@ε (arr (prod N (prod N N)) (arr N (arr N N'))) (fun r : (prod N (prod N N)) -> N -> N -> N => forall _3087 : prod N (prod N N), forall m : N, forall n : N, @COND Prop (n = (NUMERAL N0)) (((N.div m n) = (NUMERAL N0)) /\ ((r _3087 m n) = m)) ((m = (N.add (N.mul (N.div m n) n) (r _3087 m n))) /\ (N.lt (r _3087 m n) n))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))).

Axiom EVEN_def : N.Even = @ε ((prod N (prod N (prod N N))) -> N -> Prop) (fun EVEN' : (prod N (prod N (prod N N))) -> N -> Prop => forall _2603 : prod N (prod N (prod N N)), ((EVEN' _2603 (NUMERAL N0)) = True) /\ (forall n : N, (EVEN' _2603 (N.succ n)) = (~ (EVEN' _2603 n)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).

Axiom ODD_def: N.Odd = @ε ((prod N (prod N N)) -> N -> Prop) (fun ODD' : (prod N (prod N N)) -> N -> Prop => forall _2607 : prod N (prod N N), ((ODD' _2607 (NUMERAL N0)) = False) /\ (forall n : N, (ODD' _2607 (N.succ n)) = (~ (ODD' _2607 n)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))).

(****************************************************************************)
(* Alignment of recspace, the HOL-Light type used to encode inductive types. *)
(****************************************************************************)

Axiom NUMPAIR : N -> N -> N.

Axiom NUMPAIR_def : NUMPAIR = (fun _17487 : N => fun _17488 : N => N.mul (N.pow (NUMERAL (BIT0 (BIT1 N0))) _17487) (N.add (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17488) (NUMERAL (BIT1 N0)))).

Axiom NUMFST : N -> N.

Axiom NUMFST_def : NUMFST = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun X : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17503 : prod N (prod N (prod N (prod N (prod N N)))), exists Y : N -> N, forall x : N, forall y : N, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).

Axiom NUMSND : N -> N.

Axiom NUMSND_def : NUMSND = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> N => forall _17504 : prod N (prod N (prod N (prod N (prod N N)))), forall x : N, forall y : N, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).

Axiom NUMSUM : Prop -> N -> N.

Axiom NUMSUM_def : NUMSUM = (fun _17505 : Prop => fun _17506 : N => @COND N _17505 (N.succ (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17506)) (N.mul (NUMERAL (BIT0 (BIT1 N0))) _17506)).

Axiom NUMLEFT : N -> Prop.

Axiom NUMLEFT_def : NUMLEFT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop) (fun X : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop => forall _17372 : prod N (prod N (prod N (prod N (prod N (prod N N))))), exists Y : N -> N, forall x : Prop, forall y : N, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))))).

Axiom NUMRIGHT : N -> N.

Axiom NUMRIGHT_def : NUMRIGHT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N => forall _17373 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), forall x : Prop, forall y : N, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))))).

Axiom INJN : forall {A : Type'}, N -> N -> A -> Prop.

Axiom INJN_def : forall {A : Type'}, (@INJN A) = (fun _17537 : N => fun n : N => fun a : A => n = _17537).

Axiom INJP : forall {A : Type'}, (N -> A -> Prop) -> (N -> A -> Prop) -> N -> A -> Prop.

Axiom INJP_def : forall {A : Type'}, (@INJP A) = (fun _17554 : N -> A -> Prop => fun _17555 : N -> A -> Prop => fun n : N => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)).

Axiom INJA : forall {A : Type'}, A -> N -> A -> Prop.

Axiom INJA_def : forall {A : Type'}, (@INJA A) = (fun _17542 : A => fun n : N => fun b : A => b = _17542).

Axiom INJF : forall {A : Type'}, (N -> N -> A -> Prop) -> N -> A -> Prop.

Axiom INJF_def : forall {A : Type'}, (@INJF A) = (fun _17549 : N -> N -> A -> Prop => fun n : N => _17549 (NUMFST n) (NUMSND n)).

Axiom ZRECSPACE: forall {A : Type'}, (N -> A -> Prop) -> Prop.

Axiom ZCONSTR: forall {A : Type'}, N -> A -> (N -> N -> A -> Prop) -> N -> A -> Prop.

Axiom ZCONSTR_def : forall {A : Type'}, (@ZCONSTR A) = (fun _17566 : N => fun _17567 : A => fun _17568 : N -> N -> A -> Prop => @INJP A (@INJN A (N.succ _17566)) (@INJP A (@INJA A _17567) (@INJF A _17568))).

Axiom ZBOT: forall {A : Type'}, N -> A -> Prop.

Axiom ZBOT_def : forall {A : Type'}, (@ZBOT A) = (@INJP A (@INJN A (NUMERAL N0)) (@ε (N -> A -> Prop) (fun z : N -> A -> Prop => True))).

Axiom ZRECSPACE_def: forall {A : Type'}, (@ZRECSPACE A) = (fun a : N -> A -> Prop => forall ZRECSPACE' : (N -> A -> Prop) -> Prop, (forall a' : N -> A -> Prop, ((a' = (@ZBOT A)) \/ (exists c : N, exists i : A, exists r : N -> N -> A -> Prop, (a' = (@ZCONSTR A c i r)) /\ (forall n : N, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a).

Axiom recspace : Type' -> Type'.

Axiom _dest_rec : forall {A : Type'}, (recspace A) -> N -> A -> Prop.

Axiom _mk_rec : forall {A : Type'}, (N -> A -> Prop) -> recspace A.

Axiom axiom_10 : forall {A : Type'} (r : N -> A -> Prop), (@ZRECSPACE A r) = ((@_dest_rec A (@_mk_rec A r)) = r).

Axiom axiom_9 : forall {A : Type'} (a : recspace A), (@_mk_rec A (@_dest_rec A a)) = a.

Axiom BOTTOM: forall {A : Type'}, recspace A.

Axiom BOTTOM_def : forall {A : Type'}, (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).

Axiom CONSTR: forall {A : Type'}, N -> A -> (N -> recspace A) -> recspace A.

Axiom CONSTR_def : forall {A : Type'}, (@CONSTR A) = (fun _17591 : N => fun _17592 : A => fun _17593 : N -> recspace A => @_mk_rec A (@ZCONSTR A _17591 _17592 (fun n : N => @_dest_rec A (_17593 n)))).

(****************************************************************************)
(* Alignment of well-foundedness. *)
(****************************************************************************)

Axiom well_founded : forall A : Type, (A -> A -> Prop) -> Prop.

Axiom WF_def : forall {A : Type'}, (@well_founded A) = (fun _6923 : A -> A -> Prop => forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (_6923 y x) -> ~ (P y))).

(****************************************************************************)
(* Alignment of the sum type constructor. *)
(****************************************************************************)

Definition sum' (A B : Type') : Type' := {| type:= sum A B; el := inl (el A) |}.
Canonical sum'.

Axiom _dest_sum : forall {A B : Type'}, sum A B -> recspace (prod A B).

Axiom _mk_sum : forall {A B : Type'}, recspace (prod A B) -> sum A B.

Axiom axiom_11 : forall {A B : Type'} (a : sum A B), (@_mk_sum A B (@_dest_sum A B a)) = a.

Axiom axiom_12 : forall {A B : Type'} (r : recspace (prod A B)), ((fun a : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = ((fun a''' : A => @CONSTR (prod A B) (NUMERAL N0) (@pair A B a''' (@ε B (fun v : B => True))) (fun n : N => @BOTTOM (prod A B))) a'')) \/ (exists a'' : B, a' = ((fun a''' : B => @CONSTR (prod A B) (N.succ (NUMERAL N0)) (@pair A B (@ε A (fun v : A => True)) a''') (fun n : N => @BOTTOM (prod A B))) a''))) -> sum' a') -> sum' a) r) = ((@_dest_sum A B (@_mk_sum A B r)) = r).

Axiom INL_def: forall {A B : Type'}, (@inl A B) = (fun a : A => @_mk_sum A B ((fun a' : A => @CONSTR (prod A B) (NUMERAL N0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : N => @BOTTOM (prod A B))) a)).

Axiom INR_def: forall {A B : Type'}, (@inr A B) = (fun a : B => @_mk_sum A B ((fun a' : B => @CONSTR (prod A B) (N.succ (NUMERAL N0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : N => @BOTTOM (prod A B))) a)).

(****************************************************************************)
(* Alignment of the option type constructor. *)
(****************************************************************************)

Definition option' (A : Type') := {| type := option A; el := None |}.
Canonical option'.

Axiom _dest_option : forall {A : Type'}, option A -> recspace A.

Axiom _mk_option : forall {A : Type'}, (recspace A) -> option A.

Axiom axiom_13 : forall {A : Type'} (a : option A), (@_mk_option A (@_dest_option A a)) = a.

Axiom axiom_14 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (N.succ (NUMERAL N0)) a''' (fun n : N => @BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((@_dest_option A (@_mk_option A r)) = r).

Axiom NONE_def: forall {A : Type'}, (@None A) = (@_mk_option A (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))).

Axiom SOME_def: forall {A : Type'}, (@Some A) = (fun a : A => @_mk_option A ((fun a' : A => @CONSTR A (N.succ (NUMERAL N0)) a' (fun n : N => @BOTTOM A)) a)).

(****************************************************************************)
(* Alignment of the list type constructor. *)
(****************************************************************************)

Axiom FCONS: forall {A : Type'} (a : A) (f: N -> A) (n : N), A.

Axiom FCONS_def: forall {A : Type'}, @FCONS A = @ε ((prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A) (fun FCONS' : (prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A => forall _17460 : prod N (prod N (prod N (prod N N))), (forall a : A, forall f : N -> A, (FCONS' _17460 a f (NUMERAL N0)) = a) /\ (forall a : A, forall f : N -> A, forall n : N, (FCONS' _17460 a f (N.succ n)) = (f n))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).

Definition list' (A : Type') := {| type := list A; el := nil |}.
Canonical list'.

Axiom _dest_list: forall {A : Type'} (l: list A), recspace A.

Axiom _mk_list : forall {A : Type'}, (recspace A) -> list A.

Axiom axiom_15 : forall {A : Type'} (a : list A), (@_mk_list A (@_dest_list A a)) = a.

Axiom axiom_16 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall list' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => @CONSTR A (N.succ (NUMERAL N0)) a0' (@FCONS (recspace A) a1' (fun n : N => @BOTTOM A))) a0 a1)) /\ (list' a1))) -> list' a') -> list' a) r) = ((@_dest_list A (@_mk_list A r)) = r).

Module List.
  Axiom rev : forall A, list A -> list A.
  Axiom map : forall A B, (A -> B) -> list A -> list B.
  Axiom removelast : forall A, list A -> list A.
  Axiom Forall : forall A, (A -> Prop) -> list A -> Prop.
  Axiom ForallOrdPairs : forall A, (A -> A -> Prop) -> list A -> Prop.
  Axiom In : forall A, A -> list A -> Prop.
End List.

Axiom NIL_def: forall {A : Type'}, (@nil A) = (@_mk_list A (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))).

Axiom CONS_def: forall {A : Type'}, (@cons A) = (fun a0 : A => fun a1 : list A => @_mk_list A ((fun a0' : A => fun a1' : recspace A => @CONSTR A (N.succ (NUMERAL N0)) a0' (@FCONS (recspace A) a1' (fun n : N => @BOTTOM A))) a0 (@_dest_list A a1))).

Axiom APPEND_def: forall {A : Type'}, (@app A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list' A) -> (list' A) -> list' A) (fun APPEND' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list A) -> (list A) -> list A => forall _17935 : prod N (prod N (prod N (prod N (prod N N)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).

Axiom REVERSE_def: forall {A : Type'}, (@List.rev A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list' A) -> list' A) (fun REVERSE' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list A) -> list A => forall _17939 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@app A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))))).

Axiom MAP_def: forall {A B : Type'}, (@List.map A B) = (@ε ((prod N (prod N N)) -> (A -> B) -> (list' A) -> list' B) (fun MAP' : (prod N (prod N N)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod N (prod N N), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).

Axiom BUTLAST_def: forall {_25251 : Type'}, (@List.removelast _25251) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list' _25251) -> list' _25251) (fun BUTLAST' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (list _25251) -> list _25251 => forall _17958 : prod N (prod N (prod N (prod N (prod N (prod N N))))), ((BUTLAST' _17958 (@nil _25251)) = (@nil _25251)) /\ (forall h : _25251, forall t : list _25251, (BUTLAST' _17958 (@cons _25251 h t)) = (@COND (list' _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (BUTLAST' _17958 t))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))))).

Axiom ALL_def: forall {_25307 : Type'}, (@List.Forall _25307) = (@ε ((prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop) (fun ALL' : (prod N (prod N N)) -> (_25307 -> Prop) -> (list _25307) -> Prop => forall _17973 : prod N (prod N N), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : list _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).

Axiom PAIRWISE_def: forall {A : Type'}, (@List.ForallOrdPairs A) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop) (fun PAIRWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (A -> A -> Prop) -> (list A) -> Prop => forall _18057 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18057 r (@nil A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : list A, (PAIRWISE' _18057 r (@cons A h t)) = ((@List.Forall A (r h) t) /\ (PAIRWISE' _18057 r t)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).

Axiom MEM_def: forall {_25376 : Type'}, (@List.In _25376) = (@ε ((prod N (prod N N)) -> _25376 -> (list _25376) -> Prop) (fun MEM' : (prod N (prod N N)) -> _25376 -> (list _25376) -> Prop => forall _17995 : prod N (prod N N), (forall x : _25376, (MEM' _17995 x (@nil _25376)) = False) /\ (forall h : _25376, forall x : _25376, forall t : list _25376, (MEM' _17995 x (@cons _25376 h t)) = ((x = h) \/ (MEM' _17995 x t)))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).

Axiom hd: forall {A:Type'}, list A -> A.

Axiom HD_def: forall {A : Type'}, @hd A = @ε ((prod N N) -> (list A) -> A) (fun HD' : (prod N N) -> (list A) -> A => forall _17927 : prod N N, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))).

Axiom tl: forall {A : Type'} (l : list A), list A.

Axiom TL_def: forall {A : Type'}, @tl A = (@ε ((prod N N) -> (list A) -> list A) (fun TL' : (prod N N) -> (list A) -> list A => forall _17931 : prod N N, forall h : A, forall t : list A, (TL' _17931 (@cons A h t)) = t) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))).

(****************************************************************************)
(* Alignment of the type of ASCII characters. *)
(****************************************************************************)

Module Import Ascii.
  Axiom ascii : Type.
  Axiom zero: ascii.
End Ascii.

Definition ascii' := {| type := ascii; el := zero |}.
Canonical ascii'.

Axiom _dest_char : ascii -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))).

Axiom _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> ascii.

Axiom axiom_17 : forall (a : ascii), (_mk_char (_dest_char a)) = a.

Axiom axiom_18 : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))), ((fun a : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) => forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' =
((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) = ((_dest_char (_mk_char r)) = r).

(*****************************************************************************)
(* Alignment of the type nadd of nearly additive sequences of naturals. *)
(*****************************************************************************)

Axiom dist : prod N N -> N.

Axiom dist_def : dist = (fun _22947 : prod N N => N.add (N.sub (@fst N N _22947) (@snd N N _22947)) (N.sub (@snd N N _22947) (@fst N N _22947))).

Axiom is_nadd : (N -> N) -> Prop.

Axiom is_nadd_def : is_nadd = (fun _23257 : N -> N => exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (_23257 n)) (N.mul n (_23257 m)))) (N.mul B (N.add m n))).

Axiom nadd : Type'.

Axiom mk_nadd: (N -> N) -> nadd.

Axiom dest_nadd: nadd -> (N -> N).

Axiom axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.

Axiom axiom_20 : forall (r : N -> N), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).

Axiom nadd_of_num : N -> nadd.

Axiom nadd_of_num_def : nadd_of_num = (fun _23288 : N => mk_nadd (fun n : N => N.mul _23288 n)).

Axiom nadd_le : nadd -> nadd -> Prop.

Axiom nadd_le_def : nadd_le = (fun _23295 : nadd => fun _23296 : nadd => exists B : N, forall n : N, N.le (dest_nadd _23295 n) (N.add (dest_nadd _23296 n) B)).

Axiom nadd_add : nadd -> nadd -> nadd.

Axiom nadd_add_def : nadd_add = (fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : N => N.add (dest_nadd _23311 n) (dest_nadd _23312 n))).

Axiom nadd_mul : nadd -> nadd -> nadd.

Axiom nadd_mul_def : nadd_mul = (fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : N => dest_nadd _23325 (dest_nadd _23326 n))).

Axiom nadd_rinv : nadd -> N -> N.

Axiom nadd_rinv_def : nadd_rinv = (fun _23462 : nadd => fun n : N => N.div (N.mul n n) (dest_nadd _23462 n)).

Axiom nadd_eq : nadd -> nadd -> Prop.

Axiom nadd_eq_def : nadd_eq = (fun _23276 : nadd => fun _23277 : nadd => exists B : N, forall n : N, N.le (dist (@pair N N (dest_nadd _23276 n) (dest_nadd _23277 n))) B).

Axiom nadd_inv : nadd -> nadd.

Axiom nadd_inv_def : nadd_inv = (fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL N0))) (nadd_of_num (NUMERAL N0)) (mk_nadd (nadd_rinv _23476))).

(*****************************************************************************)
(* Alignment of the type hreal of non-negative real numbers. *)
(*****************************************************************************)

Axiom hreal : Type'.

Axiom mk_hreal : (nadd -> Prop) -> hreal.

Axiom dest_hreal : hreal -> (nadd -> Prop).

Axiom axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.

Axiom axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).

Axiom hreal_of_num : N -> hreal.

Axiom hreal_of_num_def : hreal_of_num = (fun m : N => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)).

Axiom hreal_add : hreal -> hreal -> hreal.

Axiom hreal_add_def : hreal_add = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).

Axiom hreal_mul : hreal -> hreal -> hreal.

Axiom hreal_mul_def : hreal_mul = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).

Axiom hreal_le : hreal -> hreal -> Prop.

Axiom hreal_le_def : hreal_le = (fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).

Axiom hreal_inv : hreal -> hreal.

Axiom hreal_inv_def : hreal_inv = (fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x'))).

(*****************************************************************************)
(* Operations on treal (pairs of hreal's). *)
(*****************************************************************************)

Axiom treal_of_num : N -> prod hreal hreal.

Axiom treal_of_num_def : treal_of_num = (fun _23721 : N => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL N0))).

Axiom treal_neg : prod hreal hreal -> prod hreal hreal.

Axiom treal_neg_def : treal_neg = (fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726)).

Axiom treal_add : prod hreal hreal -> prod hreal hreal -> prod hreal hreal.

Axiom treal_add_def : treal_add = (fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736))).

Axiom treal_mul : prod hreal hreal -> prod hreal hreal -> prod hreal hreal.

Axiom treal_mul_def : treal_mul = (fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758)))).

Axiom treal_le : prod hreal hreal -> prod hreal hreal -> Prop.

Axiom treal_le_def : treal_le = (fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779))).

Axiom treal_inv : prod hreal hreal -> prod hreal hreal.

Axiom treal_inv_def : treal_inv = (fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_of_num (NUMERAL N0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL N0))) (@pair hreal hreal (hreal_of_num (NUMERAL N0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d))))))).

Axiom treal_eq : prod hreal hreal -> prod hreal hreal -> Prop.

Axiom treal_eq_def : treal_eq = (fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810))).

(*****************************************************************************)
(* Alignment of the type of real numbers. *)
(*****************************************************************************)

Axiom R : Type'.

Axiom mk_real : (prod' hreal hreal -> Prop) -> R.

Axiom dest_real : R -> (prod' hreal hreal -> Prop).

Axiom axiom_23 : forall (a : R), (mk_real (dest_real a)) = a.

Axiom axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).

Axiom Rle : R -> R -> Prop.

Axiom real_le_def : Rle = (fun x1 : R => fun y1 : R => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).

Axiom Rplus : R -> R -> R.

Axiom real_add_def : Rplus = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).

Axiom Rmult : R -> R -> R.

Axiom real_mul_def : Rmult = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).

Axiom Rinv : R -> R.

Axiom real_inv_def : Rinv = (fun x : R => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x'))).

Axiom Ropp : R -> R.

Axiom real_neg_def : Ropp = (fun x1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1'))).

Axiom R_of_N : N -> R.

Axiom real_of_num_def : R_of_N = (fun m : N => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).

Axiom Rabs : R -> R.

Axiom real_abs_def :
  Rabs = (fun y0 : R => @COND R (Rle (R_of_N (NUMERAL N0)) y0) y0 (Ropp y0)).

Axiom Rdiv : R -> R -> R.

Axiom real_div_def : Rdiv = (fun y0 : R => fun y1 : R => Rmult y0 (Rinv y1)).

Axiom Rminus : R -> R -> R.

Axiom real_sub_def : Rminus = (fun y0 : R => fun y1 : R => Rplus y0 (Ropp y1)).

Axiom Rge : R -> R -> Prop.

Axiom real_ge_def : Rge = (fun y0 : R => fun y1 : R => Rle y1 y0).

Axiom Rlt : R -> R -> Prop.

Axiom real_lt_def : Rlt = (fun y0 : R => fun y1 : R => ~ (Rle y1 y0)).

Axiom Rgt : R -> R -> Prop.

Axiom real_gt_def : Rgt = (fun y0 : R => fun y1 : R => Rlt y1 y0).

Axiom Rmax : R -> R -> R.

Axiom real_max_def : Rmax = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y1 y0).

Axiom Rmin : R -> R -> R.

Axiom real_min_def : Rmin = (fun y0 : R => fun y1 : R => @COND R (Rle y0 y1) y0 y1).

Axiom Rpow : R -> N -> R.

Axiom real_pow_def : Rpow = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R) (fun real_pow' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> R -> N -> R => forall _24085 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : R, (real_pow' _24085 x (NUMERAL N0)) = (R_of_N (NUMERAL (BIT1 N0)))) /\ (forall x : R, forall n : N, (real_pow' _24085 x (N.succ n)) = (Rmult x (real_pow' _24085 x n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))).

Axiom Rsgn : R -> R.

Axiom real_sgn_def : Rsgn = (fun _26598 : R => @COND R (Rlt (R_of_N (NUMERAL N0)) _26598) (R_of_N (NUMERAL (BIT1 N0))) (@COND R (Rlt _26598 (R_of_N (NUMERAL N0))) (Ropp (R_of_N (NUMERAL (BIT1 N0)))) (R_of_N (NUMERAL N0)))).

(*****************************************************************************)
(* Mapping of integers. *)
(*****************************************************************************)

Axiom Z : Type.

Axiom Z0 : Z.

Definition Z' := {| type := Z; el := Z0 |}.
Canonical Z'.

Axiom IZR : Z -> R.

Axiom int_of_real : R -> Z.

Axiom axiom_25 : forall (a : Z), (int_of_real (IZR a)) = a.

Axiom integer : R -> Prop.

Axiom integer_def : integer = (fun _28715 : R => exists n : N, (Rabs _28715) = (R_of_N n)).

Axiom axiom_26 : forall (r : R), ((fun x : R => integer x) r) = ((IZR (int_of_real r)) = r).

Axiom Z_of_N : N -> Z.

Axiom int_of_num_def : Z_of_N = (fun _28789 : N => int_of_real (R_of_N _28789)).

Module Z.
  Axiom le : Z -> Z -> Prop.
  Axiom lt : Z -> Z -> Prop.
  Axiom ge : Z -> Z -> Prop.
  Axiom gt : Z -> Z -> Prop.
  Axiom opp : Z -> Z.
  Axiom add : Z -> Z -> Z.
  Axiom sub : Z -> Z -> Z.
  Axiom mul : Z -> Z -> Z.
  Axiom abs : Z -> Z.
  Axiom sgn : Z -> Z.
  Axiom max : Z -> Z -> Z.
  Axiom min : Z -> Z -> Z.
  Axiom divide : Z -> Z -> Prop.
End Z.

Axiom int_le_def :
  Z.le = (fun _28741 : Z => fun _28742 : Z => Rle (IZR _28741) (IZR _28742)).

Axiom int_lt_def :
  Z.lt = (fun _28753 : Z => fun _28754 : Z => Rlt (IZR _28753) (IZR _28754)).

Axiom int_ge_def :
  Z.ge = (fun _28765 : Z => fun _28766 : Z => Rge (IZR _28765) (IZR _28766)).

Axiom int_gt_def :
  Z.gt = (fun _28777 : Z => fun _28778 : Z => Rgt (IZR _28777) (IZR _28778)).

Axiom int_neg_def :
  Z.opp = (fun _28794 : Z => int_of_real (Ropp (IZR _28794))).

Axiom int_add_def :
  Z.add = (fun _28803 : Z => fun _28804 : Z => int_of_real (Rplus (IZR _28803) (IZR _28804))).

Axiom int_sub_def :
  Z.sub = (fun _28835 : Z => fun _28836 : Z => int_of_real (Rminus (IZR _28835) (IZR _28836))).

Axiom int_mul_def :
  Z.mul =
  (fun _28847 : Z => fun _28848 : Z => int_of_real (Rmult (IZR _28847) (IZR _28848))).

Axiom int_abs_def :
  Z.abs = (fun _28867 : Z => int_of_real (Rabs (IZR _28867))).

Axiom int_sgn_def :
  Z.sgn = (fun _28878 : Z => int_of_real (Rsgn (IZR _28878))).

Axiom int_max_def :
  Z.max = (fun _28938 : Z => fun _28939 : Z => int_of_real (Rmax (IZR _28938) (IZR _28939))).

Axiom int_min_def :
  Z.min = (fun _28956 : Z => fun _28957 : Z => int_of_real (Rmin (IZR _28956) (IZR _28957))).

Axiom Zpow : Z -> N -> Z.

Axiom int_pow_def :
  Zpow = (fun _28974 : Z => fun _28975 : N => int_of_real (Rpow (IZR _28974) _28975)).

Axiom Zdiv : Z -> Z -> Z.

Axiom Zrem : Z -> Z -> Z.

Axiom div_def :
  Zdiv = (@ε ((prod N (prod N N)) -> Z -> Z -> Z) (fun q : (prod N (prod N N)) -> Z -> Z -> Z => forall _29326 : prod N (prod N N), exists r : Z -> Z -> Z, forall m : Z, forall n : Z, @COND Prop (n = (Z_of_N (NUMERAL N0))) (((q _29326 m n) = (Z_of_N (NUMERAL N0))) /\ ((r m n) = m)) ((Z.le (Z_of_N (NUMERAL N0)) (r m n)) /\ ((Z.lt (r m n) (Z.abs n)) /\ (m = (Z.add (Z.mul (q _29326 m n) n) (r m n)))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0))))))))))).

Axiom rem_def :
  Zrem = (@ε ((prod N (prod N N)) -> Z -> Z -> Z) (fun r : (prod N (prod N N)) -> Z -> Z -> Z => forall _29327 : prod N (prod N N), forall m : Z, forall n : Z, @COND Prop (n = (Z_of_N (NUMERAL N0))) (((Zdiv m n) = (Z_of_N (NUMERAL N0))) /\ ((r _29327 m n) = m)) ((Z.le (Z_of_N (NUMERAL N0)) (r _29327 m n)) /\ ((Z.lt (r _29327 m n) (Z.abs n)) /\ (m = (Z.add (Z.mul (Zdiv m n) n) (r _29327 m n)))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))).

Axiom Rmod_eq : R -> R -> R -> Prop.

Axiom real_mod_def :
  Rmod_eq = (fun _29623 : R => fun _29624 : R => fun _29625 : R => exists q : R, (integer q) /\ ((Rminus _29624 _29625) = (Rmult q _29623))).

Axiom int_divides_def :
  Z.divide = (fun _29644 : Z => fun _29645 : Z => exists x : Z, _29645 = (Z.mul _29644 x)).

Axiom int_coprime : prod Z Z -> Prop.

Axiom int_coprime_def :
  int_coprime = (fun _29691 : prod Z Z => exists x : Z, exists y : Z, (Z.add (Z.mul (@fst Z Z _29691) x) (Z.mul (@snd Z Z _29691) y)) = (Z_of_N (NUMERAL (BIT1 N0)))).

Axiom int_gcd : prod Z Z -> Z.

Axiom int_gcd_def :
  int_gcd = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod Z Z) -> Z) (fun d : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod Z Z) -> Z => forall _30960 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall a : Z, forall b : Z, (Z.le (Z_of_N (NUMERAL N0)) (d _30960 (@pair Z Z a b))) /\ ((Z.divide (d _30960 (@pair Z Z a b)) a) /\ ((Z.divide (d _30960 (@pair Z Z a b)) b) /\ (exists x : Z, exists y : Z, (d _30960 (@pair Z Z a b)) = (Z.add (Z.mul a x) (Z.mul b y)))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))))).

Axiom int_lcm : prod Z Z -> Z.

Axiom int_lcm_def :
  int_lcm = (fun y0 : prod Z Z => @COND Z ((Z.mul (@fst Z Z y0) (@snd Z Z y0)) = (Z_of_N (NUMERAL N0))) (Z_of_N (NUMERAL N0)) (Zdiv (Z.abs (Z.mul (@fst Z Z y0) (@snd Z Z y0))) (int_gcd (@pair Z Z (@fst Z Z y0) (@snd Z Z y0))))).

(*****************************************************************************)
(* Sets. *)
(*****************************************************************************)

Axiom IN : forall {A : Type'}, A -> (A -> Prop) -> Prop.

Axiom IN_def : forall {A : Type'}, (@IN A) = (fun _32317 : A => fun _32318 : A -> Prop => _32318 _32317).

Axiom EMPTY : forall {A : Type'}, A -> Prop.

Axiom EMPTY_def : forall {A : Type'}, (@EMPTY A) = (fun x : A => False).

Axiom INSERT : forall {A : Type'}, A -> (A -> Prop) -> A -> Prop.

Axiom INSERT_def : forall {A : Type'}, (@INSERT A) = (fun _32373 : A => fun _32374 : A -> Prop => fun y : A => (@IN A y _32374) \/ (y = _32373)).

Axiom UNIV : forall (A : Type'), A -> Prop.

Axiom UNIV_def : forall {A : Type'}, (@UNIV A) = (fun x : A => True).

Axiom GSPEC : forall {A : Type'}, (A -> Prop) -> A -> Prop.

Axiom GSPEC_def : forall {A : Type'}, (@GSPEC A) = (fun _32329 : A -> Prop => _32329).

Axiom SETSPEC : forall {A : Type'}, A -> Prop -> A -> Prop.

Axiom SETSPEC_def : forall {A : Type'}, (@SETSPEC A) = (fun _32334 : A => fun _32335 : Prop => fun _32336 : A => _32335 /\ (_32334 = _32336)).

Axiom SUBSET : forall {A : Type'}, (A -> Prop) -> (A -> Prop) -> Prop.

Axiom SUBSET_def : forall {A : Type'}, (@SUBSET A) = (fun _32443 : A -> Prop => fun _32444 : A -> Prop => forall x : A, (@IN A x _32443) -> @IN A x _32444).

Axiom INTER : forall {A : Type'}, (A -> Prop) -> (A -> Prop) -> A -> Prop.

Axiom INTER_def : forall {A : Type'}, (@INTER A) = (fun _32402 : A -> Prop => fun _32403 : A -> Prop => @GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x _32402) /\ (@IN A x _32403)) x)).

Axiom UNIONS : forall {A : Type'}, ((A -> Prop) -> Prop) -> A -> Prop.

Axiom UNIONS_def : forall {A : Type'}, (@UNIONS A) = (fun _32397 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u _32397) /\ (@IN A x u)) x)).

(*****************************************************************************)
(* Finite sets. *)
(*****************************************************************************)

Axiom FINITE : forall {A : Type'}, (A -> Prop) -> Prop.

Axiom FINITE_def : forall {A : Type'}, (@FINITE A) = (fun a : A -> Prop => forall FINITE' : (A -> Prop) -> Prop, (forall a' : A -> Prop, ((a' = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a' = (@INSERT A x s)) /\ (FINITE' s))) -> FINITE' a') -> FINITE' a).

Axiom ITSET : forall {A B : Type'}, (A -> B -> B) -> (A -> Prop) -> B -> B.

Axiom ITSET_def : forall {A B : Type'}, (@ITSET A B) = (fun _43025 : A -> B -> B => fun _43026 : A -> Prop => fun _43027 : B => @ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@EMPTY A)) = _43027) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (_43025 x (g s))))) _43026).

Axiom CARD : forall {A : Type'}, (A -> Prop) -> N.

Axiom CARD_def : forall {A : Type'}, (@CARD A) = (fun _43228 : A -> Prop => @ITSET A N (fun x : A => fun n : N => N.succ n) _43228 (NUMERAL N0)).

Axiom dimindex : forall {A : Type'}, (A -> Prop) -> N.

Axiom dimindex_def : forall {A : Type'}, (@dimindex A) = (fun _94156 : A -> Prop => @COND N (@FINITE A (@UNIV A)) (@CARD A (@UNIV A)) (NUMERAL (BIT1 N0))).

(*****************************************************************************)
(* Cart.finite_image: natural numbers between 1 and the cardinal of A,
if A is finite, and 1 otherwise. *)
(*****************************************************************************)

Axiom between : N -> N -> N -> Prop.

Axiom between_def : between = (fun _66922 : N => fun _66923 : N => @GSPEC N (fun GEN_PVAR_231 : N => exists x : N, @SETSPEC N GEN_PVAR_231 ((N.le _66922 x) /\ (N.le x _66923)) x)).

Axiom finite_image : Type' -> Type'.

Axiom finite_index : forall {A : Type'}, N -> finite_image A.

Axiom dest_finite_image : forall {A : Type'}, (finite_image A) -> N.

Axiom axiom_27 : forall {A : Type'} (a : finite_image A), (@finite_index A (@dest_finite_image A a)) = a.

Axiom axiom_28 : forall {A : Type'} (r : N), ((fun x : N => @IN N x (between (NUMERAL (BIT1 N0)) (@dimindex A (UNIV A)))) r) = ((@dest_finite_image A (@finite_index A r)) = r).

(*****************************************************************************)
(* Cart.cart A B is finite_image B -> A. *)
(*****************************************************************************)

Definition cart A B := finite_image B -> A.

Definition mk_cart : forall {A B : Type'}, ((finite_image B) -> A) -> cart A B :=
  fun A B f => f.

Definition dest_cart : forall {A B : Type'}, (cart A B) -> (finite_image B) -> A :=
  fun A B f => f.

Axiom axiom_29 : forall {A B : Type'} (a : cart A B), (@mk_cart A B (@dest_cart A B a)) = a.

Axiom axiom_30 : forall {A B : Type'} (r : (finite_image B) -> A), ((fun f : (finite_image B) -> A => True) r) = ((@dest_cart A B (@mk_cart A B r)) = r).

(*****************************************************************************)
(* Cart.finite_sum *)
(*****************************************************************************)

Axiom finite_sum : Type' -> Type' -> Type'.

Axiom mk_finite_sum : forall {A B : Type'}, N -> finite_sum A B.

Axiom dest_finite_sum : forall {A B : Type'}, (finite_sum A B) -> N.

Axiom axiom_31 : forall {A B : Type'} (a : finite_sum A B), (@mk_finite_sum A B (@dest_finite_sum A B a)) = a.

Axiom axiom_32 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (between (NUMERAL (BIT1 N0)) (N.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B))))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r).

(*****************************************************************************)
(* Cart.finite_diff *)
(*****************************************************************************)

Axiom finite_diff : Type' -> Type' -> Type'.

Axiom mk_finite_diff : forall {A B : Type'}, N -> finite_diff A B.

Axiom dest_finite_diff : forall {A B : Type'}, (finite_diff A B) -> N.

Axiom axiom_33 : forall {A B : Type'} (a : finite_diff A B), (@mk_finite_diff A B (@dest_finite_diff A B a)) = a.

Axiom axiom_34 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (between (NUMERAL (BIT1 N0)) (@COND N (N.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (N.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 N0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).

(*****************************************************************************)
(* Cart.finite_prod *)
(*****************************************************************************)

Axiom finite_prod : Type' -> Type' -> Type'.

Axiom mk_finite_prod : forall {A B : Type'}, N -> finite_prod A B.

Axiom dest_finite_prod : forall {A B : Type'}, (finite_prod A B) -> N.

Axiom axiom_35 : forall {A B : Type'} (a : finite_prod A B), (@mk_finite_prod A B (@dest_finite_prod A B a)) = a.

Axiom axiom_36 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (between (NUMERAL (BIT1 N0)) (N.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r).

(*****************************************************************************)
(* Cart.tybit0 *)
(*****************************************************************************)

Axiom tybit0 : Type' -> Type'.

Axiom _mk_tybit0 : forall {A : Type'}, (recspace (finite_sum A A)) -> tybit0 A.

Axiom _dest_tybit0 : forall {A : Type'}, (tybit0 A) -> recspace (finite_sum A A).

Axiom axiom_37 : forall {A : Type'} (a : tybit0 A), (@_mk_tybit0 A (@_dest_tybit0 A a)) = a.

Axiom axiom_38 : forall {A : Type'} (r : recspace (finite_sum A A)), ((fun a : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL N0) a''' (fun n : N => @BOTTOM (finite_sum A A))) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A (@_mk_tybit0 A r)) = r).

(*****************************************************************************)
(* Cart.tybit1 *)
(*****************************************************************************)

Axiom tybit1 : Type' -> Type'.

Axiom _mk_tybit1 : forall {A : Type'}, (recspace (finite_sum (finite_sum A A) unit)) -> tybit1 A.

Axiom _dest_tybit1 : forall {A : Type'}, (tybit1 A) -> recspace (finite_sum (finite_sum A A) unit).

Axiom axiom_39 : forall {A : Type'} (a : tybit1 A), (@_mk_tybit1 A (@_dest_tybit1 A a)) = a.

Axiom axiom_40 : forall {A : Type'} (r : recspace (finite_sum (finite_sum A A) unit)), ((fun a : recspace (finite_sum (finite_sum A A) unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) unit), (exists a'' : finite_sum (finite_sum A A) unit, a' = ((fun a''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL N0) a''' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A (@_mk_tybit1 A r)) = r).

(*****************************************************************************)
(* Library.Frag.frag (free Abelian group) *)
(*****************************************************************************)

Axiom frag : Type' -> Type'.

Axiom mk_frag : forall {A : Type'}, (A -> Z) -> frag A.

Axiom dest_frag : forall {A : Type'}, (frag A) -> A -> Z.

Axiom axiom_41 : forall {A : Type'} (a : frag A), (@mk_frag A (@dest_frag A a)) = a.

Axiom axiom_42 : forall {A : Type'} (r : A -> Z), ((fun f : A -> Z => @FINITE A (@GSPEC A (fun GEN_PVAR_709 : A => exists x : A, @SETSPEC A GEN_PVAR_709 (~ ((f x) = (Z_of_N (NUMERAL N0)))) x))) r) = ((@dest_frag A (@mk_frag A r)) = r).

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

Axiom Group : Type' -> Type'.

Axiom group : forall {A : Type'}, Grp A -> Group A.

Axiom group_operations : forall {A : Type'}, (Group A) -> Grp A.

Axiom axiom_43 : forall {A : Type'} (a : Group A), (@group A (@group_operations A a)) = a.

Axiom axiom_44 : forall {A : Type'} (r : Grp A), is_group r = (group_operations (group r) = r).

(*****************************************************************************)
(* Library.Matroids.matroid *)
(*****************************************************************************)

Definition is_matroid {A:Type'} m := (forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> @SUBSET A s (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall t : A -> Prop, ((@SUBSET A s t) /\ (@SUBSET A t (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m))) -> @SUBSET A (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s) (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m t)) /\ ((forall s : A -> Prop, (@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) -> (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) = (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)) /\ ((forall s : A -> Prop, forall x : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s))) -> exists s' : A -> Prop, (@FINITE A s') /\ ((@SUBSET A s' s) /\ (@IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s')))) /\ (forall s : A -> Prop, forall x : A, forall y : A, ((@SUBSET A s (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A x (@fst (A -> Prop) ((A -> Prop) -> A -> Prop) m)) /\ ((@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A x s))) /\ (~ (@IN A y (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m s)))))) -> @IN A x (@snd (A -> Prop) ((A -> Prop) -> A -> Prop) m (@INSERT A y s))))))).

Axiom Matroid : Type' -> Type'.

Axiom matroid : forall {A : Type'}, (prod (A -> Prop) ((A -> Prop) -> A -> Prop)) -> Matroid A.

Axiom dest_matroid : forall {A : Type'}, (Matroid A) -> prod (A -> Prop) ((A -> Prop) -> A -> Prop).

Axiom axiom_45 : forall {A : Type'} (a : Matroid A), (@matroid A (@dest_matroid A a)) = a.

Axiom axiom_46 : forall {A : Type'} (r : prod (A -> Prop) ((A -> Prop) -> A -> Prop)), (is_matroid r) = ((@dest_matroid A (@matroid A r)) = r).

(*****************************************************************************)
(* Library.Analysis.topology *)
(*****************************************************************************)

Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop :=
  fun U => (IN EMPTY U)
        /\ ((forall s t, ((IN s U) /\ (IN t U)) -> IN (INTER s t) U)
           /\ (forall k, SUBSET k U -> IN (UNIONS k) U)).

Axiom Topology : Type' -> Type'.

Axiom topology : forall {A : Type'}, ((A -> Prop) -> Prop) -> Topology A.

Axiom open_in : forall {A : Type'}, (Topology A) -> (A -> Prop) -> Prop.

Axiom axiom_47 : forall {A : Type'} (a : Topology A), (@topology A (@open_in A a)) = a.

Axiom axiom_48 : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@open_in A (@topology A r)) = r).

(*****************************************************************************)
(* Multivariate.Metric.net *)
(*****************************************************************************)

Definition is_net {A:Type'} g := forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s (@fst ((A -> Prop) -> Prop) (A -> Prop) g)) /\ (@IN (A -> Prop) t (@fst ((A -> Prop) -> Prop) (A -> Prop) g))) -> @IN (A -> Prop) (@INTER A s t) (@fst ((A -> Prop) -> Prop) (A -> Prop) g).

Axiom net : Type' -> Type'.

Axiom mk_net : forall {A : Type'}, (prod ((A -> Prop) -> Prop) (A -> Prop)) -> net A.

Axiom dest_net : forall {A : Type'}, (net A) -> prod ((A -> Prop) -> Prop) (A -> Prop).

Axiom axiom_49 : forall {A : Type'} (a : net A), (@mk_net A (@dest_net A a)) = a.

Axiom axiom_50 : forall {A : Type'} (r : prod ((A -> Prop) -> Prop) (A -> Prop)), is_net r = ((@dest_net A (@mk_net A r)) = r).

(*****************************************************************************)
(* Multivariate.Metric.metric *)
(*****************************************************************************)

Definition MS (A:Type') := prod (A -> Prop) ((prod A A) -> R).

Definition Mcar {A:Type'} : MS A -> A -> Prop := fst.
Definition Mdist {A:Type'} : MS A -> prod A A -> R := snd.

Definition is_metric_space {A : Type'} := (fun M : prod (A -> Prop) ((prod A A) -> R) => (forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> Rle (R_of_N (NUMERAL N0)) (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y))) /\ ((forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> ((@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) = (R_of_N (NUMERAL N0))) = (x = y)) /\ ((forall x : A, forall y : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A y (@fst (A -> Prop) ((prod A A) -> R) M))) -> (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) = (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A y x))) /\ (forall x : A, forall y : A, forall z : A, ((@IN A x (@fst (A -> Prop) ((prod A A) -> R) M)) /\ ((@IN A y (@fst (A -> Prop) ((prod A A) -> R) M)) /\ (@IN A z (@fst (A -> Prop) ((prod A A) -> R) M)))) -> Rle (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x z)) (Rplus (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A x y)) (@snd (A -> Prop) ((prod A A) -> R) M (@pair A A y z))))))).

Axiom Metric : Type' -> Type'.

Axiom metric : forall {A : Type'}, (prod (A -> Prop) ((prod A A) -> R)) -> Metric A.

Axiom dest_metric : forall {A : Type'}, (Metric A) -> prod (A -> Prop) ((prod A A) -> R).

Axiom axiom_51 : forall {A : Type'} (a : Metric A), (@metric A (@dest_metric A a)) = a.

Axiom axiom_52 : forall {A : Type'} (r : prod (A -> Prop) ((prod A A) -> R)), ((fun m : prod (A -> Prop) ((prod A A) -> R) => @is_metric_space A m) r) = ((@dest_metric A (@metric A r)) = r).

(*****************************************************************************)
(* Multivariate.Clifford.multivector *)
(*****************************************************************************)

Axiom Multivector : Type' -> Type'.

Axiom mk_multivector : forall {N' : Type'}, (N -> Prop) -> Multivector N'.

Axiom dest_multivector : forall {N' : Type'}, (Multivector N') -> N -> Prop.

Axiom axiom_53 : forall {N' : Type'} (a : Multivector N'), (@mk_multivector N' (@dest_multivector N' a)) = a.

Axiom axiom_54 : forall {N' : Type'} (r : N -> Prop), ((fun s : N -> Prop => @SUBSET N s (between (NUMERAL (BIT1 N0)) (@dimindex N' (@UNIV N')))) r) = ((@dest_multivector N' (@mk_multivector N' r)) = r).
