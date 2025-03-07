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

Definition COND {A : Type'} := fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2)).

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

Axiom GABS : forall {A : Type'} : (A -> Prop) -> A.

Axiom GABS_def : forall {A : Type'}, (@ε A) = (fun P : A -> Prop => @ε A P).

Axiom _UNGUARDED_PATTERN : Prop -> Prop -> Prop.

Axiom _UNGUARDED_PATTERN_def : and = (fun p : Prop => fun r : Prop => p /\ r).

Axiom _FALSITY__def : Prop.

Axiom _FALSITY__def : False = False.

Axiom hashek : Prop.

Axiom hashek_def : True = True.

Axiom is_inverse: forall A B : Type, (A -> B) -> (B -> A) -> Prop.

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

Definition mk_pair {A B : Type'} := (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).

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

Definition ONE_ONE {A B : Type'} := fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2.

Definition ONTO {A B : Type'} := fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x).

Axiom axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).

Definition IND_SUC := (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))).

Definition IND_0 := (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))).

Definition NUM_REP := (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a).

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

Definition NUMERAL := (fun _2128 : N => _2128).

Definition BIT0 := N.double.

Axiom BIT0_def : BIT0 = @ε (arr N N') (fun y0 : N -> N => ((y0 (NUMERAL N0)) = (NUMERAL N0)) /\ (forall y1 : N, (y0 (N.succ y1)) = (N.succ (N.succ (y0 y1))))).

Definition BIT1 := (fun _2143 : N => N.succ (BIT0 _2143)).

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

Axiom NUMSUM : Prop -> N -> N.

Axiom NUMLEFT : N -> Prop.

Axiom NUMLEFT_def : NUMLEFT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop) (fun X : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> N -> Prop => forall _17372 : prod N (prod N (prod N (prod N (prod N (prod N N))))), exists Y : N -> N, forall x : Prop, forall y : N, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))))).

Axiom NUMRIGHT : N -> N.

Axiom NUMRIGHT_def : NUMRIGHT = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N) (fun Y : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> N => forall _17373 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), forall x : Prop, forall y : N, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))))).

Axiom ZRECSPACE: forall {A : Type'}, (N -> A -> Prop) -> Prop.

Axiom ZCONSTR: forall {A : Type'}, N -> A -> (N -> N -> A -> Prop) -> N -> A -> Prop.

Axiom ZBOT: forall {A : Type'}, N -> A -> Prop.

Axiom ZRECSPACE_def: forall {A : Type'}, (@ZRECSPACE A) = (fun a : N -> A -> Prop => forall ZRECSPACE' : (N -> A -> Prop) -> Prop, (forall a' : N -> A -> Prop, ((a' = (@ZBOT A)) \/ (exists c : N, exists i : A, exists r : N -> N -> A -> Prop, (a' = (@ZCONSTR A c i r)) /\ (forall n : N, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a).

Axiom recspace : Type' -> Type'.

Axiom _dest_rec : forall {A : Type'}, (recspace A) -> N -> A -> Prop.

Axiom _mk_rec : forall {A : Type'}, (N -> A -> Prop) -> recspace A.

Axiom axiom_10 : forall {A : Type'} (r : N -> A -> Prop), (@ZRECSPACE A r) = ((@_dest_rec A (@_mk_rec A r)) = r).

Axiom axiom_9 : forall {A : Type'} (a : recspace A), (@_mk_rec A (@_dest_rec A a)) = a.

Axiom BOTTOM: forall {A : Type'}, recspace A.

Axiom CONSTR: forall {A : Type'}, N -> A -> (N -> recspace A) -> recspace A.

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

Definition list' (A : Type') := {| type := list A; el := nil |}.
Canonical list'.

Axiom FCONS: forall {A : Type'} (a : A) (f: N -> A) (n : N), A.

Axiom FCONS_def: forall {A : Type'}, @FCONS A = @ε ((prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A) (fun FCONS' : (prod N (prod N (prod N (prod N N)))) -> A -> (N -> A) -> N -> A => forall _17460 : prod N (prod N (prod N (prod N N))), (forall a : A, forall f : N -> A, (FCONS' _17460 a f (NUMERAL N0)) = a) /\ (forall a : A, forall f : N -> A, forall n : N, (FCONS' _17460 a f (N.succ n)) = (f n))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).

Axiom _dest_list: forall {A : Type'} (l: list A), recspace A.

Axiom _mk_list : forall {A : Type'}, (recspace A) -> list A.

Axiom axiom_15 : forall {A : Type'} (a : list A), (@_mk_list A (@_dest_list A a)) = a.

Axiom axiom_16 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall list' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL N0) (@ε A (fun v : A => True)) (fun n : N => @BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => @CONSTR A (N.succ (NUMERAL N0)) a0' (@FCONS (recspace A) a1' (fun n : N => @BOTTOM A))) a0 a1)) /\ (list' a1))) -> list' a') -> list' a) r) = ((@_dest_list A (@_mk_list A r)) = r).

Module List.
  Axiom app : forall A, list A -> list A -> list A.
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

Axiom is_nadd_def : is_nadd = fun f : N -> N => exists B : N, forall m : N, forall n : N, N.le (dist (@pair N N (N.mul m (f n)) (N.mul n (f m)))) (N.mul B (N.add m n)).

Axiom nadd : Type'.

Axiom mk_nadd: (N -> N) -> nadd.

Axiom dest_nadd: nadd -> (N -> N).

Axiom axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.

Axiom axiom_20 : forall (r : N -> N), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).

(*****************************************************************************)
(* Alignment of the type hreal of non-negative real numbers. *)
(*****************************************************************************)

Axiom nadd_eq : nadd -> nadd -> Prop.

Axiom hreal : Type'.

Axiom mk_hreal : (nadd -> Prop) -> hreal.

Axiom dest_hreal : hreal -> (nadd -> Prop).

Axiom axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.

Axiom axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).

(*****************************************************************************)
(* HOL-Light definition of real numbers. *)
(*****************************************************************************)

Axiom treal_eq : hreal * hreal -> hreal * hreal -> Prop.

Axiom real : Type'.

Module Export HL.

Axiom mk_real : (prod' hreal hreal -> Prop) -> real.

Axiom dest_real : real -> (prod' hreal hreal -> Prop).

Axiom axiom_23 : forall (a : real), (mk_real (dest_real a)) = a.

Axiom axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).

End HL.
