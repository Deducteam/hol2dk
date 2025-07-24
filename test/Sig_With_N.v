Require Export HOLLight.type.
Require HOLLight.Sig_mappings_N.

Module Type Spec.

Include HOLLight.Sig_mappings_N.Spec.

(*****************************************************************************)
(* Alignment of the type of real numbers. *)
(*****************************************************************************)

Axiom R : Type.

Axiom R0 : R.

Definition R' := {| type := R; el := R0 |}.
Canonical R'.

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

Axiom dotdot : N -> N -> N -> Prop.

Axiom dotdot_def : dotdot = (fun _66922 : N => fun _66923 : N => @GSPEC N (fun GEN_PVAR_231 : N => exists x : N, @SETSPEC N GEN_PVAR_231 ((N.le _66922 x) /\ (N.le x _66923)) x)).

Axiom finite_image : Type' -> Type'.

Axiom finite_index : forall {A : Type'}, N -> finite_image A.

Axiom dest_finite_image : forall {A : Type'}, (finite_image A) -> N.

Axiom axiom_27 : forall {A : Type'} (a : finite_image A), (@finite_index A (@dest_finite_image A a)) = a.

Axiom axiom_28 : forall {A : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 N0)) (@dimindex A (UNIV A)))) r) = ((@dest_finite_image A (@finite_index A r)) = r).

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

Axiom axiom_32 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 N0)) (N.add (@dimindex A (UNIV A)) (@dimindex B (UNIV B))))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r).

(*****************************************************************************)
(* Cart.finite_diff *)
(*****************************************************************************)

Axiom finite_diff : Type' -> Type' -> Type'.

Axiom mk_finite_diff : forall {A B : Type'}, N -> finite_diff A B.

Axiom dest_finite_diff : forall {A B : Type'}, (finite_diff A B) -> N.

Axiom axiom_33 : forall {A B : Type'} (a : finite_diff A B), (@mk_finite_diff A B (@dest_finite_diff A B a)) = a.

Axiom axiom_34 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 N0)) (@COND N (N.lt (@dimindex B (UNIV B)) (@dimindex A (UNIV A))) (N.sub (@dimindex A (UNIV A)) (@dimindex B (UNIV B))) (NUMERAL (BIT1 N0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).

(*****************************************************************************)
(* Cart.finite_prod *)
(*****************************************************************************)

Axiom finite_prod : Type' -> Type' -> Type'.

Axiom mk_finite_prod : forall {A B : Type'}, N -> finite_prod A B.

Axiom dest_finite_prod : forall {A B : Type'}, (finite_prod A B) -> N.

Axiom axiom_35 : forall {A B : Type'} (a : finite_prod A B), (@mk_finite_prod A B (@dest_finite_prod A B a)) = a.

Axiom axiom_36 : forall {A B : Type'} (r : N), ((fun x : N => @IN N x (dotdot (NUMERAL (BIT1 N0)) (N.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r).

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

Axiom axiom_54 : forall {N' : Type'} (r : N -> Prop), ((fun s : N -> Prop => @SUBSET N s (dotdot (NUMERAL (BIT1 N0)) (@dimindex N' (@UNIV N')))) r) = ((@dest_multivector N' (@mk_multivector N' r)) = r).

End Spec.

Include Spec.
