constant symbol Set : TYPE;

constant symbol bool : Set;
constant symbol fun : Set → Set → Set;

injective symbol El : Set → TYPE;
rule El (fun $a $b) ↪ El $a → El $b;

constant symbol el [A] : El A;
constant symbol ε [A] : El (fun (fun A bool) A);
constant symbol ∃! [A] : El (fun (fun A bool) bool);
constant symbol ¬ : El (fun bool bool);
constant symbol F : El bool;
constant symbol ∨ : El (fun bool (fun bool bool));
constant symbol ∃ [A] : El (fun (fun A bool) bool);
constant symbol ∀ [A] : El (fun (fun A bool) bool);
constant symbol ⇒ : El (fun bool (fun bool bool));
constant symbol ∧ : El (fun bool (fun bool bool));
constant symbol T : El bool;
constant symbol = [A] : El (fun A (fun A bool));

injective symbol Prf : El bool → TYPE;

symbol fun_ext [a b] [f g : El (fun a b)] :
  (Π x, Prf (= (f x) (g x))) → Prf (= f g);
symbol prop_ext [p q : El bool] : (Prf p → Prf q) → (Prf q → Prf p) → Prf (= p q);
symbol REFL [a] (t : El a) : Prf (= t t);
symbol MK_COMB [a b] [s t : El (fun a b)] [u v : El a] :
  Prf (= s t) → Prf (= u v) → Prf (= (s u) (t v));
symbol EQ_MP [p q : El bool] : Prf (= p q) → Prf p → Prf q;
opaque symbol TRANS [a] [x y z : El a] :
  Prf (= x y) → Prf (= y z) → Prf (= x z) ≔
//λ a: Set, λ x: El a, λ y: El a, λ z: El a,
//λ xy: Prf (@= a x y), λ yz: Prf (@= a y z), @EQ_MP (@= a x y) (@= a x z) (@MK_COMB a bool (@= a x) (@= a x) y z (@REFL (fun a bool) (@= a x)) yz) xy;
λ xy: Prf (= x y), λ yz: Prf (= y z), EQ_MP (MK_COMB (REFL (= x)) yz) xy;
/*begin
  assume a x y z xy yz; apply EQ_MP (MK_COMB (REFL (= x)) yz) xy;
  flag "print_implicits" on; flag "print_domains" on; proofterm
end;*/
opaque symbol SYM [a] [x y : El a] : Prf (= x y) → Prf (= y x) ≔
//λ a: Set, λ x: El a, λ y: El a,
//λ xy: Prf (@= a x y), @EQ_MP (@= a x x) (@= a y x) (@MK_COMB a bool (@= a x) (@= a y) x x (@MK_COMB a (fun a bool) (@= a) (@= a) x y (@REFL (fun a (fun a bool)) (@= a)) xy) (@REFL a x)) (@REFL a x);
λ xy: Prf (= x y), EQ_MP (MK_COMB (MK_COMB (REFL (@= a)) xy) (REFL x)) (REFL x);
/*begin
  assume a x y xy;
  apply EQ_MP (MK_COMB (MK_COMB (REFL (@= a)) xy) (REFL x)) (REFL x);
  flag "print_implicits" on; flag "print_domains" on; proofterm
end;*/

rule Prf (⇒ $p $q) ↪ Prf $p → Prf $q;
rule Prf (∀ $p) ↪ Π x, Prf ($p x);

symbol top : Prf T;
symbol ∧ᵢ [p : El bool] : Prf p → Π [q : El bool], Prf q → Prf (∧ p q);
symbol ∧ₑ₁ [p q : El bool] : Prf (∧ p q) → Prf p;
symbol ∧ₑ₂ [p q : El bool] : Prf (∧ p q) → Prf q;
symbol ∃ᵢ [a] (p : El a → El bool) t : Prf (p t) → Prf (∃ p);
symbol ∃ₑ [a] [p : El a → El bool] : Prf (∃ (λ x, p x)) → Π [r : El bool], (Π x:El a, Prf (p x) → Prf r) → Prf r;
symbol ∨ᵢ₁ [p : El bool] : Prf p → Π q : El bool, Prf (∨ p q);
symbol ∨ᵢ₂ (p : El bool) [q : El bool] : Prf q → Prf (∨ p q);
symbol ∨ₑ [p q : El bool] :
  Prf (∨ p q) → Π [r], (Prf p → Prf r) → (Prf q → Prf r) → Prf r;
