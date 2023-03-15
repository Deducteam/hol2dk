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
symbol prop_ext [p q] : (Prf p → Prf q) → (Prf q → Prf p) → Prf (= p q);
symbol REFL [a] (t:El a) : Prf (= t t);
symbol MK_COMB [a b] [s t : El (fun a b)] [u v : El a] :
  Prf (= s t) → Prf (= u v) → Prf (= (s u) (t v));
symbol EQ_MP [p q] : Prf (= p q) → Prf p → Prf q;
symbol TRANS [a] [x y z : El a] :
  Prf (= x y) → Prf (= y z) → Prf (= x z) ≔
/*begin
  assume a x y z xy yz; apply EQ_MP _ xy; apply MK_COMB (REFL (= x)) yz;
  flag "print_implicits" on; flag "print_domains" on; proofterm;
end;*/
  λ xy : Prf (= x y), λ yz : Prf (= y z),
    @EQ_MP (= x y) (= x z)
      (@MK_COMB a bool (@= a x) (@= a x) y z (@REFL (fun a bool) (@= a x)) yz)
      xy;

rule Prf (⇒ $p $q) ↪ Prf $p → Prf $q;
rule Prf (∀ $p) ↪ Π x, Prf ($p x);

symbol top : Prf T;
symbol ∧ᵢ [p] : Prf p → Π [q], Prf q → Prf (∧ p q);
symbol ∧ₑ₁ [p q] : Prf (∧ p q) → Prf p;
symbol ∧ₑ₂ [p q] : Prf (∧ p q) → Prf q;
symbol ∃ᵢ [a] p (t : El a) : Prf (p t) → Prf (∃ p);
symbol ∃ₑ [a] p : Prf (∃ p) → Π r, (Π x:El a, Prf (p x) → Prf r) → Prf r;
symbol ∨ᵢ₁ [p] : Prf p → Π q, Prf (∨ p q);
symbol ∨ᵢ₂ p [q] : Prf q → Prf (∨ p q);
symbol ∨ₑ [p q] :
  Prf (∨ p q) → Π [r], (Prf p → Prf r) → (Prf q → Prf r) → Prf r;
