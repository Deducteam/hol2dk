/* Map from dk/lp symbols on the right to Coq expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Coq expressions. */

// primitive types
builtin "Type" ≔ Set;
builtin "el" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;

// connectives
builtin "Eq" ≔ =;

builtin "imp" ≔ ⇒;
builtin "imp_def" ≔ ⇒_def;

builtin "all" ≔ ∀;
builtin "all_def" ≔ ∀_def;

builtin "or" ≔ ∨;
builtin "or_def" ≔ ∨_def;

builtin "and" ≔ ∧;
builtin "and_def" ≔ ∧_def;

builtin "ex" ≔ ∃;
builtin "ex_def" ≔ ∃_def;

builtin "not" ≔ ¬;
builtin "not_def" ≔ ¬_def;

builtin "True" ≔ ⊤;
builtin "T_def" ≔ ⊤_def;

builtin "False" ≔ ⊥;
builtin "F_def" ≔ ⊥_def;

builtin "ex1" ≔ ∃₁;
builtin "ex1_def" ≔ ∃₁_def;

// natural deduction rules
builtin "True.intro" ≔ ⊤ᵢ;
builtin "And.intro" ≔ ∧ᵢ;
builtin "And.left" ≔ ∧ₑ₁;
builtin "And.right" ≔ ∧ₑ₂;
builtin "Or.inl" ≔ ∨ᵢ₁;
builtin "Or.inr" ≔ ∨ᵢ₂;
builtin "or_elim" ≔ ∨ₑ;
builtin "Exists.intro" ≔ ∃ᵢ;
builtin "ex_elim" ≔ ∃ₑ;

// HOL-Light rules
builtin "Eq.refl" ≔ REFL;
builtin "EQ_MP" ≔ EQ_MP;
builtin "MK_COMB" ≔ MK_COMB;

// HOL-Light axioms
builtin "ε" ≔ ε;
builtin "axiom_0" ≔ axiom_0;
builtin "axiom_1" ≔ axiom_1;
builtin "fun_ext" ≔ fun_ext;
builtin "prop_ext" ≔ prop_ext;
