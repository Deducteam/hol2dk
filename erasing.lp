// dk/lp symbols (on the right) the declarations of which are removed
// and whose uses are replaced by the given Coq expressions (on the left)

builtin "Type'" ≔ Set;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;
builtin "imp" ≔ ⇒;
builtin "all" ≔ ∀;
builtin "eq" ≔ =;
builtin "or" ≔ ∨;
builtin "and" ≔ ∧;
builtin "ex" ≔ ∃;
builtin "not" ≔ ¬;
builtin "True" ≔ T;
builtin "False" ≔ F;

builtin "Logic.I" ≔ top;
builtin "conj" ≔ ∧ᵢ;
builtin "proj1" ≔ ∧ₑ₁;
builtin "proj2" ≔ ∧ₑ₂;
builtin "or_intro1" ≔ ∨ᵢ₁;
builtin "or_intro2" ≔ ∨ᵢ₂;
builtin "or_elim" ≔ ∨ₑ;
builtin "ex_intro" ≔ ∃ᵢ;
builtin "ex_elim" ≔ ∃ₑ;
builtin "eq_refl" ≔ REFL;
builtin "EQ_MP" ≔ EQ_MP;
builtin "MK_COMB" ≔ MK_COMB;
builtin "el" ≔ el;

builtin "nat" ≔ num;
builtin "0" ≔ _0;
builtin "S" ≔ SUC;

builtin "prod" ≔ prod;
builtin "pair" ≔ pair;
builtin "fst" ≔ FST;
builtin "snd" ≔ SND;

builtin "unit" ≔ 1;
builtin "tt" ≔ one;

builtin "id" ≔ I;

builtin "False" ≔ _FALSITY_;

builtin "ε" ≔ ε;
builtin "ex1" ≔ ∃!;

builtin "axiom_0" ≔ axiom_0;
builtin "axiom_1" ≔ axiom_1;

builtin "_FALSITY__def" ≔ _FALSITY__def;
builtin "ex1_def" ≔ ∃!_def;
builtin "not_def" ≔ ¬_def;
builtin "or_def" ≔ ∨_def;
builtin "ex_def" ≔ ∃_def;
builtin "all_def" ≔ ∀_def;
builtin "imp_def" ≔ ⇒_def;
builtin "and_def" ≔ ∧_def;
builtin "F_def" ≔ F_def;
builtin "T_def" ≔ T_def;

builtin "fun_ext" ≔ fun_ext;
builtin "prop_ext" ≔ prop_ext;
