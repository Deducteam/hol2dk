/* Map from dk/lp symbols on the right to Coq expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Coq expressions. */

// primitive types
builtin "Type'" ≔ Set;
builtin "el" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;

// connectives
builtin "eq" ≔ =;

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
builtin "Logic.I" ≔ ⊤ᵢ;
builtin "conj" ≔ ∧ᵢ;
builtin "proj1" ≔ ∧ₑ₁;
builtin "proj2" ≔ ∧ₑ₂;
builtin "or_intro1" ≔ ∨ᵢ₁;
builtin "or_intro2" ≔ ∨ᵢ₂;
builtin "or_elim" ≔ ∨ₑ;
builtin "ex_intro" ≔ ∃ᵢ;
builtin "ex_elim" ≔ ∃ₑ;

// HOL-Light rules
builtin "eq_refl" ≔ REFL;
builtin "EQ_MP" ≔ EQ_MP;
builtin "MK_COMB" ≔ MK_COMB;

// HOL-Light axioms
builtin "ε" ≔ ε;
builtin "axiom_0" ≔ axiom_0;
builtin "axiom_1" ≔ axiom_1;
builtin "fun_ext" ≔ fun_ext;
builtin "prop_ext" ≔ prop_ext;

// unit type
builtin "unit" ≔ unit;
builtin "tt" ≔ one;
builtin "one_def" ≔ one_def;
builtin "one_ABS" ≔ one_ABS;
builtin "one_REP" ≔ one_REP;
builtin "axiom_2" ≔ axiom_2;
builtin "axiom_3" ≔ axiom_3;

// product type
builtin "mk_pair" ≔ mk_pair;
builtin "prod" ≔ prod;
builtin "ABS_prod" ≔ ABS_prod;
builtin "REP_prod" ≔ REP_prod;
builtin "axiom_4" ≔ axiom_4;
builtin "axiom_5" ≔ axiom_5;
builtin "pair" ≔ ̦‚;
builtin "pair_def" ≔ ̦‚_def;
builtin "fst" ≔ FST;
builtin "FST_def" ≔ FST_def;
builtin "snd" ≔ SND;
builtin "SND_def" ≔ SND_def;

// infinite type ind
builtin "ind" ≔ ind;
builtin "ONE_ONE" ≔ ONE_ONE;
builtin "ONTO" ≔ ONTO;
builtin "axiom_6" ≔ axiom_6;
builtin "IND_SUC" ≔ IND_SUC;
builtin "IND_0" ≔ IND_0;

// type of natural numbers
builtin "N" ≔ num;
builtin "0%N" ≔ _0;
builtin "N.succ" ≔ SUC;
builtin "mk_num" ≔ mk_num;
builtin "dest_num" ≔ dest_num;
builtin "NUM_REP" ≔ NUM_REP;
builtin "_0_def" ≔ _0_def;
builtin "SUC_def" ≔ SUC_def;
builtin "axiom_7" ≔ axiom_7;
builtin "axiom_8" ≔ axiom_8;

// usual mathematical functions on natural numbers
builtin "BIT0" ≔ BIT0;
builtin "BIT0_def" ≔ BIT0_def;
builtin "BIT1" ≔ BIT1;
builtin "N.pred" ≔ PRE;
builtin "PRE_def" ≔ PRE_def;
builtin "N.add" ≔ +;
builtin "add_def" ≔ +_def;
builtin "N.mul" ≔ *;
builtin "mul_def" ≔ *_def;
builtin "N.pow" ≔ EXP;
builtin "EXP_def" ≔ EXP_def;
builtin "N.le" ≔ <=;
builtin "le_def" ≔ <=_def;
builtin "N.lt" ≔ <;
builtin "lt_def" ≔ <_def;
builtin "N.ge" ≔ >=;
builtin "ge_def" ≔ >=_def;
builtin "N.gt" ≔ >;
builtin "gt_def" ≔ >_def;
builtin "COND" ≔ COND;
builtin "N.max" ≔ MAX;
builtin "MAX_def" ≔ MAX_def;
builtin "N.min" ≔ MIN;
builtin "MIN_def" ≔ MIN_def;
builtin "N.sub" ≔ -;
builtin "minus_def" ≔ -_def;
//builtin "Factorial.fact" ≔ FACT;
//builtin "FACT_def" ≔ FACT_def;
builtin "N.div" ≔ DIV;
builtin "DIV_def" ≔ DIV_def;
builtin "N.modulo" ≔ MOD;
builtin "MOD_def" ≔ MOD_def;
//builtin "N.Even" ≔ EVEN;
//builtin "EVEN_def" ≔ EVEN_def;
//builtin "N.Odd" ≔ ODD;
//builtin "ODD_def" ≔ ODD_def;

// indtypes
builtin "NUMLEFT" ≔ NUMLEFT; // not mandatory
builtin "NUMLEFT_def" ≔ NUMLEFT_def; // not mandatory
builtin "NUMRIGHT" ≔ NUMRIGHT; // not mandatory
builtin "NUMRIGHT_def" ≔ NUMRIGHT_def; // not mandatory
builtin "ZRECSPACE" ≔ ZRECSPACE;
builtin "ZRECSPACE_def" ≔ ZRECSPACE_def;
builtin "recspace" ≔ recspace;
builtin "_mk_rec" ≔ _mk_rec;
builtin "_dest_rec" ≔ _dest_rec;
builtin "axiom_9" ≔ axiom_9;
builtin "axiom_10" ≔ axiom_10;
builtin "option" ≔ option;
builtin "_mk_option" ≔ _mk_option;
builtin "_dest_option" ≔ _dest_option;
builtin "axiom_13" ≔ axiom_13;
builtin "axiom_14" ≔ axiom_14;
builtin "None" ≔ NONE;
builtin "NONE_def" ≔ NONE_def;
builtin "Some" ≔ SOME;
builtin "SOME_def" ≔ SOME_def;
builtin "Datatypes.sum" ≔ Sum;
builtin "_mk_sum" ≔ _mk_sum;
builtin "_dest_sum" ≔ _dest_sum;
builtin "axiom_11" ≔ axiom_11;
builtin "axiom_12" ≔ axiom_12;
builtin "inl" ≔ INL;
builtin "INL_def" ≔ INL_def;
builtin "inr" ≔ INR;
builtin "INR_def" ≔ INR_def;

// lists
builtin "list" ≔ list;
builtin "FCONS" ≔ FCONS;
builtin "FCONS_def" ≔ FCONS_def;
builtin "_dest_list" ≔ _dest_list;
builtin "_mk_list" ≔ _mk_list;
builtin "axiom_15" ≔ axiom_15;
builtin "axiom_16" ≔ axiom_16;
builtin "nil" ≔ NIL;
builtin "NIL_def" ≔ NIL_def;
builtin "cons" ≔ CONS;
builtin "CONS_def" ≔ CONS_def;
builtin "ExtensionalityFacts.is_inverse" ≔ ISO;
builtin "ISO_def" ≔ ISO_def;
builtin "List.app" ≔ APPEND;
builtin "APPEND_def" ≔ APPEND_def;
builtin "List.rev" ≔ REVERSE;
builtin "REVERSE_def" ≔ REVERSE_def;
//builtin "List.length" ≔ LENGTH;
//builtin "LENGTH_def" ≔ LENGTH_def;
builtin "List.map" ≔ MAP;
builtin "MAP_def" ≔ MAP_def;
builtin "List.removelast" ≔ BUTLAST;
builtin "BUTLAST_def" ≔ BUTLAST_def;
builtin "List.Forall" ≔ ALL;
builtin "ALL_def" ≔ ALL_def;
builtin "List.ForallOrdPairs" ≔ PAIRWISE;
builtin "PAIRWISE_def" ≔ PAIRWISE_def;
//builtin "List.filter" ≔ FILTER;
//builtin "FILTER_def" ≔ FILTER_def;
builtin "List.In" ≔ MEM;
builtin "MEM_def" ≔ MEM_def;
//builtin "repeat_with_perm_args" ≔ REPLICATE;
//builtin "REPLICATE_def" ≔ REPLICATE_def;
//builtin "fold_right_with_perm_args" ≔ ITLIST;
//builtin "ITLIST_def" ≔ ITLIST_def;
builtin "hd" ≔ HD;
builtin "HD_def" ≔ HD_def;
builtin "tl" ≔ TL;
builtin "TL_def" ≔ TL_def;
//builtin "EL" ≔ EL;
//builtin "EL_def" ≔ EL_def;
builtin "Ascii.ascii" ≔ char;
builtin "_dest_char" ≔ _dest_char;
builtin "_mk_char" ≔ _mk_char;
builtin "axiom_17" ≔ axiom_17;
builtin "axiom_18" ≔ axiom_18;

// realax
builtin "dist" ≔ dist;
builtin "is_nadd" ≔ is_nadd;
builtin "nadd" ≔ nadd;
builtin "dest_nadd" ≔ dest_nadd;
builtin "mk_nadd" ≔ mk_nadd;
builtin "axiom_19" ≔ axiom_19;
builtin "axiom_20" ≔ axiom_20;

builtin "nadd_of_num" ≔ nadd_of_num;
builtin "nadd_le" ≔ nadd_le;
builtin "nadd_eq" ≔ nadd_eq;
builtin "nadd_add" ≔ nadd_add;
builtin "nadd_mul" ≔ nadd_mul;
builtin "nadd_rinv" ≔ nadd_rinv;
builtin "nadd_inv" ≔ nadd_inv;

builtin "hreal" ≔ hreal;
builtin "mk_hreal" ≔ mk_hreal;
builtin "dest_hreal" ≔ dest_hreal;
builtin "axiom_21" ≔ axiom_21;
builtin "axiom_22" ≔ axiom_22;

builtin "hreal_of_num" ≔ hreal_of_num;
builtin "hreal_le" ≔ hreal_le;
builtin "hreal_eq" ≔ hreal_eq;
builtin "hreal_add" ≔ hreal_add;
builtin "hreal_mul" ≔ hreal_mul;
builtin "hreal_inv" ≔ hreal_inv;

builtin "treal_of_num" ≔ treal_of_num;
builtin "treal_le" ≔ treal_le;
builtin "treal_eq" ≔ treal_eq;
builtin "treal_add" ≔ treal_add;
builtin "treal_mul" ≔ treal_mul;
builtin "treal_inv" ≔ treal_inv;
builtin "treal_neg" ≔ treal_neg;

builtin "R" ≔ Real;
builtin "mk_real" ≔ mk_real;
builtin "dest_real" ≔ dest_real;
builtin "axiom_23" ≔ axiom_23;
builtin "axiom_24" ≔ axiom_24;

builtin "Rle" ≔ real_le;
builtin "real_le_def" ≔ real_le_def;
builtin "Rplus" ≔ real_add;
builtin "real_add_def" ≔ real_add_def;
builtin "Rmult" ≔ real_mul;
builtin "real_mul_def" ≔ real_mul_def;
builtin "Rinv" ≔ real_inv;
builtin "real_inv_def" ≔ real_inv_def;
builtin "Ropp" ≔ real_neg;
builtin "real_neg_def" ≔ real_neg_def;
builtin "R_of_N" ≔ real_of_num;
builtin "real_of_num_def" ≔ real_of_num_def;
builtin "Rpow" ≔ real_pow;
builtin "real_pow_def" ≔ real_pow_def;
builtin "Rabs" ≔ real_abs;
builtin "real_abs_def" ≔ real_abs_def;
builtin "Rdiv" ≔ real_div;
builtin "real_div_def" ≔ real_div_def;
builtin "Rminus" ≔ real_sub;
builtin "real_sub_def" ≔ real_sub_def;
builtin "Rge" ≔ real_ge;
builtin "real_ge_def" ≔ real_ge_def;
builtin "Rgt" ≔ real_gt;
builtin "real_gt_def" ≔ real_gt_def;
builtin "Rlt" ≔ real_lt;
builtin "real_lt_def" ≔ real_lt_def;
builtin "Rmax" ≔ real_max;
builtin "real_max_def" ≔ real_max_def;
builtin "Rmin" ≔ real_min;
builtin "real_min_def" ≔ real_min_def;
builtin "Rsgn" ≔ real_sgn;
builtin "real_sgn_def" ≔ real_sgn_def;
builtin "Rmod_eq" ≔ real_mod;
builtin "real_mod_def" ≔ real_mod_def;

// integers
builtin "Z" ≔ int;
builtin "IZR" ≔ real_of_int;
builtin "int_of_real" ≔ int_of_real;
builtin "axiom_25" ≔ axiom_25;
builtin "axiom_26" ≔ axiom_26;
builtin "Z_of_N" ≔ int_of_num;
builtin "int_of_num_def" ≔ int_of_num_def;
builtin "Z.le" ≔ int_le;
builtin "int_le_def" ≔ int_le_def;
builtin "Z.lt" ≔ int_lt;
builtin "int_lt_def" ≔ int_lt_def;
builtin "Z.ge" ≔ int_ge;
builtin "int_ge_def" ≔ int_ge_def;
builtin "Z.gt" ≔ int_gt;
builtin "int_gt_def" ≔ int_gt_def;
builtin "Z.opp" ≔ int_neg;
builtin "int_neg_def" ≔ int_neg_def;
builtin "Z.add" ≔ int_add;
builtin "int_add_def" ≔ int_add_def;
builtin "Z.sub" ≔ int_sub;
builtin "int_sub_def" ≔ int_sub_def;
builtin "Z.mul" ≔ int_mul;
builtin "int_mul_def" ≔ int_mul_def;
builtin "Z.abs" ≔ int_abs;
builtin "int_abs_def" ≔ int_abs_def;
builtin "Z.sgn" ≔ int_sgn;
builtin "int_sgn_def" ≔ int_sgn_def;
builtin "Z.max" ≔ int_max;
builtin "int_max_def" ≔ int_max_def;
builtin "Z.min" ≔ int_min;
builtin "int_min_def" ≔ int_min_def;
builtin "Zpow" ≔ int_pow;
builtin "int_pow_def" ≔ int_pow_def;
builtin "Zdiv" ≔ div;
builtin "div_def" ≔ div_def;
builtin "Zrem" ≔ rem;
builtin "rem_def" ≔ rem_def;
builtin "Z.divide" ≔ int_divides;
builtin "int_divides_def" ≔ int_divides_def;
builtin "int_coprime" ≔ int_coprime;
builtin "int_coprime_def" ≔ int_coprime_def;
builtin "int_gcd" ≔ int_gcd;
builtin "int_gcd_def" ≔ int_gcd_def;
builtin "int_lcm" ≔ int_lcm;
builtin "int_lcm_def" ≔ int_lcm_def;

// finite_image
builtin "finite_image" ≔ finite_image;
builtin "finite_index" ≔ finite_index;
builtin "dest_finite_image" ≔ dest_finite_image;
builtin "axiom_27" ≔ axiom_27;
builtin "axiom_28" ≔ axiom_28;

// cart
builtin "cart" ≔ cart;
builtin "mk_cart" ≔ mk_cart;
builtin "dest_cart" ≔ dest_cart;
builtin "axiom_29" ≔ axiom_29;
builtin "axiom_30" ≔ axiom_30;

// finite_sum
builtin "finite_sum" ≔ finite_sum;
builtin "mk_finite_sum" ≔ mk_finite_sum;
builtin "dest_finite_sum" ≔ dest_finite_sum;
builtin "axiom_31" ≔ axiom_31;
builtin "axiom_32" ≔ axiom_32;

// finite_diff
builtin "finite_diff" ≔ finite_diff;
builtin "mk_finite_diff" ≔ mk_finite_diff;
builtin "dest_finite_diff" ≔ dest_finite_diff;
builtin "axiom_33" ≔ axiom_33;
builtin "axiom_34" ≔ axiom_34;

// finite_prod
builtin "finite_prod" ≔ finite_prod;
builtin "mk_finite_prod" ≔ mk_finite_prod;
builtin "dest_finite_prod" ≔ dest_finite_prod;
builtin "axiom_35" ≔ axiom_35;
builtin "axiom_36" ≔ axiom_36;

// tybit0
builtin "tybit0" ≔ tybit0;
builtin "_mk_tybit0" ≔ _mk_tybit0;
builtin "_dest_tybit0" ≔ _dest_tybit0;
builtin "axiom_37" ≔ axiom_37;
builtin "axiom_38" ≔ axiom_38;

// tybit1
builtin "tybit1" ≔ tybit1;
builtin "_mk_tybit1" ≔ _mk_tybit1;
builtin "_dest_tybit1" ≔ _dest_tybit1;
builtin "axiom_39" ≔ axiom_39;
builtin "axiom_40" ≔ axiom_40;

// frag
builtin "frag" ≔ frag;
builtin "mk_frag" ≔ mk_frag;
builtin "dest_frag" ≔ dest_frag;
builtin "axiom_41" ≔ axiom_41;
builtin "axiom_42" ≔ axiom_42;

// group
builtin "Group" ≔ Group;
builtin "group" ≔ group;
builtin "group_operations" ≔ group_operations;
builtin "axiom_43" ≔ axiom_43;
builtin "axiom_44" ≔ axiom_44;

// matroid
builtin "Matroid" ≔ Matroid;
builtin "matroid" ≔ matroid;
builtin "dest_matroid" ≔ dest_matroid;
builtin "axiom_45" ≔ axiom_45;
builtin "axiom_46" ≔ axiom_46;

// topology
builtin "Topology" ≔ Topology;
builtin "topology" ≔ topology;
builtin "open_in" ≔ open_in;
builtin "axiom_47" ≔ axiom_47;
builtin "axiom_48" ≔ axiom_48;

// net
builtin "net" ≔ net;
builtin "mk_net" ≔ mk_net;
builtin "dest_net" ≔ dest_net;
builtin "axiom_49" ≔ axiom_49;
builtin "axiom_50" ≔ axiom_50;

// metric_space
builtin "Metric" ≔ Metric;
builtin "metric" ≔ metric;
builtin "dest_metric" ≔ dest_metric;
builtin "axiom_51" ≔ axiom_51;
builtin "axiom_52" ≔ axiom_52;

// multivector
builtin "Multivector" ≔ Multivector;
builtin "mk_multivector" ≔ mk_multivector;
builtin "dest_multivector" ≔ dest_multivector;
builtin "axiom_53" ≔ axiom_53;
builtin "axiom_54" ≔ axiom_54;
