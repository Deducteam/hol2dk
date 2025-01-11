// map for renaming dk/lp identifiers (on the right)
// to Coq expressions (on the left)

builtin "minus" ≔ -;
builtin "minus_def" ≔ -_def;
builtin "minus'" ≔ -';
builtin "gt" ≔ >;
builtin "gt_def" ≔ >_def;
builtin "ge" ≔ >=;
builtin "ge_def" ≔ >=_def;
builtin "lt" ≔ <;
builtin "lt_def" ≔ <_def;
builtin "lt" ≔ <';
builtin "le" ≔ <=;
builtin "le_def" ≔ <=_def;
builtin "le'" ≔ <=';
builtin "mul" ≔ *;
builtin "mul_def" ≔ *_def;
builtin "mul'" ≔ *';
builtin "add" ≔ +;
builtin "add_def" ≔ +_def;
builtin "add'" ≔ +';
builtin "pair" ≔ ̦‚;
builtin "pair_def" ≔ ̦‚_def;
builtin "gt_c" ≔ >_c;
builtin "gt_c_def" ≔ >_c_def;
builtin "ge_c" ≔ >=_c;
builtin "ge_c_def" ≔ >=_c_def;
builtin "eq_c" ≔ =_c;
builtin "eq_c_def" ≔ =_c_def;
builtin "lt_c" ≔ <_c;
builtin "lt_c_def" ≔ <_c_def;
builtin "le_c" ≔ <=_c;
builtin "le_c_def" ≔ <=_c_def;
builtin "eq2" ≔ ==;
builtin "eq2_def" ≔ ==_def;
builtin "ltle" ≔ <<=;
builtin "ltle'" ≔ <<=';
builtin "lt2" ≔ <<;
builtin "lt2_def" ≔ <<_def;
builtin "lt2'" ≔ <<';
builtin "lt2''" ≔ <<'';
builtin "lt3" ≔ <<<;
builtin "not_def" ≔ ¬_def;
builtin "dotdot" ≔ …;
builtin "dotdot_def" ≔ …_def;
builtin "dollar" ≔ ﹩;
builtin "dollar_def" ≔ ﹩_def;

// Logic
builtin "FImp" ≔ ⟶;
builtin "FImp_def" ≔ ⟶_def;
builtin "FAll" ≔ !!;
builtin "FAll_def" ≔ !!_def;
builtin "FOr" ≔ ¦¦;
builtin "FOr_def" ≔ ¦¦_def;
builtin "FAnd" ≔ &&;
builtin "FAnd_def" ≔ &&_def;
builtin "FEquiv" ≔ ↔;
builtin "FEquiv_def" ≔ ↔_def;
builtin "FEx" ≔ ??;
builtin "FEx_def" ≔ ??_def;
builtin "FFalse" ≔ False;
builtin "FFalse_def" ≔ False_def;
builtin "FTrue" ≔ True;
builtin "FTrue_def" ≔ True_def;
builtin "FEq" ≔ ===;
builtin "FEq_def" ≔ ===_def;
builtin "FNot" ≔ ~~;
builtin "FNot_def" ≔ ~~_def;

// Arithmetic
builtin "addadd" ≔ ++;
builtin "addadd_def" ≔ ++_def;
builtin "mulmul" ≔ **;
builtin "mulmul_def" ≔ **_def;
builtin "ltle" ≔ <<=;
builtin "ltle_def" ≔ <<=_def;

// Multivariate
builtin "pair'" ≔ pair;

builtin "add_c" ≔ +_c;
builtin "add_c_def" ≔ +_c_def;
builtin "percent" ≔ %;
builtin "percent_def" ≔ %_def;
builtin "mul_c" ≔ *_c;
builtin "mul_c_def" ≔ *_c_def;
builtin "pow_c" ≔ ^_c;
builtin "pow_c_def" ≔ ^_c_def;
builtin "_at" ≔ at;
builtin "_at_def" ≔ at_def;
builtin "dollardollar" ≔ ﹩﹩;
builtin "dollardollar_def" ≔ ﹩﹩_def;
builtin "longarrow" ≔ ⭬;
builtin "longarrow_def" ≔ ⭬_def;

builtin "N'" ≔ N;
builtin "N''" ≔ N';
builtin "N'''" ≔ N'';

builtin "R'" ≔ R;
builtin "R''" ≔ R';

builtin "S'" ≔ S;
builtin "S''" ≔ S';
builtin "S'''" ≔ S'';
builtin "S''''" ≔ S''';

builtin "Z'" ≔ Z;
builtin "Z''" ≔ Z';
builtin "Z'''" ≔ Z'';
