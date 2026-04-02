/* Map from dk/lp symbols on the right to Coq expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Coq expressions. */

// primitive types
builtin "Type'" ≔ Set;
builtin "point" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;
builtin "imp" ≔ ⇒;
builtin "all" ≔ ∀;