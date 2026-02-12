(****************************************************************************)
(* Export HOL-Light proofs to Lambdapi. *)
(****************************************************************************)

open Xprelude
open Fusion
open Xlib
open Xproof

(****************************************************************************)
(* Translation of names. *)
(****************************************************************************)

(* Rename HOL-Light names to valid (and sometimes nicer) identifiers. *)
let lp_name =
  let prefixes = (* the order is important *)
    [ "|----", "vdash4"
    ; "|---", "vdash3"
    ; "|--", "vdash2"
    ; "|->", "mapsto"
    ; "|-", "vdash"
    ; "|=>", "bar_imp"]
  in
  fun n ->
  match n with
    | "" -> assert false
    | "," -> "̦‚" (* 201A *)
    | "@" -> "ε"
    | "\\/" -> "∨"
    | "/\\" -> "∧"
    | "==>" -> "⇒"
    | "!" -> "∀"
    | "?" -> "∃"
    | "F" -> "⊥"
    | "T" -> "⊤"
    | "?!" -> "∃₁"
    | "~" -> "¬"
    | "-->" -> "⟶" (* 27F6 *)
    | "--->" -> "⭬" (* 279F *)
    | "<->" -> "↔" (* 2194 *)
    (* invalid Lambdapi identifiers *)
    | "$" -> "﹩" (* FE69 *)
    | "$$" -> "﹩﹩" (* FE69 *)
    | ".." -> "…" (* 2026 *)
    | "|" -> "¦" (* 00A6 *)
    | "||" -> "¦¦"
    |"_"|"abort"|"admit"|"admitted"|"apply"|"as"|"assert"|"assertnot"
    |"associative"|"assume"|"begin"|"builtin"|"coerce_rule"|"commutative"
    |"compute"|"constant"|"debug"|"end"|"fail"|"flag"|"generalize"|"have"
    |"in"|"induction"|"inductive"|"infix"|"injective"|"left"|"let"|"notation"
    |"off"|"on"|"opaque"|"open"|"postfix"|"prefix"|"print"|"private"
    |"proofterm"|"protected"|"prover"|"prover_timeout"|"quantifier"|"refine"
    |"reflexivity"|"remove"|"require"|"rewrite"|"right"|"rule"|"search"
    |"sequential"|"simplify"|"solve"|"symbol"|"symmetry"|"type"|"TYPE"
    |"unif_rule"|"verbose"|"why3"|"with" -> "_" ^ n
    (* for Coq *)
    | "%" -> n
    | _ -> Xlib.change_prefixes prefixes (Xlib.replace '%' '_' n)
;;

let name oc n = string oc (lp_name n);;

(****************************************************************************)
(* Translation of types. *)
(****************************************************************************)

let string_of_typ_name n =
  match n with
  | "" -> assert false
  | "1" -> "unit"
  (* type names used also as constant names are capitalized *)
  |"group"|"matroid"|"metric"|"multiset"|"multivector"|"real"|"sum"|"topology"
   -> String.capitalize_ascii n
  | _ ->
    if n.[0] = '?' then "_" ^ String.sub n 1 (String.length n - 1) else n
;;

let typ_name oc n = string oc (string_of_typ_name n);;

let rec raw_typ oc b =
  match b with
  | Tyvar n
  | Tyapp(n,[]) -> typ_name oc n
  | Tyapp(n,bs) ->
    char oc '('; typ_name oc n; list_prefix " " raw_typ oc bs; char oc ')'
;;

let rec string_of_typ = function
  | Tyvar n
  | Tyapp(n,[]) -> string_of_typ_name n
  | Tyapp(n,bs) ->
    "("^string_of_typ_name n^" "
    ^String.concat " " (List.map string_of_typ bs)^")"
;;

let map_typ_abbrev : (Digest.t * int) MapStr.t ref = ref MapStr.empty;;

let abbrev_typ oc b =
  match b with
  | Tyvar n
  | Tyapp(n,[]) -> typ_name oc n
  | Tyapp(_,bs) ->
    if List.for_all is_var_or_cst_type bs then raw_typ oc b
    else
      let tvs, b = canonical_typ b in
      let s = string_of_typ b in
      let d = Digest.string s in
      map_typ_abbrev := MapStr.add s (d, List.length tvs) !map_typ_abbrev;
      match tvs with
      | [] -> string oc "type"; digest oc d
      | _ ->
        string oc "(type"; digest oc d; list_prefix " " raw_typ oc tvs;
        char oc ')'
;;

let typ = abbrev_typ;;

(* [decl_type_abbrevs oc] outputs on [oc] the type abbreviations. *)
let decl_type_abbrevs oc =
  let abbrev s (k,n) =
    string oc "symbol type"; digest oc k;
    for i=0 to n-1 do string oc " a"; int oc i done;
    (* We can use [raw_typ] here since [b] is canonical. *)
    string oc " ≔ "; string oc s; string oc ";\n"
  in
  MapStr.iter abbrev !map_typ_abbrev
;;

(****************************************************************************)
(* Translation of term variables. *)
(****************************************************************************)

let raw_var oc t =
  match t with
  | Var(n,_) -> name oc n
  | _ -> assert false
;;

(* [var rmap oc t] prints on [oc] the variable [t] using the name
   given by [rmap]. Fails if [t] is not a variable or if [t] is not in
   [rmap]. Variables need to be renamed in Dedukti or Lambdapi
   because, in HOL-Light, a variable is identified by both its name
   AND its type, that is, two distinct variables can have the same
   name but distinct types. *)
let var rmap oc t =
  try name oc (List.assoc t rmap)
  with Not_found -> assert false
    (*match t with
    | Var(n,_) -> name oc n; string oc " /*not found*/"
    | _ -> assert false*)
;;

let raw_decl_var oc t =
  match t with
  | Var(n,b) -> name oc n; string oc " : El "; typ oc b
  | _ -> assert false
;;

let decl_var rmap oc t =
  match t with
  | Var(_,b) -> var rmap oc t; string oc " : El "; typ oc b
  | _ -> assert false
;;

let unabbrev_decl_var rmap oc t =
  match t with
  | Var(_,b) -> var rmap oc t; string oc " : El "; raw_typ oc b
  | _ -> assert false
;;

let decl_param rmap oc v = string oc " ("; decl_var rmap oc v; char oc ')';;

let unabbrev_decl_param rmap oc v =
  string oc " ("; unabbrev_decl_var rmap oc v; char oc ')';;

(****************************************************************************)
(* Translation of terms. *)
(****************************************************************************)

let rec raw_term oc t =
  match t with
  | Var(n,_) -> name oc n
  | Const(n,b) ->
     begin match const_typ_vars_pos n with
     | [] -> name oc n
     | ps ->
        string oc "(@"; name oc n;
        List.iter (fun p -> char oc ' '; raw_typ oc (subtyp b p)) ps;
        char oc ')'
     end
  | Comb _ ->
     let h, ts = head_args t in
     begin match h, ts with
     | Const("=" as n,_), [_;_]
     | Const(("!"|"?") as n,_), [_] ->
       char oc '('; name oc n; list_prefix " " raw_term oc ts; char oc ')'
     | _ ->
       char oc '('; raw_term oc h; list_prefix " " raw_term oc ts; char oc ')'
     end
  | Abs(u,v) ->
    string oc "(λ "; raw_decl_var oc u; string oc ", "; raw_term oc v;
    char oc ')'
;;

(* [unabbrev_term rmap oc t] prints on [oc] the term [t] with term
   variable renaming map [rmap] without using term abbreviations. A
   variable of type b not in [rmap] is replaced by [el b]. *)
let unabbrev_term =
  let rec term rmap oc t =
  match t with
  | Var(n,b) ->
     begin
       try name oc (List.assoc t rmap)
       with Not_found ->
         string oc "/*"; name oc n; string oc "*/(el "; raw_typ oc b;
         char oc ')'
     end
  | Const _ -> raw_term oc t
  | Comb _ ->
     let h, ts = head_args t in
     begin match h, ts with
     | Const("=" as n,_), [_;_]
     | Const(("!"|"?") as n,_), [_] ->
       char oc '('; name oc n; list_prefix " " (term rmap) oc ts;
       char oc ')'
     | _ ->
       char oc '('; term rmap oc h; list_prefix " " (term rmap) oc ts;
       char oc ')'
     end
  | Abs(u,v) ->
    let rmap' = add_var rmap u in
    string oc "(λ "; unabbrev_decl_var rmap' oc u; string oc ", ";
    term rmap' oc v; char oc ')'
  in term
;;

(* Htable recording the part of each abbreviation. *)
let htbl_abbrev_part : (int,int) Hashtbl.t = Hashtbl.create 100_000;;
let abbrev_part_of = Hashtbl.find htbl_abbrev_part;;

(* Dependencies on term abbreviations parts of the current proof part. *)
let abbrev_deps = ref SetInt.empty;;

(* Index of the current term_abbrevs_part file. *)
let abbrev_part = ref 1;;

(* Record the size of printed terms. *)
let abbrev_part_size = ref 0;;

(* Maximum size of a term_abbrev file. *)
let max_abbrev_part_size = ref max_int;;

(* Htable recording the maximum index of each abbrevs part. *)
let htbl_abbrev_part_max : (int,int) Hashtbl.t = Hashtbl.create 1_000;;

(* Htable recording the minimum index of each abbrevs part. *)
let htbl_abbrev_part_min : (int,int) Hashtbl.t = Hashtbl.create 1_000;;

(* Index of the last abbreviation. *)
let cur_abbrev = ref (-1);;

(* [abbrev_term oc t] prints on [oc] the term [t] or its abbreviation
   if [t] has already been abbreviated. *)
let abbrev_term =
  let abbrev oc t =
    let tvs, vs, bs, t = canonical_term t in
    let k =
      match TrmHashtbl.find_opt htbl_term_abbrev t with
      | Some (k,_,_) ->
         abbrev_deps := SetInt.add (abbrev_part_of k) !abbrev_deps;
         k
      | None ->
         let k = !cur_abbrev + 1 in
         let ltvs = List.length tvs in
         abbrev_part_size := !abbrev_part_size + !Xproof.step_size;
         if !abbrev_part_size > !max_abbrev_part_size then
           begin
             Hashtbl.add htbl_abbrev_part_max !abbrev_part !cur_abbrev;
             incr abbrev_part;
             Hashtbl.add htbl_abbrev_part_min !abbrev_part k;
             abbrev_part_size := 0
           end;
         cur_abbrev := k;
         let x = (k, ltvs, bs) in
         TrmHashtbl.add htbl_term_abbrev t x;
         Hashtbl.add htbl_abbrev_part k !abbrev_part;
         abbrev_deps := SetInt.add !abbrev_part !abbrev_deps;
         k
    in
    match tvs, vs with
    | [], [] -> string oc "term"; int oc k
    | _ ->
      string oc "(term"; int oc k; list_prefix " " raw_typ oc tvs;
      list_prefix " " raw_term oc vs; char oc ')'
  in
  let rec term oc t =
    let h,ts = head_args t in
    if List.for_all is_var_or_cst_term (h::ts) then raw_term oc t
    else
    match h,ts with
    | Const("=",_b),[u;v] ->
      string oc "(= "; (*typ oc (get_domain b); char oc ' ';*)
      term oc u; char oc ' '; term oc v; char oc ')'
    | _ -> abbrev oc t
  in term
;;

(* [rename rmap t] returns a new term obtained from [t] by applying
   [rmap] and by replacing variables not occurring in [rmap] by the
   constant [el]. *)
let rec rename rmap t =
  match t with
  | Var(_,b) -> (try mk_var(List.assoc t rmap,b) with Not_found -> mk_el b)
  | Const(_,_) -> t
  | Comb(u,v) -> Comb(rename rmap u, rename rmap v)
  | Abs(u,v) ->
     let rmap' = add_var rmap u in Abs(rename rmap' u,rename rmap' v)
;;

let term rmap oc t = abbrev_term oc (rename rmap t);;

(****************************************************************************)
(* Handling file dependencies. *)
(****************************************************************************)

let root_path = ref "HOLLight";;

let require oc n = out oc "require private open %s.%s;\n" !root_path n;;

(* [create_file_with_deps tmp n iter_deps gen] creates a file
   [tmp^".lp"], which will be renamed or included in [n^".lp"] in the
   end, and writes in it require commands following the dependency
   iterator [iter_deps], followed by [gen]. It also creates the file
   [n^".lpo.mk"] to record the dependencies of [n^".lpo"]. *)
let create_file_with_deps (tmp:string) (n:string)
      (iter_deps:(string->unit)->unit) (gen:out_channel->unit) =
  let oc_lp = log_open_out (tmp^".lp")
  and oc_mk = log_open_out (n^".lpo.mk") in
  out oc_mk "%s.lpo:" n;
  let handle dep =
    require oc_lp dep;
    out oc_mk " %s.lpo" dep;
  in
  handle "theory_hol";
  iter_deps handle;
  out oc_mk "\n";
  close_out oc_mk;
  gen oc_lp;
  close_out oc_lp
;;

let spec f n = f (n^"_spec");;

let export_iter n = create_file_with_deps n n;;

let export n deps = export_iter n (fun f -> List.iter f deps);;

(****************************************************************************)
(* Translation of term abbreviations. *)
(****************************************************************************)

(* map recording the number of type variables of each symbol *)
let tvs_map = ref MapStr.empty;;
let raw_update_tvs_map n k = tvs_map := MapStr.add n k !tvs_map;;
let update_tvs_map n tvs =
  if tvs <> [] then raw_update_tvs_map n (List.length tvs)

let print_let oc (t,t',_,_) =
  string oc "\n  let "; raw_term oc t'; string oc " ≔ "; raw_term oc t;
  string oc " in"
;;

let decl_term_abbrev oc t (k,ntvs,bs) =
  let n = "term"^string_of_int k in
  if ntvs > 0 then raw_update_tvs_map n ntvs;
  string oc "symbol "; string oc n;
  for i=0 to ntvs-1 do string oc " a"; int oc i done;
  let decl_var i b =
    string oc " (x"; int oc i; string oc ": El "; abbrev_typ oc b; char oc ')'
  in
  List.iteri decl_var bs;
  if !use_sharing then
    begin
      let t', l = shared t in
      string oc " ≔"; list print_let oc l; char oc ' '; raw_term oc t';
      string oc ";\n"
    end
  else
    begin
      string oc " ≔ "; raw_term oc t; string oc ";\n"
    end
;;

(* [decl_term_abbrevs oc] outputs on [oc] the term abbreviations. *)
let decl_term_abbrevs oc =
  TrmHashtbl.iter (decl_term_abbrev oc) htbl_term_abbrev
;;

(* [decl_subterm_abbrevs oc] outputs on [oc] the subterm abbreviations
   with no variables. *)
let decl_subterm_abbrevs =
  let add _ x l = match x with t,t',false,_ when t != t' -> x::l | _ -> l
  and cmp (_,_,_,k1) (_,_,_,k2) = k1 - k2 in
  fun oc ->
  let abbrev (t,t',_,_) =
    let n, tvs =
      match t' with
      | Var(n,b) | Const(n,b) -> n, tyvars b
      | _ -> assert false
    in
    update_tvs_map n tvs;
    string oc "symbol "; raw_term oc t'; string oc " ≔ "; raw_term oc t;
    string oc ";\n"
  in
  List.iter abbrev (List.sort cmp (TrmHashtbl.fold add htbl_subterms []))
;;

(****************************************************************************)
(* Translation of proofs. *)
(****************************************************************************)

(* In a theorem, the hypotheses [t1;..;tn] are given the names
   ["h1";..;"hn"]. *)
let hyp_var ts oc t = char oc 'h'; int oc (try 1 + index t ts with _ -> 0);;

(* [extend_to_bool ty_su tvs] extends the type substitution [ty_su] by
   mapping every type variable of [tvs] to [bool]. *)
let extend_to_bool = List.fold_left (fun su tv -> (bool_ty,tv)::su);;

(* Printing on the output channel [oc] of the subproof [p2] of index [i2]
given:
- tvs: list of type variables of the theorem
- rmap: renaming map for term variables
- ty_su: type substitution that needs to be applied
- tm_su: term substitution that needs to be applied
- ts1: hypotheses of the theorem *)
let subproof tvs rmap ty_su tm_su ts1 i2 oc p2 =
  let term = term rmap in
  let Proof(th2,_) = p2 in
  let ts2,t2 = dest_thm th2 in
  (* vs2 is the list of free term variables of th2 *)
  let vs2 = freesl (t2::ts2) in
  (* vs2 is now the application of tm_su on vs2 *)
  let vs2 = vsubstl tm_su vs2 in
  (* ts2 is now the application of tm_su on ts2 *)
  let ts2 = vsubstl tm_su ts2 in
  (* tvs2 are the list of type variables of th2 *)
  let tvs2 = type_vars_in_thm th2 in
  (* bs2 is the application of ty_su on tvs2 *)
  let bs2 = List.map (type_subst ty_su) tvs2 in
  (* tvbs2 is the type variables of bs2 *)
  let tvbs2 = tyvarsl bs2 in
  (* we remove from tvbs2 the variables of tvs *)
  let tvbs2 = remove_elts tvs tvbs2 in
  (* we extend ty_su by mapping every type variable of tvbs2 to bool *)
  let ty_su = extend_to_bool ty_su tvbs2 in
  match ty_su with
  | [] ->
     string oc "(@lem"; int oc i2; list_prefix " " typ oc tvs2;
     list_prefix " " term oc vs2; list_prefix " " (hyp_var ts1) oc ts2;
     char oc ')'
  | _ ->
     (* vs2 is now the application of ty_su on vs2 *)
     let vs2 = List.map (inst ty_su) vs2 in
     (* ts2 is now the application of ty_su on ts2 *)
     let ts2 = List.map (inst ty_su) ts2 in
     (* bs2 is the list of types obtained by applying ty_su on tvs2 *)
     let bs2 = List.map (type_subst ty_su) tvs2 in
     string oc "(@lem"; int oc i2; list_prefix " " typ oc bs2;
     list_prefix " " term oc vs2; list_prefix " " (hyp_var ts1) oc ts2;
     char oc ')'
;;

(* [proof tvs rmap oc p] prints on [oc] the proof [p] for a theorem
   with type variables [tvs] and free variables renaming map [rmap]. *)
let proof tvs rmap =
  let term = term rmap in
  let proof oc p =
    let Proof(thm,content) = p in
    let ts = hyp thm in
    let tvs' = extra_type_vars_in_proof_content proof_at content in
    let tvs' = remove_elts tvs tvs' in
    List.iter (fun tv -> out oc "let %a ≔ bool in " typ tv) tvs';
    let sub = subproof tvs rmap [] [] ts in
    let sub_at oc k = sub k oc (proof_at k) in
    match content with
    | Prefl(t) -> string oc "REFL "; term oc t
    | Psym k -> string oc "SYM "; sub_at oc k
    | Ptrans(k1,k2) ->
      string oc "TRANS "; sub_at oc k1; char oc ' '; sub_at oc k2
    | Pmkcomb(k1,k2) ->
      string oc "MK_COMB "; sub_at oc k1; char oc ' '; sub_at oc k2
    | Pabs(k,t) ->
       let rmap' = add_var rmap t in
       string oc "fun_ext (λ "; decl_var rmap' oc t; string oc ", ";
       subproof tvs rmap' [] [] ts k oc (proof_at k); char oc ')'
    | Pbeta(t) -> string oc "REFL "; term oc t
    | Passume(t) -> hyp_var (hyp thm) oc t
    | Peqmp(k1,k2) ->
      string oc "EQ_MP "; sub_at oc k1; char oc ' '; sub_at oc k2
    | Pdeduct(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       let Proof(th1,_) = p1 and Proof(th2,_) = p2 in
       let t1 = concl th1 and t2 = concl th2 in
       let n = 1 + List.length ts in
       string oc "prop_ext (λ h"; int oc n; string oc " : Prf "; term oc t1;
       string oc ", "; subproof tvs rmap [] [] (ts @ [t1]) k2 oc p2;
       string oc ") (λ h"; int oc n; string oc " : Prf "; term oc t2;
       string oc ", "; subproof tvs rmap [] [] (ts @ [t2]) k1 oc p1;
       char oc ')'
    | Pinst(k,s) -> subproof tvs rmap [] s ts k oc (proof_at k)
    | Pinstt(k,s) -> subproof tvs rmap s [] ts k oc (proof_at k)
    | Paxiom(t) ->
      string oc "@axiom_";
      int oc (pos_first (fun th -> concl th = t) !the_axioms);
      list_prefix " " typ oc (type_vars_in_term t);
      list_prefix " " term oc (frees t)
    | Pdef(t,n,_) ->
       char oc '@'; name oc n; string oc "_def";
       list_prefix " " typ oc (type_vars_in_term t)
    | Pdeft(_,t,_,_) ->
      string oc "@axiom_";
      int oc (pos_first (fun th -> concl th = t) !the_axioms);
      list_prefix " " typ oc (type_vars_in_term t);
      list_prefix " " term oc (frees t)
    | Ptruth -> string oc "⊤ᵢ"
    | Pconj(k1,k2) -> string oc "∧ᵢ "; sub_at oc k1; char oc ' '; sub_at oc k2
    | Pconjunct1 k -> string oc "∧ₑ₁ "; sub_at oc k
    | Pconjunct2 k -> string oc "∧ₑ₂ "; sub_at oc k
    | Pmp(k1,k2) -> sub_at oc k1; char oc ' '; sub_at oc k2
    | Pdisch(t,k) ->
      string oc "λ "; hyp_var ts oc t; string oc " : Prf "; term oc t;
      string oc ", "; sub_at oc k
    | Pspec(t,k) -> sub_at oc k; char oc ' '; term oc t
    | Pgen(x,k) ->
       let rmap' = add_var rmap x in
       string oc "λ "; decl_var rmap' oc x; string oc ", ";
       subproof tvs rmap' [] [] ts k oc (proof_at k)
    | Pexists(p,t,k) ->
      string oc "∃ᵢ "; term oc p; char oc ' '; term oc t; char oc ' ';
      sub_at oc k
    | Pdisj1(p,k) -> string oc "∨ᵢ₁ "; sub_at oc k; char oc ' '; term oc p
    | Pdisj2(p,k) -> string oc "∨ᵢ₂ "; term oc p; char oc ' '; sub_at oc k
    | Pdisj_cases(k1,k2,k3) ->
       let p1 = proof_at k1 in
       let Proof(th1,_) = p1 in
       let l,r = binop_args (concl th1) in
       string oc "∨ₑ "; sub k1 oc p1; string oc " (λ h0 : Prf "; term oc l;
       string oc ", "; sub_at oc k2; string oc ") (λ h0 : Prf "; term oc r;
       string oc ", "; sub_at oc k3; char oc ')'
    | Pchoose(v,k1,k2) ->
       let p1 = proof_at k1 in
       let Proof(th1,_) = p1 in
       begin match concl th1 with
       | Comb(_,p) ->
          let rmap' = add_var rmap v in
          string oc "∃ₑ "; sub k1 oc p1; string oc " (λ "; decl_var rmap' oc v;
          string oc ", λ h0 : Prf("; term oc p; char oc ' '; var rmap' oc v;
          string oc "), "; subproof tvs rmap' [] [] ts k2 oc (proof_at k2);
          char oc ')'
       | _ -> assert false
       end
  in proof
;;

(****************************************************************************)
(* Translation of type declarations and axioms. *)
(****************************************************************************)

let typ_arity oc k =
  for _ = 1 to k do string oc "Set → " done; string oc "Set";;

let decl_typ oc (n,k) =
  string oc "constant symbol "; typ_name oc n; string oc " : ";
  typ_arity oc k; string oc ";\n"
;;

let typ_vars oc ts =
  match ts with
  | [] -> ()
  | ts -> string oc " ["; list_sep " " typ oc ts; char oc ']'
;;

let typ_vars_set oc ts =
  match ts with
  | [] -> ()
  | ts -> string oc " ["; list_sep " " typ oc ts; string oc " : Set]"
;;

let typ_params = list_prefix " " raw_typ;;

let definition_of n =
  let f th =
    let t = concl th in
    match t with
    | Comb(Comb(Const("=",_),Const(n',_)),r) ->
       if n'=n then Some(t,r) else None
    | _ -> assert false
  in List.find_map f !the_definitions
;;

let decl_sym oc (hollight_name,b) =
  let n = lp_name hollight_name in
  let tvsb = tyvars b in
  update_tvs_map n tvsb;
  match definition_of hollight_name with
  | None ->
     string oc "symbol "; string oc n; typ_vars oc tvsb;
     string oc " : El "; raw_typ oc b; string oc ";\n"
  | Some (t,r) ->
     let tvst = type_vars_in_term t in
     update_tvs_map (n^"_def") tvst;
     let rmap = renaming_map tvst [] in
     match hollight_name with
     |"@"|"\\/"|"/\\"|"==>"|"!"|"?"|"?!"|"~"|"F"|"T" ->
       (* symbols already declared in theory_hol.lp *)
       string oc "symbol "; string oc n; string oc "_def"; typ_vars oc tvst;
       string oc " : Prf "; unabbrev_term rmap oc t; string oc ";\n"
     | _ ->
        string oc "symbol "; string oc n; typ_vars oc tvsb;
        string oc " : El "; raw_typ oc b; string oc " ≔ ";
        unabbrev_term rmap oc r; string oc ";\n";
        match tvsb with
        | [] ->
           string oc "opaque symbol "; string oc n; string oc "_def";
           typ_vars oc tvst; string oc " : Prf "; unabbrev_term rmap oc t;
           string oc " ≔ REFL "; string oc n; string oc ";\n"
        | _ ->
           string oc "opaque symbol "; string oc n; string oc "_def";
           typ_vars oc tvst; string oc " : Prf "; unabbrev_term rmap oc t;
           string oc " ≔ REFL (@"; string oc n; char oc ' ';
           typ_params oc tvsb; string oc ");\n"
;;

let decl_axioms oc ths =
  let axiom i th =
    let t = concl th in (* axioms have no assumptions *)
    let tvs = type_vars_in_term t in
    let xs = frees t in
    let rmap = renaming_map tvs xs in
    let n = "axiom_"^string_of_int i in
    update_tvs_map n tvs;
    string oc "symbol "; string oc n; typ_vars oc tvs;
    list (unabbrev_decl_param rmap) oc xs; string oc " : Prf ";
    unabbrev_term rmap oc t; string oc ";\n"
  in
  List.iteri axiom ths
;;

(****************************************************************************)
(* Translation of theorems and proofs. *)
(****************************************************************************)

type decl =
  | DefThmIdProof (* lemXXX : abbrev_type := proof *)
  | DeclThmId of (*abbrev:*)bool (* lemXXX : [un]abbrev_type *)
  | DefThmNameAsThmId of string (* name : unabbrev_type := lemXXX *)
  | DeclThmName of string (* name : unabbrev_type *)
;;

(* [!proof_part_max_idx] indicates the maximal index of the current part. *)
let proof_part_max_idx = ref (-1);;

(* [decl_theorem oc k p d] outputs on [oc] the theorem of index [k]
   and proof [p] as declaration type [d]. *)
let decl_theorem oc k p d =
  let Proof(thm,pc) = p in
  (*log "theorem %d ...\n%!" k;*)
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let decl_hyp term i t =
    string oc " (h"; int oc (i+1); string oc " : Prf "; term oc t; char oc ')'
  in
  let decl_hyps term = List.iteri (decl_hyp term) in
  match d with
  | DefThmIdProof ->
    let n = "lem"^string_of_int k in
    let tvs = type_vars_in_thm thm in
    update_tvs_map n tvs;
    let extras = extra_type_vars_in_proof_content proof_at pc in
    let rmap = renaming_map (extras @ tvs) xs in
    let term = term rmap in
    let prv = let l = get_use k in l > 0 && l <= !proof_part_max_idx in
    string oc (if prv then "private" else "opaque");
    string oc " symbol "; string oc n; typ_vars oc tvs;
    list (decl_param rmap) oc xs; decl_hyps term ts;
    string oc " : Prf "; term oc t;
    string oc " ≔ "; proof tvs rmap oc p; string oc ";\n";
  | DeclThmId abbrev ->
    let n = "lem"^string_of_int k in
    let tvs = type_vars_in_thm thm in
    update_tvs_map n tvs;
    let rmap = renaming_map tvs xs in
    let term = if abbrev then term rmap else unabbrev_term rmap in
    string oc "symbol "; string oc n; typ_vars oc tvs;
    list (unabbrev_decl_param rmap) oc xs; decl_hyps term ts;
    string oc " : Prf "; term oc t; string oc ";\n"
  | DefThmNameAsThmId n ->
    let tvs = type_vars_in_thm thm in
    update_tvs_map n tvs;
    let rmap = renaming_map tvs xs in
    let term = unabbrev_term rmap in
    string oc "opaque symbol "; string oc n; string oc " : ";
    if tvs <> [] || xs <> [] || ts <> [] then
      begin
        string oc "Π ";
        typ_vars_set oc tvs; list (unabbrev_decl_param rmap) oc xs;
        decl_hyps term ts;
        string oc ", ";
      end;
    string oc "Prf "; term oc t;
    string oc " ≔ @lem"; int oc k; string oc ";\n"
  | DeclThmName n ->
    let tvs = type_vars_in_thm thm in
    update_tvs_map n tvs;
    let rmap = renaming_map tvs xs in
    let term = unabbrev_term rmap in
    string oc "symbol "; string oc n;
    typ_vars oc tvs; list (unabbrev_decl_param rmap) oc xs;
    decl_hyps term ts;
    string oc " : Prf "; term oc t; string oc ";\n"
;;

(* [theorem oc k p] outputs on [oc] the proof [p] of index [k]. *)
let theorem oc k p = decl_theorem oc k p DefThmIdProof;;

(* [theorem_as_axiom abbrev oc k p] outputs on [oc] the proof [p] of index
   [k] as an axiom, with abbreviated terms if [abbrev]. *)
let theorem_as_axiom abbrev oc k p = decl_theorem oc k p (DeclThmId abbrev);;

(* [proofs_in_interval oc x y] outputs on [oc] the proofs in interval
   [x] .. [y]. *)
let proofs_in_interval oc x y =
  for k = x to y do
    if get_use k >= 0 then theorem oc k (proof_at k)
  done
;;

(* Used in single file generation.
   [proofs_in_range oc r] outputs on [oc] the proofs in range [r]. *)
let proofs_in_range oc = function
  | Only x ->
     let p = proof_at x in
     List.iter (fun k -> theorem_as_axiom false oc k (proof_at k)) (deps p);
     theorem oc x p(*;
     out oc
"flag \"print_implicits\" on;
flag \"print_domains\" on;
print lem%d;\n" x*)
  | All ->
     proofs_in_interval oc !the_start_idx
       (!the_start_idx + Array.length !prf_pos - 1)
  | Upto y -> proofs_in_interval oc 0 y
  | Inter(x,y) -> proofs_in_interval oc x y
;;

(****************************************************************************)
(* Generate type and term abbreviation files. *)
(****************************************************************************)

(* In single file generation.
   [export_type_abbrevs b n] generates [n^"_type_abbrevs.lp"]. *)
let export_type_abbrevs b n =
  export (n^"_type_abbrevs") [b^"_types"] decl_type_abbrevs
;;

(* [export_subterm_abbrevs b n] generates [n^"_subterm_abbrevs.lp"]. *)
let export_subterm_abbrevs b n =
  export (n^"_subterm_abbrevs") [b^"_types";b^"_type_abbrevs";b^"_terms"]
    decl_subterm_abbrevs
;;

(* 2nd step in command "theorem" when n is NOT in BIG_FILES.
   [export_term_abbrevs_in_one_file b n] generates
   [n^"_term_abbrevs.lp"] and [n^"_term_abbrevs.typ"]. *)
let export_term_abbrevs_in_one_file b n =
  begin
    if !use_sharing then
      let deps =
        [b^"_types";b^"_type_abbrevs";b^"_terms";n^"_subterm_abbrevs"] in
      export (n^"_term_abbrevs") deps decl_term_abbrevs;
      export_subterm_abbrevs b n
    else
      let deps = [b^"_types";b^"_type_abbrevs";b^"_terms"] in
      export (n^"_term_abbrevs") deps decl_term_abbrevs
  end;
  write_val (n^"_term_abbrevs.typ") !map_typ_abbrev
;;

(* Called in command "abbrev" used in Makefile.
   [export_theorem_term_abbrevs b n k] generates the files
   [n^"_term_abbrevs"^part(k)^".lp"], assuming that the files
   [n^".brp"] and [n^"_term_abbrevs"^part(k)^".min"] already exist. *)
let export_theorem_term_abbrevs_part b n k =
  let p = n^"_term_abbrevs"^part k in
  (* generate [p^"_tail.lp"] *)
  let pos : int array = read_val (n^".brp")
  and (min, max) : int * int = read_val (p^".min") in
  read_file_bin (n^".brv")
    (fun ic ->
      if max >= 0 then seek_in ic pos.(min);
      let term_abbrevs oc =
        for _ = min to max do
          let t,x = input_value ic in
          decl_term_abbrev oc t x
        done
      in
      create_file (p^"_tail.lp") term_abbrevs);
  (* generate [p^".typ"] *)
  write_val (p^".typ") !map_typ_abbrev;
  (* generate [p^"_head.lp"] *)
  let iter_deps f =
    f (b^"_types");
    f (b^"_terms");
    f (b^"_type_abbrevs");
    if !use_sharing then f (p^"_subterm_abbrevs")
  in
  create_file_with_deps (p^"_head") p iter_deps (fun _ -> ());
  (* generate [p^".lp"] *)
  Xlib.concat [p^"_head.lp";p^"_tail.lp"] (p^".lp");
  Xlib.remove [p^"_head.lp";p^"_tail.lp"]
;;

(****************************************************************************)
(* Generate proof files. *)
(****************************************************************************)

(* Maximum number of proof steps in a proof file. *)
let max_proof_part_size = ref max_int;;

(* Current proof part. *)
let proof_part = ref 0;;

(* Dependencies on term abbreviations parts of each proof part. *)
let htbl_abbrev_deps = Hashtbl.create 1_000;;

(* Dependencies on previous parts of each proof part. *)
let htbl_proof_deps = Hashtbl.create 1_000;;

(* Dependencies on named theorems of each proof part. *)
let htbl_thm_deps = Hashtbl.create 1_000;;

(* Htable recording in which proof part is every theorem. *)
let htbl_thm_part = Hashtbl.create 1_000_000;;
let proof_part_of = Hashtbl.find htbl_thm_part;;

(* Dependencies on previous proof parts of the current proof part. *)
let proof_deps = ref SetInt.empty;;

(* Used in [export_theorem_proof],
   1st step in command "theorem" when n is NOT in BIG_FILES.
   [export_proofs_in_interval n x y] generates the proof steps of
   index between [x] and [y] in the files [n^part(k)^"_proofs.lp"]. *)
let export_proofs_in_interval n x y =
  let proof_part_size = ref 0 in
  let cur_oc = ref stdout in
  let start_part k =
    incr proof_part;
    let f = n^part !proof_part^"_proofs.lp" in
    log_gen f;
    cur_oc := open_out f;
    proof_part_size := 0;
    abbrev_deps := SetInt.empty;
    proof_deps := SetInt.empty;
    thdeps := SetStr.empty;
    (* compute proof_part_max_idx *)
    let i = ref k and size = ref 0 in
    while (!i <= y && !size < !max_proof_part_size) do
      if get_use !i >= 0 then size := !size + size_proof_at !i;
      incr i
    done;
    proof_part_max_idx := !i - 2
  in
  let end_part() =
    close_out !cur_oc;
    Hashtbl.add htbl_abbrev_deps !proof_part !abbrev_deps;
    Hashtbl.add htbl_proof_deps !proof_part !proof_deps;
    Hashtbl.add htbl_thm_deps !proof_part !thdeps;
  in
  Hashtbl.add htbl_abbrev_part_min 1 0;
  proof_part := 0;
  start_part x;
  let add_dep d =
    try
      let pd = proof_part_of d in
      if pd < !proof_part then proof_deps := SetInt.add pd !proof_deps
    with Not_found -> ()
  in
  for k = x to y do
    if get_use k >= 0 then
      begin
        proof_part_size := !proof_part_size + size_proof_at k;
        if !proof_part_size > !max_proof_part_size then
          (end_part(); start_part k);
        Hashtbl.add htbl_thm_part k !proof_part;
        let p = proof_at k in
        List.iter add_dep (deps p);
        theorem !cur_oc k p;
      end
  done;
  end_part();
  Hashtbl.add htbl_abbrev_part_max !abbrev_part !cur_abbrev
;;

(* 1st step in command "theorem" when n is NOT in BIG_FILES.
  [export_theorem_proof b n] generates the files
  [n^part(k)^"_proofs.lp"] for [1<=k<!proof_part], [n^"_proofs.lp"],
  [n^".typ"] and [n^"_spec.lp"]. *)
let export_theorem_proof b n =
  let thid = !the_start_idx + Array.length !prf_pos - 1 in
  export_proofs_in_interval n !the_start_idx thid;
  Xlib.rename (n^part !proof_part^"_proofs.lp") (n^"_proofs.lp");
  write_val (n^".typ") !map_typ_abbrev;
  export (n^"_spec") [b^"_types";b^"_terms"]
    (fun oc ->
      for k = !the_start_idx to thid do
        let l = get_use k in
        if l=0 || l>thid then theorem_as_axiom false oc k (proof_at k)
      done)
;;

(* 3rd step in command "theorem" when n is NOT in BIG_FILES.
   [export_theorem_deps b n] generates for [1<=i<=!proof_part] the
   files [n^part(i)^"_deps.lp"] and [n^part(i)^".lp"] assuming that
   the files [n^part(i)^"_proofs.lp"] are already generated. *)
let export_theorem_deps b n =
  for i = 1 to !proof_part do
    let p = if i < !proof_part then n^part i else n in
    let iter_deps f =
      f (b^"_types");
      f (b^"_terms");
      f (b^"_axioms");
      f (b^"_type_abbrevs");
      if !use_sharing then f (n^"_subterm_abbrevs");
      SetInt.iter (fun j -> if j=1 then f (n^"_term_abbrevs")
                            else f (n^"_term_abbrevs"^part j))
        (Hashtbl.find htbl_abbrev_deps i);
      SetInt.iter (fun j -> f (n^part j)) (Hashtbl.find htbl_proof_deps i);
      SetStr.iter (spec f) (Hashtbl.find htbl_thm_deps i);
    in
    create_file_with_deps (p^"_deps") p iter_deps (fun _ -> ());
    Xlib.concat [p^"_deps.lp";p^"_proofs.lp"] (p^".lp");
    Xlib.remove [p^"_deps.lp";p^"_proofs.lp"]
  done
;;

(* Called by command "thmsplit" in Makefile when f is in BIG_FILES.
   [split_theorem_proof b n] generates the files [n^part(k)^".idx"],
   [n^".max"], [n^".lp"] and [n^"_spec.lp"]. *)
let split_theorem_proof b n =
  let x = !the_start_idx
  and y = !the_start_idx + Array.length !last_use - 1
  and part_size = ref 0
  and min = ref !the_start_idx
  and ht_part_max = Hashtbl.create 1_000 in
  proof_part := 1;
  Hashtbl.add ht_part_max 0 (-1);
  for k = x to y do
    if get_use k >= 0 then
      begin
        part_size := !part_size + size_proof_at k;
        if !part_size > !max_proof_part_size then
          begin
            let max = k-1 in
            write_val (n^part !proof_part^".idx") (!min,max);
            Hashtbl.add ht_part_max !proof_part max;
            incr proof_part;
            min := k;
            part_size := 0
          end
      end;
  done;
  let max = y in
  write_val (n^part !proof_part^".idx") (!min,max);
  Hashtbl.add ht_part_max !proof_part max;
  let max_of =
    Array.init (Hashtbl.length ht_part_max) (Hashtbl.find ht_part_max) in
  write_val (n^".max") max_of;
  (* generate [n^".lp"] and [n^"_spec.lp"].
     Remark: these two files are identical. *)
  let iter_deps f =
    f (b^"_types");
    f (b^"_terms");
    spec f (n^part !proof_part);
  in
  let p = proof_at max in
  let t = DefThmNameAsThmId ("lem"^string_of_int max) in
  export_iter n iter_deps (fun oc -> decl_theorem oc max p t);
  export_iter (n^"_spec") iter_deps (fun oc -> decl_theorem oc max p t)
;;

(* Called in [export_theorem_proof_part] which is called by command
   "thmpart" in Makefile when n is in BIG_FILES.
   [split_theorem_abbrevs n] generates the files [n^".brv"],
   [n^".brp"], [n^"_term_abbrevs"^part(k)^".min"] and
   [n^"_term_abbrevs"^part(k)^".max"]. *)
let split_theorem_abbrevs n =
  (* generate the file [n^".brv"]. *)
  let l = TrmHashtbl.fold (fun t x acc -> (t,x)::acc) htbl_term_abbrev [] in
  let cmp (_,(k1,_,_)) (_,(k2,_,_)) = Stdlib.compare k1 k2 in
  let l = List.sort cmp l in
  create_file_bin (n^".brv") (fun oc -> List.iter (output_value oc) l);
  (* generate the file [n^".brp"]. *)
  let len = TrmHashtbl.length htbl_term_abbrev in
  let pos = Array.make len 0 in
  let size = Array.make len 0 in
  read_file_bin (n^".brv")
    (fun ic ->
      for k = 0 to len - 1 do
        Array.set pos k (pos_in ic);
        Array.set size k (size_abbrev (input_value ic))
      done);
  write_val (n^".brp") pos;
  (* generate the files [n^"_term_abbrevs"^part(k)^".min"] *)
  let f = n^"_term_abbrevs"
  and nb_parts = ref 1
  and min = ref 0
  and ht_part_max = Hashtbl.create 1_000
  and k = ref 0
  and abbrev_part_size = ref 0 in
  Hashtbl.add ht_part_max 0 (-1);
  while !k < len do
    min := !k;
    abbrev_part_size := 0;
    while !k < len && !abbrev_part_size < !max_abbrev_part_size do
      abbrev_part_size := !abbrev_part_size + size.(!k);
      incr k;
    done;
    if !k < len then
      begin
        let max = !k - 1 in
        write_val (f^part !nb_parts^".min") (!min,max);
        Hashtbl.add ht_part_max !nb_parts max;
        incr nb_parts
      end
  done;
  let max = len - 1 in
  write_val (f^part !nb_parts^".min") (!min,max);
  Hashtbl.add ht_part_max !nb_parts max;
  write_val (n^".max") (array_of_hashtbl ht_part_max);
  !nb_parts
;;

(* Called by command "thmpart" in Makefile when n is in BIG_FILES.
   [export_theorem_proof_part b n k] generates the files [n^part(k)^".lp"],
   [n^part(k)^".typ"], [n^part(k)^".brv"], [n^part(k)^".brp"],
   [n^part(k)^"_term_abbrevs"^part(i)^".min"], [n^part(k)^"_spec.lp"],
   [n^part(k)^"_subterm_abbrevs.lp"] (if !use_sharing). *)
let export_theorem_proof_part b n k =
  (* generate [n^part(k)^"_proofs.lp"] *)
  proof_part := k;
  let p = n^part k in
  let (min,max) = read_val (p^".idx")
  and max_of = read_val (n^".max")
  and part_deps = ref SetInt.empty in
  let part_of i =
    let p = ref (k-1) in while i <= max_of.(!p) do decr p done; !p + 1 in
  let add_dep d =
    let p = part_of d in
    if p <> !proof_part then part_deps := SetInt.add p !part_deps
  in
  create_file (p^"_body.lp")
    (fun oc ->
      create_file (p^"_spec_body.lp")
        (fun oc_spec ->
          proof_part_max_idx := max - 1;
          for k = min to max do
            let l = get_use k in
            if l >= 0 then
              begin
                let p = proof_at k in
                List.iter add_dep (deps p);
                theorem oc k p;
                if l = 0 || l >= max then theorem_as_axiom true oc_spec k p
              end
          done));
  (* dump term abbreviations *)
  let nb_parts = split_theorem_abbrevs p in
  (* generate [n^part(k)^".typ"] *)
  write_val (p^".typ") !map_typ_abbrev;
  (* generate [n^part(k)^"_subterm_abbrevs.lp"] *)
  if !use_sharing then export_subterm_abbrevs b p;
  (* generate [n^part(k)^"_deps.lp"] *)
  let iter_deps f =
    f (b^"_types");
    f (b^"_terms");
    f (b^"_axioms");
    SetStr.iter (spec f) !thdeps;
    SetInt.iter (fun j -> spec f (n^part j)) !part_deps;
    f (b^"_type_abbrevs");
    if !use_sharing then f (p^"_subterm_abbrevs");
    for j = 1 to nb_parts do f (p^"_term_abbrevs"^part j) done
  in
  create_file_with_deps (p^"_deps") p iter_deps (fun _ -> ());
  (* generate [n^part(k)^"_spec_deps.lp"] *)
  let iter_deps f =
    f (b^"_types");
    f (b^"_terms");
    f (b^"_type_abbrevs");
    if !use_sharing then f (p^"_subterm_abbrevs");
    for j = 1 to nb_parts do f (p^"_term_abbrevs"^part j) done
  in
  create_file_with_deps (p^"_spec_deps") (p^"_spec") iter_deps (fun _ -> ());
  (* generate [n^part(k)^".lp"] and [n^part(k)^"_spec.lp"] *)
  Xlib.concat [p^"_deps.lp";p^"_body.lp"] (p^".lp");
  Xlib.concat [p^"_spec_deps.lp";p^"_spec_body.lp"] (p^"_spec.lp");
  Xlib.remove [p^"_deps.lp";p^"_body.lp";p^"_spec_deps.lp";p^"_spec_body.lp"]
;;

(****************************************************************************)
(* Lambdapi file generation with type and term abbreviations. *)
(****************************************************************************)

(* Functions called in single file generation and by the command "sig"
   in b.mk and Makefile. *)

let types() =
  let f (n,_) = match n with "bool" | "fun" -> false | _ -> true in
  List.filter f (types())
;;

let export_types b =
  export (b^"_types") [] (fun oc -> list decl_typ oc (types()))
;;

let constants() =
  let f (n,_) = match n with "=" | "el" -> false | _ -> true in
  List.filter f (constants())
;;

let export_terms b =
  let n = b^"_terms" in
  export n [b^"_types"] (fun oc -> list decl_sym oc (constants()))
;;

let export_axioms b =
  let n = b^"_axioms" in
  export n [b^"_types"; b^"_terms"]
    (fun oc -> decl_axioms oc !the_axioms)
;;

(* Used in single file generation. Generate b_proofs.lp. *)
let export_proofs b r =
  let iter_proofs_deps f =
    f (b^"_types");
    f (b^"_type_abbrevs");
    f (b^"_terms");
    f (b^"_axioms");
    if !use_sharing then f (b^"_subterm_abbrevs");
    f (b^"_term_abbrevs")(*;
    for k = 2 to !abbrev_part do f (b^"_term_abbrevs"^part k) done*)
  in
  export_iter (b^"_proofs") iter_proofs_deps (fun oc -> proofs_in_range oc r)
;;

(* Generate a declaration of the form "thm_name : type", or "thm_name
   : type := lemXXX" if [with_proof], for each named theorem. The
   prefix "thm_" is used to avoid clashes with terms. *)
let out_map_thid_name map_thid_name cond with_proof oc =
  MapInt.iter
    (fun k n ->
      if cond k n
      then if with_proof then
             decl_theorem oc k (proof_at k) (DefThmNameAsThmId ("thm_"^n))
           else decl_theorem oc k (proof_at k) (DeclThmName ("thm_"^n)))
    map_thid_name
;;

(* Called in single file generation. Generate f.lp with a declaration
   of the form "name : type := lemXXX" for each named theorem. *)
let single_export_theorems f b map_thid_name =
  export f [b^"_types";b^"_terms";b^"_proofs"]
    (out_map_thid_name map_thid_name (fun _ _ -> true) true)
;;

(* Called in Makefile by the command "axm". Generate f.lp with, for
   each named theorem name, a declaration "symbol thm_name : type". *)
let export_theorems f b map_thid_name cond =
  export f [b^"_types";b^"_terms"]
    (out_map_thid_name map_thid_name cond false)
;;

(* Called in b.mk by the command "part" to create b_part_k and the
   associated type and term abbreviation files. *)
let export_proofs_part b dg k x y =
  let iter_proofs_part_deps f =
    f (b^"_types");
    f (b^"_type_abbrevs");
    f (b^"_terms");
    f (b^part k^"_term_abbrevs");
    f (b^"_axioms");
    for i = 1 to k-1 do if dg.(k-1).(i-1) > 0 then f (b^part i) done
  in
  proof_part_max_idx := y;
  export_iter (b^part k) iter_proofs_part_deps
    (fun oc -> proofs_in_interval oc x y)
;;

(* Called in b.mk by the command "thm" to create b.lp with, for each
   named theorem, a definition of the form "name := lemXXX", where XXX
   is the index of name. *)
let export_theorems_part k b map_thid_name =
  let iter_theorems_part_deps f =
    f (b^"_types");
    f (b^"_terms");
    f (b^"_axioms");
    for i = 1 to k do f (b^part i) done
  in
  export_iter b iter_theorems_part_deps
    (out_map_thid_name map_thid_name (fun _ _ -> true) false)
;;
