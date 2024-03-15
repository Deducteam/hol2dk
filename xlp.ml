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
let name =
  let prefixes = (* the order is important *)
    [ "|----", "vdash4"
    ; "|---", "vdash3"
    ; "|--", "vdash2"
    ; "|-", "vdash"
    ; "|=>", "bar_imp"]
  in
  fun oc n ->
  string oc
    begin match n with
    | "" -> assert false
    | "," -> "̦‚" (* 201A *)
    | "@" -> "ε"
    | "\\/" -> "∨"
    | "/\\" -> "∧"
    | "==>" -> "⇒"
    | "!" -> "∀"
    | "?" -> "∃"
    | "?!" -> "∃!"
    | "~" -> "¬"
    | "-->" -> "⟶" (* 27F6 *)
    | "<->" -> "↔" (* 2194 *)
    (* invalid Lambdapi identifiers *)
    | "$" -> "﹩" (* FE69 *)
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
    end
;;

let cst_name = name;;

(****************************************************************************)
(* Translation of types. *)
(****************************************************************************)

let typ_name oc n =
  string oc
    begin match n with
     | "" -> assert false
       (* type names used also as constant names are capitalized *)
     |"sum"|"topology"|"metric"|"multiset"|"group" ->
       String.capitalize_ascii n
     | n ->
        if n.[0] = '?' then "_" ^ String.sub n 1 (String.length n - 1)
        else n
    end
;;

let rec raw_typ oc b =
  match b with
  | Tyvar n
  | Tyapp(n,[]) -> typ_name oc n
  | Tyapp(n,bs) -> out oc "(%a%a)" typ_name n (list_prefix " " raw_typ) bs
;;

let abbrev_typ =
  let idx = ref (-1) in
  fun oc b ->
  match b with
  | Tyvar n
  | Tyapp(n,[]) -> typ_name oc n
  | _ ->
     (* check whether the type is already abbreviated; add a new
        abbreviation if needed *)
     let tvs, b = canonical_typ b in
     let k =
       match TypHashtbl.find_opt htbl_type_abbrev b with
       | Some (k,_) -> k
       | None ->
          let k = !idx + 1 in
          idx := k;
          let x = (k, List.length tvs) in
          TypHashtbl.add htbl_type_abbrev b x;
          k
     in
     match tvs with
     | [] -> out oc "type%d" k
     | _ -> out oc "(type%d%a)" k (list_prefix " " raw_typ) tvs
;;

let typ = abbrev_typ;;
  (*if !use_abbrev then abbrev_typ oc b else raw_typ oc b;;*)

(* [decl_type_abbrevs oc] outputs on [oc] the type abbreviations. *)
let decl_type_abbrevs oc =
  let abbrev b (k,n) =
    out oc "symbol type%d" k;
    for i=0 to n-1 do out oc " a%d" i done;
    (* We can use [raw_typ] here since [b] canonical. *)
    out oc " ≔ %a;\n" raw_typ b
  in
  (*List.iter abbrev
    (List.sort (fun (_,(k1,_)) (_,(k2,_)) -> k1 - k2)
       (MapTyp.fold (fun b x l -> (b,x)::l) m []))*)
  TypHashtbl.iter abbrev htbl_type_abbrev
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
    | Var(n,_) -> out oc "%a /*not found*/" name n
    | _ -> assert false*)
;;

let raw_decl_var oc t =
  match t with
  | Var(n,b) -> out oc "%a : El %a" name n typ b
  | _ -> assert false
;;

let decl_var rmap oc t =
  match t with
  | Var(_,b) -> out oc "%a : El %a" (var rmap) t typ b
  | _ -> assert false
;;

let unabbrev_decl_var rmap oc t =
  match t with
  | Var(_,b) -> out oc "%a : El %a" (var rmap) t raw_typ b
  | _ -> assert false
;;

let decl_param rmap oc v = out oc " (%a)" (decl_var rmap) v;;

let unabbrev_decl_param rmap oc v = out oc " (%a)" (unabbrev_decl_var rmap) v;;

(****************************************************************************)
(* Translation of terms. *)
(****************************************************************************)

let rec raw_term oc t =
  match t with
  | Var(n,_) -> name oc n
  | Const(n,b) ->
     begin match const_typ_vars_pos n with
     | [] -> cst_name oc n
     | ps ->
        let typ_args oc ps =
          List.iter (fun p -> out oc " %a" raw_typ (subtyp b p)) ps in
        out oc "(@%a%a)" cst_name n typ_args ps
     end
  | Comb _ ->
     let h, ts = head_args t in
     begin match h, ts with
     | Const(("=") as n,_), [_;_]
     | Const(("!"|"?") as n,_), [_] ->
        out oc "(%a%a)" cst_name n (list_prefix " " raw_term) ts
     | _ -> out oc "(%a%a)" raw_term h (list_prefix " " raw_term) ts
     end
  | Abs(u,v) -> out oc "(λ %a, %a)" raw_decl_var u raw_term v
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
       with Not_found -> out oc "/*%a*/(el %a)" name n raw_typ b
     end
  | Const _ -> raw_term oc t
  | Comb _ ->
     let h, ts = head_args t in
     begin match h, ts with
     | Const(("=") as n,_), [_;_]
     | Const(("!"|"?") as n,_), [_] ->
        out oc "(%a%a)" cst_name n (list_prefix " " (term rmap)) ts
     | _ -> out oc "(%a%a)" (term rmap) h (list_prefix " " (term rmap)) ts
     end
  | Abs(u,v) ->
     let rmap' = add_var rmap u in
     out oc "(λ %a, %a)" (unabbrev_decl_var rmap') u (term rmap') v
  in term
;;

(* Htable recording the part of each abbreviation. *)
let htbl_abbrev_part : (int,int) Hashtbl.t = Hashtbl.create 100_000;;
let part_of = Hashtbl.find htbl_abbrev_part;;

(* Dependencies on term abbreviations parts of the current proof part. *)
let proof_abdeps = ref SetInt.empty;;

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
  (*let oc_abbrevs = open_out "term_abbrevs" in*)
  let abbrev oc t =
    let tvs, vs, bs, t, n = canonical_term t in
    let k =
      match TrmHashtbl.find_opt htbl_term_abbrev t with
      | Some (k,_,_) ->
         proof_abdeps := SetInt.add (part_of k) !proof_abdeps;
         k
      | None ->
         let k = !cur_abbrev + 1 in
         let ltvs = List.length tvs and lvs = List.length vs in
         abbrev_part_size := !abbrev_part_size + n + 1 + ltvs + lvs;
         if !abbrev_part_size > !max_abbrev_part_size then
           begin
             Hashtbl.add htbl_abbrev_part_max !abbrev_part !cur_abbrev;
             incr abbrev_part;
             Hashtbl.add htbl_abbrev_part_min !abbrev_part k;
             abbrev_part_size := 0
           end;
         (*if k mod 1000 = 0 then log "term abbrev %d\n%!" k;*)
         (*out oc_abbrevs "%a\n\n" raw_term t;*)
         cur_abbrev := k;
         let x = (k, ltvs, bs) in
         TrmHashtbl.add htbl_term_abbrev t x;
         Hashtbl.add htbl_abbrev_part k !abbrev_part;
         proof_abdeps := SetInt.add !abbrev_part !proof_abdeps;
         k
    in
    match tvs, vs with
    | [], [] -> out oc "term%d" k
    | _ ->
       out oc "(term%d%a%a)"
         k (list_prefix " " raw_typ) tvs (list_prefix " " raw_term) vs
  in
  let rec term oc t =
    match t with
    | Var(_,_) | Const(_,_) -> raw_term oc t
    | Comb(Comb(Const("=",b),u),v) ->
       out oc "(@= %a %a %a)" typ (get_domain b) term u term v
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
  (*if !use_abbrev then abbrev_term oc (rename rmap t)
  else unabbrev_term rmap oc (rename rmap t);;*)

(****************************************************************************)
(* Handling of file dependencies. *)
(****************************************************************************)

let require oc n = out oc "require open hol-light.%s;\n" n;;

(* [create n iter_deps] creates a file [n^".lp"] and returns its
   out_channel. It also adds in it require commands following the
   dependency iterator [iter_deps], and creates the files
   [n^".lpo.mk"] and [n^".vo.mk"] to record the dependencies of
   [n^".lpo"] and [n^".vo"] respectively. *)
let create (p:string) (iter_deps:(string->unit)->unit) =
  let oc_lp = open_file (p^".lp")
  and oc_lpo_mk = open_file (p^".lpo.mk") in
  out oc_lpo_mk "%s.lpo:" p;
  let handle dep =
    require oc_lp dep;
    out oc_lpo_mk " %s.lpo" dep;
  in
  handle "theory_hol";
  iter_deps handle;
  out oc_lpo_mk "\n";
  close_out oc_lpo_mk;
  oc_lp
;;

let export_iter p iter_deps f =
  let oc = create p iter_deps in f oc; close_out oc
;;

let export p deps = export_iter p (fun h -> List.iter h deps);;

(****************************************************************************)
(* Translation of term abbreviations. *)
(****************************************************************************)

let print_let oc (t,t',_,_) =
  out oc "\n  let %a ≔ %a in" raw_term t' raw_term t;;

let abbrev oc t (k,n,bs) =
  out oc "symbol term%d" k;
  for i=0 to n-1 do out oc " a%d" i done;
  (* We can use [abbrev_typ] here since [bs] are canonical. *)
  List.iteri (fun i b -> out oc " (x%d: El %a)" i abbrev_typ b) bs;
  (* We can use [raw_term] here since [t] is canonical. *)
  if !use_sharing then
    let t', l = shared t in
    out oc " ≔%a %a;\n" (list print_let) l raw_term t'
  else out oc " ≔ %a;\n" raw_term t
;;

(* [decl_term_abbrevs oc] outputs on [oc] the term abbreviations. *)
let decl_term_abbrevs oc = TrmHashtbl.iter (abbrev oc) htbl_term_abbrev;;

(* [decl_subterm_abbrevs oc] outputs on [oc] the subterm abbreviations
   with no variables. *)
let decl_subterm_abbrevs =
  let add _ x l = match x with t,t',false,_ when t != t' -> x::l | _ -> l
  and cmp (_,_,_,k1) (_,_,_,k2) = k1 - k2 in
  fun oc ->
  (* print closed subterm abbreviations *)
  let abbrev (t,t',_,_) = out oc "symbol %a ≔ %a;\n" raw_term t' raw_term t in
  List.iter abbrev (List.sort cmp (TrmHashtbl.fold add htbl_subterms []))
;;

(****************************************************************************)
(* Translation of proofs. *)
(****************************************************************************)

(* In a theorem, the hypotheses [t1;..;tn] are given the names
   ["h1";..;"hn"]. *)
let hyp_var ts oc t = out oc "h%d" (try 1 + index t ts with _ -> 0);;

(* Printing on the output channel [oc] of the subproof [p2] given:
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
  (* tvs2 are the lst of type variables of th2 *)
  let tvs2 = type_vars_in_thm th2 in
  (* bs2 is the application of ty_su on tvs2 *)
  let bs2 = List.map (type_subst ty_su) tvs2 in
  (* tvbs2 is the type variables of bs2 *)
  let tvbs2 = tyvarsl bs2 in
  (* we remove from tvbs2 the variables of tvs *)
  let tvbs2 =
    List.fold_left
      (fun tvbs2 tv -> if List.mem tv tvs then tvbs2 else tv::tvbs2)
      [] tvbs2
  in
  (* we extend ty_su by mapping every type variable of tvbs2 to bool *)
  let ty_su =
    List.fold_left
      (fun su tv -> (bool_ty,tv)::su)
      ty_su tvbs2
  in
  match ty_su with
  | [] ->
     out oc "(@lem%d%a%a%a)" i2 (list_prefix " " typ) tvs2
       (list_prefix " " term) vs2 (list_prefix " " (hyp_var ts1)) ts2
  | _ ->
     (* vs2 is now the application of ty_su on vs2 *)
     let vs2 = List.map (inst ty_su) vs2 in
     (* ts2 is now the application of ty_su on ts2 *)
     let ts2 = List.map (inst ty_su) ts2 in
     (* bs is the list of types obtained by applying ty_su on tvs2 *)
     let bs = List.map (type_subst ty_su) tvs2 in
     out oc "(@lem%d%a%a%a)" i2 (list_prefix " " typ) bs
       (list_prefix " " term) vs2 (list_prefix " " (hyp_var ts1)) ts2
;;

(* [proof tvs rmap oc p] prints on [oc] the proof [p] for a theorem
   with type variables [tvs] and free variables renaming map [rmap]. *)
let proof tvs rmap =
  let term = term rmap in
  let proof oc p =
    let Proof(thm,content) = p in
    let ts = hyp thm in
    let sub = subproof tvs rmap [] [] ts in
    let sub_at oc k = sub k oc (proof_at k) in
    match content with
    | Prefl(t) -> out oc "REFL %a" term t
    | Psym k -> out oc "SYM %a" sub_at k
    | Ptrans(k1,k2) -> out oc "TRANS %a %a" sub_at k1 sub_at k2
    | Pmkcomb(k1,k2) -> out oc "MK_COMB %a %a" sub_at k1 sub_at k2
    | Pabs(k,t) ->
       let rmap' = add_var rmap t in
       out oc "fun_ext (λ %a, %a)" (decl_var rmap') t
         (subproof tvs rmap' [] [] ts k) (proof_at k)
    | Pbeta(t) -> out oc "REFL %a" term t
    | Passume(t) -> hyp_var (hyp thm) oc t
    | Peqmp(k1,k2) -> out oc "EQ_MP %a %a" sub_at k1 sub_at k2
    | Pdeduct(k1,k2) ->
       let p1 = proof_at k1 and p2 = proof_at k2 in
       let Proof(th1,_) = p1 and Proof(th2,_) = p2 in
       let t1 = concl th1 and t2 = concl th2 in
       let n = 1 + List.length ts in
       out oc "prop_ext (λ h%d : Prf %a, %a) (λ h%d : Prf %a, %a)"
         n term t1 (subproof tvs rmap [] [] (ts @ [t1]) k2) p2
         n term t2 (subproof tvs rmap [] [] (ts @ [t2]) k1) p1
    | Pinst(k,s) -> out oc "%a" (subproof tvs rmap [] s ts k) (proof_at k)
    | Pinstt(k,s) -> out oc "%a" (subproof tvs rmap s [] ts k) (proof_at k)
    | Paxiom(t) ->
       out oc "axiom_%d%a"
         (pos_first (fun th -> concl th = t) (axioms()))
         (list_prefix " " term) (frees t)
    | Pdef(_,n,_) -> out oc "%a_def" cst_name n
    | Pdeft(_,t,_,_) ->
       out oc "@axiom_%d%a%a"
         (pos_first (fun th -> concl th = t) (axioms()))
         (list_prefix " " typ) (type_vars_in_term t)
         (list_prefix " " term) (frees t)
    | Ptruth -> out oc "Tᵢ"
    | Pconj(k1,k2) -> out oc "∧ᵢ %a %a" sub_at k1 sub_at k2
    | Pconjunct1 k -> out oc "∧ₑ₁ %a" sub_at k
    | Pconjunct2 k -> out oc "∧ₑ₂ %a" sub_at k
    | Pmp(k1,k2) -> out oc "%a %a" sub_at k1 sub_at k2
    | Pdisch(t,k) ->
       out oc "λ %a : Prf %a, %a" (hyp_var ts) t term t sub_at k
    | Pspec(t,k) -> out oc "%a %a" sub_at k term t
    | Pgen(x,k) ->
       let rmap' = add_var rmap x in
       out oc "λ %a, %a"
         (decl_var rmap') x (subproof tvs rmap' [] [] ts k) (proof_at k)
    | Pexists(p,t,k) -> out oc "∃ᵢ %a %a %a" term p term t sub_at k
    | Pdisj1(p,k) -> out oc "∨ᵢ₁ %a %a" sub_at k term p
    | Pdisj2(p,k) -> out oc "∨ᵢ₂ %a %a" term p sub_at k
    | Pdisj_cases(k1,k2,k3) ->
       let p1 = proof_at k1 in
       let Proof(th1,_) = p1 in
       let l,r = binop_args (concl th1) in
       out oc "∨ₑ %a (λ h0 : Prf %a, %a) (λ h0 : Prf %a, %a)"
         (sub k1) p1 term l sub_at k2 term r sub_at k3
    | Pchoose(v,k1,k2) ->
       let p1 = proof_at k1 in
       let Proof(th1,_) = p1 in
       begin match concl th1 with
       | Comb(_,p) ->
          let rmap' = add_var rmap v in
          out oc "∃ₑ %a (λ %a, λ h0 : Prf(%a %a), %a)"
            (sub k1) p1 (decl_var rmap') v term p (var rmap') v
            (subproof tvs rmap' [] [] ts k2) (proof_at k2)
       | _ -> assert false
       end
  in proof
;;

(****************************************************************************)
(* Translation of type declarations and axioms. *)
(****************************************************************************)

let typ_arity oc k = for _ = 1 to k do out oc "Set → " done; out oc "Set";;

let decl_typ oc (n,k) =
  out oc "constant symbol %a : %a;\n" typ_name n typ_arity k;;

let typ_vars oc ts =
  match ts with
  | [] -> ()
  | ts -> out oc " [%a]" (list_sep " " typ) ts
;;

let typ_params = list_prefix " " raw_typ;;

let definition_of n =
  let f th =
    let t = concl th in
    match t with
    | Comb(Comb(Const("=",_),Const(n',_)),r) ->
       if n'=n then Some(t,r) else None
    | _ -> assert false
  in List.find_map f (definitions())
;;

let decl_sym oc (n,b) =
  match definition_of n with
  | None ->
     out oc "symbol %a%a : El %a;\n" cst_name n typ_vars (tyvars b) raw_typ b
  | Some (t,r) ->
     let tvst = type_vars_in_term t in
     let rmap = renaming_map tvst [] in
     match n with
     |"@"|"\\/"|"/\\"|"==>"|"!"|"?"|"?!"|"~"|"F"|"T" ->
       out oc "symbol %a_def%a : Prf %a;\n"
         cst_name n typ_vars tvst (unabbrev_term rmap) t
     | _ ->
        let tvsb = tyvars b in
        out oc "symbol %a%a : El %a ≔ %a;\n"
          cst_name n typ_vars tvsb raw_typ b (unabbrev_term rmap) r;
        if tvsb = [] then
          out oc "opaque symbol %a_def%a : Prf %a ≔ REFL %a;\n"
            cst_name n typ_vars tvst (unabbrev_term rmap) t cst_name n
        else
          out oc "opaque symbol %a_def%a : Prf %a ≔ REFL (@%a %a);\n"
            cst_name n typ_vars tvst (unabbrev_term rmap) t
            cst_name n typ_params tvsb
;;

let decl_axioms oc ths =
  let axiom i th =
    let t = concl th in (* axioms have no assumptions *)
    let tvs = type_vars_in_term t in
    let xs = frees t in
    let rmap = renaming_map tvs xs in
    out oc "symbol axiom_%d%a%a : Prf %a;\n"
      i typ_vars (type_vars_in_term t) (list (unabbrev_decl_param rmap)) xs
      (unabbrev_term rmap) t
  in
  List.iteri axiom ths
;;

(****************************************************************************)
(* Translation of theorems and proofs. *)
(****************************************************************************)

type decl =
  | Unnamed_thm
  | Axiom
  | Named_thm of string
  | Named_axm of string
;;

(* [!proof_part_max_idx] indicates the maximal index of the current part. *)
let proof_part_max_idx = ref (-1);;

(* [decl_theorem oc k p d] outputs on [oc] the theorem of index [k]
   and proof [p] as declaration type [d]. *)
let decl_theorem oc k p d =
  let Proof(thm,_) = p in
  (*log "theorem %d ...\n%!" k;*)
  let ts,t = dest_thm thm in
  let xs = freesl (t::ts) in
  let tvs = type_vars_in_thm thm in
  let rmap = renaming_map tvs xs in
  match d with
  | Unnamed_thm ->
     let term = term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     let prv = let l = get_use k in l > 0 && l <= !proof_part_max_idx in
     out oc "%s symbol lem%d%a%a%a : Prf %a ≔ %a;\n"
       (if prv then "private" else "opaque") k
       typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
       (proof tvs rmap) p
  | Axiom ->
     let term = unabbrev_term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     out oc "symbol lem%d%a%a%a : Prf %a;\n" k
       typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
  | Named_thm n ->
     let term = unabbrev_term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     let hyps oc ts = List.iteri (fun i _ -> out oc " h%d" (i+1)) ts in
     out oc "opaque symbol lem%s%a%a%a : Prf %a ≔ lem%d%a%a;\n" n
       typ_vars tvs (list (unabbrev_decl_param rmap)) xs decl_hyps ts term t
       k (list_prefix " " (var rmap)) xs hyps ts
  | Named_axm n ->
     let term = unabbrev_term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     out oc "symbol lem%s%a%a%a : Prf %a;\n" n
       typ_vars tvs (list (unabbrev_decl_param rmap)) xs decl_hyps ts term t
;;

(* [theorem oc k p] outputs on [oc] the proof [p] of index [k]. *)
let theorem oc k p = decl_theorem oc k p Unnamed_thm;;

(* [theorem_as_axiom oc k p] outputs on [oc] the proof [p] of index
   [k] as an axiom. *)
let theorem_as_axiom oc k p = decl_theorem oc k p Axiom;;

(* [proofs_in_interval oc x y] outputs on [oc] the proofs in interval
   [x] .. [y]. *)
let proofs_in_interval oc x y =
  for k = x to y do
    if get_use k >= 0 then
      begin (*log "proof %d ...\n%!" k;*) theorem oc k (proof_at k) end
  done
;;

(* [proofs_in_range oc r] outputs on [oc] the proofs in range [r]. *)
let proofs_in_range oc = function
  | Only x ->
     let p = proof_at x in
     List.iter (fun k -> theorem_as_axiom oc k (proof_at k)) (deps p);
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
(* Generate term abbreviation files. *)
(****************************************************************************)

let export_term_abbrevs_in_one_file b n =
  let deps = [b^"_types"; n^"_type_abbrevs"; b^"_terms"] in
  export (n^"_term_abbrevs")
    (deps @ if !use_sharing then [n^"_subterm_abbrevs"] else [])
    decl_term_abbrevs;
  if !use_sharing then
    export (n^"_subterm_abbrevs") deps decl_subterm_abbrevs
;;

(* [export_theorem_term_abbrevs b n] writes the term abbreviations in
   the files [n^"_term_abbrevs"^part(k)^".lp"]. *)
let export_theorem_term_abbrevs b n =
  let l = TrmHashtbl.fold (fun t x acc -> (t,x)::acc) htbl_term_abbrev [] in
  let cmp (_,(k1,_,_)) (_,(k2,_,_)) = Stdlib.compare k1 k2 in
  let l = ref (List.sort cmp l) in
  let iter_deps f =
    f (b^"_types");
    f (n^"_type_abbrevs");
    f (b^"_terms");
    if !use_sharing then f (n^"_subterm_abbrevs")
  in
  let part_abbrev (i,min) =
    let abbrevs oc =
      let max = Hashtbl.find htbl_abbrev_part_max i in
      for _ = min to max do
        match !l with
        | [] -> assert false
        | (t,x)::l' -> abbrev oc t x; l := l'
      done
    in
    export_iter (n^"_term_abbrevs"^part i) iter_deps abbrevs
  in
  List.iter part_abbrev
    (List.sort Stdlib.compare (Xlib.bindings htbl_abbrev_part_min));
  if !use_sharing then
    export (n^"_subterm_abbrevs") [b^"_types"; n^"_type_abbrevs"; b^"_terms"]
      decl_subterm_abbrevs
;;

(****************************************************************************)
(* Generate proof files. *)
(****************************************************************************)

(* Maximum number of proof steps in a proof file. *)
let max_steps = ref max_int;;

(* Current proof part. *)
let proof_part = ref 0;;

(* Dependencies on term abbreviations parts of each proof part. *)
let htbl_proof_abdeps = Hashtbl.create 1_000;;

(* [export_proofs_in_interval n x y] generates the proof steps of
   index between [x] and [y] in the files [n^part(k)^"_proofs.lp"]. *)
let export_proofs_in_interval n x y =
  let nb_steps = ref 0 in
  let cur_oc = ref stdout in
  let start_part k =
    incr proof_part;
    let f = n ^ part !proof_part ^ "_proofs.lp" in
    log "generate %s ...\n%!" f;
    cur_oc := open_out f;
    nb_steps := 0;
    proof_abdeps := SetInt.empty;
    (* compute proof_part_max_idx *)
    let i = ref k and c = ref 0 in
    while (!i <= y && !c < !max_steps) do
      if get_use !i >= 0 then incr c;
      incr i
    done;
    proof_part_max_idx := !i - 2
  in
  Hashtbl.add htbl_abbrev_part_min 1 0;
  proof_part := 0;
  start_part x;
  for k = x to y do
    if get_use k >= 0 then
      begin
        incr nb_steps;
        if !nb_steps > !max_steps then
          begin
            close_out !cur_oc;
            Hashtbl.add htbl_proof_abdeps !proof_part !proof_abdeps;
            start_part k
          end;
        (*log "proof %d ...\n%!" k;*)
        theorem !cur_oc k (proof_at k)
      end
  done;
  close_out !cur_oc;
  Hashtbl.add htbl_abbrev_part_max !abbrev_part !cur_abbrev;
  Hashtbl.add htbl_proof_abdeps !proof_part !proof_abdeps
;;

(* [export_theorem_proof n] generates the files
   [n^part(k)^"_proofs.lp"] for some [1<=k<!proof_part] and the file
   [n^"_proofs.lp"]. *)
let export_theorem_proof n =
  export_proofs_in_interval n !the_start_idx
    (!the_start_idx + Array.length !prf_pos - 1);
  log "rename %s_part_%d_proofs.lp into %s.lp ...\n%!" n !proof_part n;
  command
    (Printf.sprintf "mv -f %s_part_%d_proofs.lp %s_proofs.lp" n !proof_part n)
;;

(* [export_theorem_deps n] generates for [1<=i<=!proof_part] the files
   [n^part(i)^"_deps.lp"] and [n^part(i)^".lp"] assuming that the files
   [n^part(i)^"_proofs.lp"] are already generated. *)
let export_theorem_deps b n =
  for i = 1 to !proof_part do
    let p = if i < !proof_part then n^part i else n in
    let oc_lp = open_file (p^"_deps.lp")
    and oc_lpo_mk = open_file (p^".lpo.mk") in
    out oc_lpo_mk "%s.lpo:" p;
    let f dep =
      require oc_lp dep;
      out oc_lpo_mk " %s.lpo" dep;
    in
    f "theory_hol";
    f (b^"_types");
    f (b^"_terms");
    f (b^"_axioms");
    f (n^"_type_abbrevs");
    if !use_sharing then f (n^"_subterm_abbrevs");
    SetInt.iter (fun j -> f (n^"_term_abbrevs"^part j))
      (Hashtbl.find htbl_proof_abdeps i);
    SetStr.iter f !thdeps;
    for j = 1 to i-1 do f (n^part j) done; (*TO BE OPTIMIZED*)
    close_out oc_lp;
    out oc_lpo_mk "\n";
    close_out oc_lpo_mk;
    concat (p^"_deps.lp") (p^"_proofs.lp") (p^".lp");
  done
;;

(****************************************************************************)
(* Lambdapi file generation with type and term abbreviations. *)
(****************************************************************************)

let types() =
  let f (n,_) = match n with "bool" | "fun" -> false | _ -> true in
  List.filter f (types())
;;

let export_types b =
  export (b^"_types") [] (fun oc -> list decl_typ oc (types()))
;;

let export_type_abbrevs b n =
  export (n^"_type_abbrevs") [b^"_types"] decl_type_abbrevs
;;

let constants() =
  let f (n,_) = match n with "=" | "el" -> false | _ -> true in
  List.filter f (constants())
;;

let export_terms b =
  export (b^"_terms") [b^"_types"] (fun oc -> list decl_sym oc (constants()))
;;

let export_axioms b =
  export (b^"_axioms") [b^"_types"; b^"_terms"]
    (fun oc -> decl_axioms oc (axioms()))
;;

let iter_proofs_deps b f =
  f (b^"_types");
  f (b^"_type_abbrevs");
  f (b^"_terms");
  f (b^"_axioms");
  if !use_sharing then f (b^"_subterm_abbrevs");
  f (b^"_term_abbrevs");
  for k = 2 to !abbrev_part do f (b^"_term_abbrevs"^part k) done
;;

let export_proofs b r =
  export_iter (b^"_proofs") (iter_proofs_deps b)
    (fun oc -> proofs_in_range oc r)
;;

let out_map_thid_name as_axiom oc map_thid_name =
  MapInt.iter
    (fun k n -> decl_theorem oc k (proof_at k)
                  (if as_axiom then Named_axm n else Named_thm n))
    map_thid_name
;;

let iter_theorems_deps b f =
  f (b^"_types");
  f (b^"_type_abbrevs");
  f (b^"_terms");
  f (b^"_axioms");
  f (b^"_proofs")
;;

let export_theorems b map_thid_name =
  export_iter b (iter_theorems_deps b)
    (fun oc -> out_map_thid_name false oc map_thid_name)
;;

let export_theorems_as_axioms b map_thid_name =
  export (b^"_opam") [b^"_types";b^"_terms";b^"_axioms"]
    (fun oc -> out_map_thid_name true oc map_thid_name)
;;

let iter_proofs_part_deps b k dg f =
  f (b^"_types");
  f (b^part k^"_type_abbrevs");
  f (b^"_terms");
  f (b^part k^"_term_abbrevs");
  f (b^"_axioms");
  for i = 1 to k-1 do if dg.(k-1).(i-1) > 0 then f (b^part i) done
;;

let export_proofs_part b dg k x y =
  proof_part_max_idx := y;
  export_iter (b^part k) (iter_proofs_part_deps b k dg)
    (fun oc -> proofs_in_interval oc x y)
;;

let iter_theorems_part_deps b k f =
  f (b^"_types");
  f (b^"_terms");
  f (b^"_axioms");
  for i = 1 to k do f (b^part i) done
;;

let export_theorems_part k b map_thid_name =
  export_iter b (iter_theorems_part_deps b k)
    (fun oc -> out_map_thid_name false oc map_thid_name)
;;
(*
(****************************************************************************)
(* Generate a lp file without abbreviations for each proof step. *)
(****************************************************************************)

(* Warning: checking the generated lp files is currently very
   inefficient because of the way loading is currently done in
   Lambdapi (see https://github.com/Deducteam/lambdapi/issues/959). *)

(* [export_one_file_by_prf b x y] creates a lp file for each proof in
   interval [x..y]. *)
let export_one_file_by_prf b x y =
  use_abbrev := false;
  update_map_const_typ_vars_pos();
  (* Generate p.lp. *)
  let fname = "p.lp" in
  log "generate %s ...\n" fname;
  let oc = open_out fname in
  out oc
"/* file generated by: hol2dk exp %s */\n
require open hol-light.theory_hol;\n
/* type constructors */
%a
/* constants */
%a
/* axioms */
%a\n"
    b (list decl_typ) (types()) (list decl_sym) (constants())
    decl_axioms (axioms());
  close_out oc;
  (* Generate a lp file for each proof. *)
  let theorem_file k p =
    let fname = "p" ^ string_of_int k ^ ".lp" in
    log "generate %s ...\n%!" fname;
    let oc = open_out fname in
    out oc "require open hol-light.theory_hol;\n\
            require open hol-light.p;\n";
    let lp_dep oc d = out oc "require open hol-light.p%d;\n" d in
    List.iter (lp_dep oc) (deps p);
    theorem oc k p;
    close_out oc
  in
  for k = x to y do
    if get_use k >= 0 then theorem_file k (proof_at k)
  done
;;

(* [gen_lp_makefile_one_file_by_prf b nb_proofs nb_parts] creates
   a makefile to generate the lp files for [b.prf]. *)
let gen_lp_makefile_one_file_by_prf b nb_proofs nb_parts =
  let fname = "Makefile.lp" in
  log "generate %s ...\n%!" fname;
  let oc = open_out fname in
  (* Commands for generating lp files. *)
  out oc "# file generated by: hol2dk mk-lp %d %s\n\
          .SUFFIXES:\n\
          .PHONY: lp\n\
          lp:" nb_parts b;
  for k = 1 to nb_parts do out oc " lp%d" k done;
  out oc "\n";
  let f k x y =
    out oc ".PHONY: lp%d\nlp%d:\n\thol2dk prf %d %d %s\n" k k x y b in
  Xlib.iter_parts nb_proofs nb_parts f;
  out oc ".PHONY: clean\n\
          clean:\n\
          \trm -f %s*.lp\n" b;
  close_out oc
;;

(* [gen_makefile_one_file_by_prf b i x y] creates a makefile to
   translate to Coq the lp files generated by [export_one_file_by_prf
   b] for the proofs in the interval [x..y]. *)
let gen_makefile_one_file_by_prf b i x y =
  (* Start generating Makefile. *)
  let fname = "coq" ^ string_of_int i ^ ".mk" in
  log "generate %s ...\n%!" fname;
  let oc_makefile = open_out fname in
  out oc_makefile
    "# file generated by: hol2dk mk-coq %s\n\
     .SUFFIXES:\n\
     include vofiles%d.mk\n\
     %%.vo: %%.v\n\
     \tcoqc -R . HOLLight $<\n\
     %%.v: %%.lp\n\
     \tlambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp \
     --renaming $(HOL2DK_DIR)/renaming.lp --erasing $(HOL2DK_DIR)/erasing.lp \
     --use-notations --requiring coq.v $< \
     | sed -e 's/^Require Import hol-light\\./Require Import /g' > $@\n\
     p.vo: coq.vo theory_hol.vo\n" b i;
  let add_vodep d = out oc_makefile " p%d.vo" d in
  (* Start generating vofiles.mk. *)
  let fname = "vofiles" ^ string_of_int i ^ ".mk" in
  log "generate %s ...\n%!" fname;
  let oc_vofiles = open_out fname in
  out oc_vofiles
    "# file generated by: hol2dk mk-exp %s\n\
     .PHONY: vo\n\
     vo: coq.vo p.vo" b;
  let add_vofile d = out oc_vofiles " p%d.vo" d in
  (* Start generating lpofiles.mk. *)
  (*let fname = "lpofiles" ^ string_of_int i ^ ".mk" in
  log "generate %s ...\n%!" fname;
  let oc_lpofiles = open_out fname in
  out oc_lpofiles
    "# file generated by: hol2dk mk-exp %s\n\
     .PHONY: lpo\n\
     lpo:" b;
  let add_lpofile d = out oc_lpofiles " p%d.lpo" d in*)
  (* Generate a lp file for each proof. *)
  let handle_proof k p =
    out oc_makefile "p%d.vo: p.vo" k;
    let f d = add_vofile d; add_vodep d(*; add_lpofile d*) in
    List.iter f (deps p);
    out oc_makefile "\n"
  in
  for k = x to y do handle_proof k (proof_at k) done;
  close_out oc_makefile;
  close_out oc_vofiles
;;

(* [gen_coq_makefile_one_file_by_prf b nb_proofs nb_parts] creates
   a makefile to translate to Coq the lp files generated by
   [export_one_file_by_prf b]. *)
let gen_coq_makefile_one_file_by_prf b nb_proofs nb_parts =
  Xlib.iter_parts nb_proofs nb_parts (gen_makefile_one_file_by_prf b);
  let fname = "Makefile" in
  log "generate %s ...\n%!" fname;
  let oc = open_out fname in
  out oc "# file generated by: hol2dk mk-coq %d %s\n.SUFFIXES:\n" nb_parts b;
  out oc "include Makefile.lp\n";
  out oc ".PHONY: vo\nvo:\n";
  for k = 1 to nb_parts do out oc "\t$(MAKE) -f coq%d.mk\n" k done;
  out oc ".PHONY: clean\n\
          clean:\n\
          \trm -f *.glob *.vo* .*.aux *.lpo *.dko\n";
  close_out oc
;;
*)
