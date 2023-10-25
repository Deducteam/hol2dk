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
let name oc n =
  string oc
    begin match n with
    | "," -> "̦‚" (* low single comma quotation mark
                    https://unicode-table.com/en/201A/ *)
    | "@" -> "ε" (* Hilbert choice operator *)
    | "\\/" -> "∨"
    | "/\\" -> "∧"
    | "==>" -> "⇒"
    | "!" -> "∀"
    | "?" -> "∃"
    | "?!" -> "∃!"
    | "~" -> "¬"
    (* invalid Lambdapi identifiers *)
    | "$" -> "dollar"
    | ".." -> "dotdot"
    | "" -> assert false
    | _ -> Xlib.replace '%' '_' n (* for Coq *)
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
     | "sum" -> "sum_type" (* sum is also a term constant *)
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
       match MapTyp.find_opt b !map_typ with
       | Some (k,_) -> k
       | None ->
          let k = !idx + 1 in
          idx := k;
          let x = (k, List.length tvs) in
          map_typ := MapTyp.add b x !map_typ;
          k
     in
     match tvs with
     | [] -> out oc "type%d" k
     | _ -> out oc "(type%d%a)" k (list_prefix " " raw_typ) tvs
;;

let typ oc b = if !use_abbrev then abbrev_typ oc b else raw_typ oc b;;

(* [decl_map_typ oc m] outputs on [oc] the type abbreviations of [m]. *)
let decl_map_typ oc m =
  let abbrev (b,(k,n)) =
    out oc "symbol type%d" k;
    for i=0 to n-1 do out oc " a%d" i done;
    (* We can use [raw_typ] here since [b] canonical. *)
    out oc " ≔ %a;\n" raw_typ b
  in
  List.iter abbrev
    (List.sort (fun (_,(k1,_)) (_,(k2,_)) -> k1 - k2)
       (MapTyp.fold (fun b x l -> (b,x)::l) m []))
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

let abbrev_term =
  let idx = ref (-1) in
  let abbrev oc t =
    (* check whether the term is already abbreviated; add a new
       abbreviation if needed *)
    let tvs, vs, bs, t = canonical_term t in
    let k =
      match MapTrm.find_opt t !map_term with
      | Some (k,_,_) -> k
      | None ->
         let k = !idx + 1 in
         idx := k;
         let x = (k, List.length tvs, bs) in
         map_term := MapTrm.add t x !map_term;
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
  | Var(n,b) -> (try mk_var(List.assoc t rmap,b) with Not_found -> mk_el b)
  | Const(_,_) -> t
  | Comb(u,v) -> mk_comb(rename rmap u, rename rmap v)
  | Abs(u,v) ->
     let rmap' = add_var rmap u in mk_abs(rename rmap' u,rename rmap' v)
;;

let term rmap oc t =
  if !use_abbrev then abbrev_term oc (rename rmap t)
  else unabbrev_term rmap oc (rename rmap t)
;;

(* [decl_map_term oc m] outputs on [oc] the term abbreviations defined
   by [m]. *)
let decl_map_term oc m =
  let abbrev (t,(k,n,bs)) =
    out oc "symbol term%d" k;
    for i=0 to n-1 do out oc " a%d" i done;
    (* We can use abbrev_typ here since [bs] are canonical. *)
    List.iteri (fun i b -> out oc " (x%d: El %a)" i abbrev_typ b) bs;
    (* We can use [raw_term] here since [t] is canonical. *)
    out oc " ≔ %a;\n" raw_term t
  in
  List.iter abbrev
    (List.sort (fun (_,(k1,_,_)) (_,(k2,_,_)) -> k1 - k2)
       (MapTrm.fold (fun b x l -> (b,x)::l) m []))
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
     out oc "(@thm_%d%a%a%a)" i2 (list_prefix " " typ) tvs2
       (list_prefix " " term) vs2 (list_prefix " " (hyp_var ts1)) ts2
  | _ ->
     (* vs2 is now the application of ty_su on vs2 *)
     let vs2 = List.map (inst ty_su) vs2 in
     (* ts2 is now the application of ty_su on ts2 *)
     let ts2 = List.map (inst ty_su) ts2 in
     (* bs is the list of types obtained by applying ty_su on tvs2 *)
     let bs = List.map (type_subst ty_su) tvs2 in
     out oc "(@thm_%d%a%a%a)" i2 (list_prefix " " typ) bs
       (list_prefix " " term) vs2 (list_prefix " " (hyp_var ts1)) ts2
;;

(* [proof tvs rmap oc p] prints on [oc] the proof [p] for a theorem
   with type variables [tvs] and free variables renaming map [rmap]. *)
let proof tvs rmap =
  let term = term rmap in
  let rec proof oc p =
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
       out oc "axiom_%d%a"
         (pos_first (fun th -> concl th = t) (axioms()))
         (list_prefix " " term) (frees t)
    | Ptruth -> out oc "top"
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

let typ_arity oc k = for i = 1 to k do out oc "Set → " done; out oc "Set";;

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
(* Translation of theorems. *)
(****************************************************************************)

type decl =
  | Unnamed_thm
  | Axiom
  | Named_thm of string
;;

(* [decl_theorem oc k p d] outputs on [oc] the theorem of index [k]
   and proof [p] as declaration type [d]. *)
let decl_theorem oc k p d =
  let Proof(thm,content) = p in
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
     let prv =
       Array.length !Xproof.thm_uses > 0 &&
       let l = Array.get !Xproof.thm_uses k in
       l = -1 || (l > 0 && l < !cur_part_max)
     in
     out oc "%s symbol thm_%d%a%a%a : Prf %a ≔ %a;\n"
       (if prv then "private" else "opaque") k
       typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
       (proof tvs rmap) p
  | Axiom ->
     let term = unabbrev_term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     out oc "symbol thm_%d%a%a%a : Prf %a;\n" k
       typ_vars tvs (list (decl_param rmap)) xs decl_hyps ts term t
  | Named_thm n ->
     let term = unabbrev_term rmap in
     let decl_hyps oc ts =
       List.iteri (fun i t -> out oc " (h%d : Prf %a)" (i+1) term t) ts in
     let hyps oc ts = List.iteri (fun i _ -> out oc " h%d" (i+1)) ts in
     out oc "opaque symbol thm_%s%a%a%a : Prf %a ≔ thm_%d%a%a;\n" n
       typ_vars tvs (list (unabbrev_decl_param rmap)) xs decl_hyps ts term t
       k (list_prefix " " (var rmap)) xs hyps ts
;;

(* [theorem oc k p] outputs on [oc] the proof [p] of index [k]. *)
let theorem oc k p = decl_theorem oc k p Unnamed_thm;;

(* [theorem_as_axiom oc k p] outputs on [oc] the proof [p] of index
   [k] as an axiom. *)
let theorem_as_axiom oc k p = decl_theorem oc k p Axiom;;

(* [proofs_in_range oc r] outputs on [oc] the proofs in range [r]. *)
let proofs_in_range oc = function
  | Only x ->
     let p = proof_at x in
     List.iter (fun k -> theorem_as_axiom oc k (proof_at k)) (deps p);
     theorem oc x p(*;
     out oc
"flag \"print_implicits\" on;
flag \"print_domains\" on;
print thm_%d;\n" x*)
  | Upto y -> for k = 0 to y do theorem oc k (proof_at k) done
  | All -> iter_proofs_at (theorem oc)
  | Inter(x,y) -> for k = x to y do theorem oc k (proof_at k) done
;;

(****************************************************************************)
(* Lambdapi file generation with type and term abbreviations. *)
(****************************************************************************)

let require oc basename s =
  out oc "require open hol-light.%s%s;\n" basename s;;

let export basename suffix f =
  let filename = basename ^ suffix ^ ".lp" in
  log "generate %s ...\n%!" filename;
  let oc = open_out filename in
  out oc "require open hol-light.theory_hol;\n";
  f oc;
  close_out oc
;;

let types() =
  let f (n,_) = match n with "bool" | "fun" -> false | _ -> true in
  List.filter f (types())
;;

let export_types b =
  export b "_types" (fun oc -> list decl_typ oc (types()))
;;

let export_type_abbrevs b s =
  export b (s ^ "_type_abbrevs")
    (fun oc -> require oc b "_types"; decl_map_typ oc !map_typ)
;;

let constants() =
  let f (n,_) = match n with "=" | "el" -> false | _ -> true in
  List.filter f (constants())
;;

let export_terms b =
  export b "_terms"
    (fun oc -> require oc b "_types"; list decl_sym oc (constants()))
;;

let export_term_abbrevs b s =
  export b (s ^ "_term_abbrevs")
    (fun oc ->
      List.iter (require oc b) ["_types"; s ^ "_type_abbrevs"; "_terms"];
      decl_map_term oc !map_term)
;;

let export_axioms b =
  export b "_axioms"
    (fun oc ->
      List.iter (require oc b) ["_types"; "_terms"];
      decl_axioms oc (axioms()))
;;

let export_proofs b r =
  export b "_proofs"
    (fun oc ->
      List.iter (require oc b)
        ["_types"; "_type_abbrevs"; "_terms"; "_term_abbrevs"; "_axioms"];
      proofs_in_range oc r)
;;

let out_map_thid_name oc map_thid_name =
  MapInt.iter
    (fun k n -> decl_theorem oc k (proof_at k) (Named_thm n))
    map_thid_name
  (*List.iter
    (fun (k,n) -> decl_theorem oc k (proof_at k) (Named_thm n))
    (List.sort Stdlib.compare
       (MapInt.fold (fun i n l -> (i,n)::l) map_thid_name []))*)
;;

let export_theorems b map_thid_name =
  export b ""
    (fun oc ->
      List.iter (require oc b)
        ["_types";"_type_abbrevs";"_terms";"_term_abbrevs";"_axioms";"_proofs"];
      out_map_thid_name oc map_thid_name)
;;

let export_proofs_part =
  let part i s = "_part_" ^ string_of_int i ^ s in
  fun b dg k x y ->
  export b ("_part_" ^ string_of_int k)
    (fun oc ->
      List.iter (require oc b)
        ["_types"; part k "_type_abbrevs"; "_terms"; part k "_term_abbrevs";
         "_axioms"];
      for i = 1 to k-1 do
        if dg.(k-1).(i-1) > 0 then require oc b ("_part_" ^ string_of_int i)
      done;
      proofs_in_range oc (Inter(x,y)))
;;

let export_theorems_part k b map_thid_name =
  export b ""
    (fun oc ->
      List.iter (require oc b) ["_types";"_terms";"_axioms"];
      for i = 1 to k do require oc b ("_part_" ^ string_of_int i) done;
      out_map_thid_name oc map_thid_name)
;;

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
  for k = x to y do theorem_file k (proof_at k) done
;;

(* [gen_lp_makefile_one_file_by_prf basename nb_proofs nb_parts] creates
   a makefile to generate the lp files for [basename.prf]. *)
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

(* [gen_coq_makefile_one_file_by_prf basename nb_proofs nb_parts] creates
   a makefile to translate to Coq the lp files generated by
   [export_one_file_by_prf basename]. *)
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
