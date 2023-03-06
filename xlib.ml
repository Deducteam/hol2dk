(****************************************************************************)
(* Useful functions on types, terms and other data structures. *)
(****************************************************************************)

(*REMOVE
unset_jrh_lexer;;
REMOVE*)

open Xprelude
open Fusion

let the_proofs : proof array ref = ref [||]
let proof_at k = Array.get (!the_proofs) k
let the_proofs_idx : int ref = ref (-1)
let nb_proofs() = !the_proofs_idx + 1
let iter_proofs f = for k = 0 to !the_proofs_idx do f k (proof_at k) done

(****************************************************************************)
(* Ranges of proof indexes. *)
(****************************************************************************)

type range = Only of int | Upto of int | All | Inter of int * int;;

let in_range = function
  | Only x -> fun k -> k = x
  | Upto x -> fun k -> k <= x
  | All -> fun _ -> true
  | Inter(x,y) -> fun k -> x <= k && k <= y
;;

(****************************************************************************)
(* Functions on basic data structures. *)
(****************************************************************************)

(* [pos_first f l] returns the position (counting from 0) of the first
   element of [l] satisfying [f]. Raises Not_found if there is no such
   element. *)
let pos_first f =
  let rec aux k l =
    match l with
    | [] -> raise Not_found
    | y::l -> if f y then k else aux (k+1) l
  in aux 0
;;

(****************************************************************************)
(* Printing functions. *)
(****************************************************************************)

let int oc k = out oc "%d" k;;

let string oc s = out oc "%s" s;;

let pair f g oc (x, y) = out oc "%a, %a" f x g y;;

let opair f g oc (x, y) = out oc "(%a, %a)" f x g y;;

let prefix p elt oc x = out oc "%s%a" p elt x;;

let list_sep sep elt oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs
;;

let list elt oc xs = list_sep "" elt oc xs;;

let olist elt oc xs = out oc "[%a]" (list_sep "; " elt) xs;;

let list_prefix p elt oc xs = list (prefix p elt) oc xs;;

let hstats oc ht =
  let open Hashtbl in let s = stats ht in
  out oc "{ num_bindings = %d; num_buckets = %d; max_bucket_length = %d }\n"
    s.num_bindings s.num_buckets s.max_bucket_length
;;

(****************************************************************************)
(* Functions on types. *)
(****************************************************************************)

(* Printing function for debug. *)
let rec otyp oc b =
  match b with
  | Tyvar n -> out oc "(Tyvar %s)" n
  | Tyapp(n,bs) -> out oc "Tyapp(%s,%a)" n (olist otyp) bs
;;

(* Sets and maps on types. *)
module OrdTyp = struct type t = hol_type let compare = compare end;;
module SetTyp = Set.Make(OrdTyp);;
module MapTyp = Map.Make(OrdTyp);;

(* It is important for the export that list of type variables and term
   free variables are always ordered and have no duplicate. *)

(* [tyvarsl bs] returns the ordered list with no duplicate of type
   variables occurring in the list of types [bs]. *)
let tyvarsl bs =
  List.sort_uniq compare
    (List.fold_left (fun l b -> tyvars b @ l) [] bs)
;;

(* Redefinition of [tyvars] so that the output is sorted and has no
   duplicate. *)
let tyvars b = List.sort_uniq compare (tyvars b);;

(* [missing_as_bool tvs b] replaces in [b] every type variable not in
   [tvs]. *)
let missing_as_bool tvs =
  let rec typ b =
    match b with
    | Tyvar _ -> if List.mem b tvs then b else bool_ty
    | Tyapp(n,bs) -> mk_type(n, List.map typ bs)
  in typ
;;

(* [canonical_typ b] returns the type variables of [b] together with a
   type alpha-equivalent to any type alpha-equivalent to [b]. *)
let canonical_typ =
  let type_var i tv = mk_vartype ("a" ^ string_of_int i), tv in
  fun b ->
  let tvs = tyvars b in
  tvs, type_subst (List.mapi type_var tvs) b
;;

(* Subterm positions in types are represented as list of natural numbers. *)

(* [subtyp b p] returns the type at position [p] in the type [b]. *)
let rec subtyp b p =
  match b, p with
  | _, [] -> b
  | Tyapp(_, bs), p::ps -> subtyp (List.nth bs p) ps
  | _ -> invalid_arg "subtyp"
;;

(* [typ_vars_pos b] returns an association list mapping every type
   variable occurrence to its posiion in [b]. *)
let typ_vars_pos b =
  let rec aux acc l =
    match l with
    | [] -> acc
    | (Tyvar n, p)::l -> aux ((n, List.rev p)::acc) l
    | (Tyapp(n,bs), p)::l ->
       aux acc
         (let k = ref (-1) in
          List.fold_left
            (fun l b -> incr k; (b,!k::p)::l)
            l bs)
  in aux [] [b,[]]
;;

(* test:
typ_vars_pos
  (mk_type("fun",[mk_vartype"a"
                 ;mk_type("fun",[mk_vartype"a";mk_vartype"b"])]));;*)

(* [get_domain ty] returns the domain of [ty], assuming that [ty] is
   of the form [Tyapp("fun",_)]. *)
let get_domain ty =
  match ty with
  | Tyapp("fun",[b;_]) -> b
  | _ -> invalid_arg "get_domain"
;;

(* [arity b] returns the number of arguments a term of type [b] can take. *)
let arity =
  let rec arity acc b =
    match b with
    | Tyapp("fun",[_;b]) -> arity (1+acc) b
    | _ -> acc
  in arity 0
;;

(****************************************************************************)
(* Functions on terms. *)
(****************************************************************************)

(* Printing function for debug. *)
let rec oterm oc t =
  match t with
  | Var(n,b) -> out oc "Var(%s,%a)" n otyp b
  | Const(n,b) -> out oc "Const(%s,%a)" n otyp b
  | Comb(u,v) -> out oc "Comb(%a,%a)" oterm u oterm v
  | Abs(u,v) -> out oc "Abs(%a,%a)" oterm u oterm v
;;

(* Sets and maps on terms. *)
module OrdTrm = struct type t = term let compare = compare end;;
module MapTrm = Map.Make(OrdTrm);;
module SetTrm = Set.Make(OrdTrm);;

let ormap oc m = MapTrm.iter (fun t n -> out oc "(%a,%s)" oterm t n) m;;

(* [head_args t] returns the pair [h,ts] such that [t] is of the t is
   the Comb application of [h] to [ts]. *)
let head_args =
  let rec aux acc t =
    match t with
    | Comb(t1,t2) -> aux (t2::acc) t1
    | _ -> t, acc
  in aux []
;;

(* [binop_args t] returns the terms [u,v] assuming that [t] is of the
   form [Comb(Comb(_,u),v)]. *)
let binop_args t =
  match t with
  | Comb(Comb(_,u),v) -> u,v
  | _ -> assert false
;;

(* [index t ts] returns the position (counting from 0) of the first
   element of [ts] alpha-equivalent to [t]. Raises Not_found if there
   is no such term. *)
let index t =
  try pos_first (fun u -> alphaorder t u = 0)
  with Not_found -> assert false;;

(* [vsubstl s ts] applies the substitution [s] to each term of [ts]. *)
let vsubstl s ts = if s = [] then ts else List.map (vsubst s) ts;;

(* [type_vars_in_terms ts] returns the ordered list with no duplicate
   of type variables occurring in the list of terms [ts]. *)
let type_vars_in_terms ts =
  List.sort_uniq compare
    (List.fold_left (fun l t -> type_vars_in_term t @ l) [] ts)
;;

(* Redefinition of [type_vars_in_term] so that the output is sorted
   and has no duplicat. *)
let type_vars_in_term t = List.sort_uniq compare (type_vars_in_term t)

(* [type_vars_in_terms th] returns the ordered list with no duplicate
   of type variables occurring in the theorem [th]. *)
let type_vars_in_thm thm =
  let ts,t = dest_thm thm in type_vars_in_terms (t::ts);;

(* [vars_terms ts] returns the ordered list with no duplicate of all
   the term variables (including bound variables) occurring in the
   terms [ts] *)
let vars_terms =
  let rec vars_term t =
    match t with
    | Const _ -> []
    | Var _ -> [t]
    | Abs(t,u) -> t :: vars_term u
    | Comb(t,u) -> vars_term t @ vars_term u
  in
  fun ts ->
  List.sort_uniq compare
    (List.fold_left (fun vs t -> vs @ vars_term t) [] ts);;

(* [rename_var rmap v] returns a variable with the same type as the one
   of [v] but with a name not occuring in the codomain of [rmap]. *)
let rename_var rmap =
  let rec rename v =
    match v with
    | Var(n,b) ->
       if List.exists (fun (_,s) -> s = n) rmap then rename (mk_var(n^"'",b))
       else v
    | _ -> assert false
  in rename
;;

(* [add_var rmap v] returns a map extending [rmap] with a mapping from
   [v] to a name not occurring in the codomain of [rmap]. *)
let add_var rmap v =
  match rename_var rmap v with
  | Var(n,_) -> (v,n)::rmap
  | _ -> assert false
;;

(* [renaming_map vs] returns an association list giving new distinct names
   to all the variables occurring in the list of variables [vs]. *)
let renaming_map = List.fold_left add_var [];;

(* Add a new HOL-Light constant "el" that could be defined as:
let el b =
  mk_comb(mk_const("@",[b,aty]),mk_abs(mk_var("_",b),mk_const("T",[])))
*)
(*if not(!el_added) then (new_constant("el",aty); el_added := true);;*)

let mk_el b = mk_const("el",[b,aty]);;

(* [canonical_term t] returns the type variables and term variables of
   [t] together with a term alpha-equivalent to any term
   alpha-equivalent to [t]. *)
let canonical_term =
  let type_var i tv = mk_vartype ("a" ^ string_of_int i), tv in
  let term_var i v =
    match v with
    | Var(_,b) -> v, mk_var ("x" ^ string_of_int i, b)
    | _ -> assert false
  in
  (* [subst i su t] applies [su] on [t] and rename abstracted
     variables as well by using [i]. *)
  let rec subst i su t =
    (*log "subst %d %a %a\n%!" i (olist (opair oterm oterm)) su oterm t;*)
    match t with
    | Var _ -> (try List.assoc t su with Not_found -> assert false)
    | Const _ -> t
    | Comb(u,v) -> mk_comb(subst i su u, subst i su v)
    | Abs(u,v) ->
       match u with
       | Var(_,b) ->
          let u' = mk_var ("y" ^ string_of_int i, b) in
          mk_abs(u', subst (i+1) ((u,u')::su) v)
       | _ -> assert false
  in
  fun t ->
  let tvs = type_vars_in_term t and vs = frees t in
  let su = List.mapi type_var tvs in
  let t' = inst su t in
  let vs' = List.map (inst su) vs in
  let get_type = function Var(_,b) -> b | _ -> assert false in
  let bs = List.map get_type vs' in
  let su' = List.mapi term_var vs' in
  tvs, vs, bs, subst 0 su' t'
;;

(****************************************************************************)
(* Functions on proofs. *)
(****************************************************************************)

(* [get_eq_typ p] returns the type [b] of the terms t and u of the
   conclusion of the proof [p] assumed of the form [= t u]. *)
let get_eq_typ p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb(Const((*"="*)_,b),_),_) -> get_domain b
  | _ -> assert false
;;

(* [get_eq_args p] returns the terms t and u of the conclusion of the
   proof [p] assumed of the form [= t u]. *)
let get_eq_args p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb((*Const("=",_)*)_,t),u) -> t,u
  | _ -> assert false
;;

(* [get_eq_typ_args p] returns the type of the terms t and u, and the
   terms t and u, of the conclusion of the proof [p] assumed of the
   form [= t u]. *)
let get_eq_typ_args p =
  let Proof(th,_) = p in
  match concl th with
  | Comb(Comb(Const((*"="*)_,b),t),u) -> get_domain b,t,u
  | _ -> assert false
;;

(* [deps p] returns the list of proof indexes the proof [p] depends on. *)
let deps (Proof(_,content)) =
  match content with
  | Pdisj_cases(k1,k2,k3) -> [k1;k2;k3]
  | Ptrans(k1,k2) | Pmkcomb(k1,k2) | Peqmp(k1,k2) | Pdeduct(k1,k2)
  | Pconj(k1,k2) | Pmp(k1,k2)
    -> [k1;k2]
  | Pabs(k,_) | Pinst(k,_) | Pinstt(k,_)| Pdeft(k,_,_,_)
  | Pconjunct1 k | Pconjunct2 k | Pdisch(_,k) | Pspec(_,k) | Pgen(_,k)
  | Pexists(_,_,k) | Pdisj1(_,k) | Pdisj2(_,k)
    -> [k]
  | Prefl _ | Pbeta _ | Passume _ | Paxiom _ | Pdef _ | Ptruth
    -> []
;;

(* Print some statistics on how many times a proof is used. *)
let print_proof_stats() =
  (* Array for mapping each proof index to the number of times it is used. *)
  let proof_uses = Array.make (nb_proofs()) 0 in
  (* Maximum number of times a proof is used. *)
  let max = ref 0 in
  (* Actually compute [proof_uses]. *)
  let use k =
    let n = Array.get proof_uses k + 1 in
    Array.set proof_uses k n;
    if n > !max then max := n
  in
  iter_proofs (fun _ p -> List.iter use (deps p));
  (* Array for mapping to each number n <= !max the number of proofs which
     is used n times. *)
  let hist = Array.make (!max + 1) 0 in
  let f nb_uses = Array.set hist nb_uses (Array.get hist nb_uses + 1) in
  Array.iter f proof_uses;
  (* Print histogram *)
  log "i: n means that n proofs are used i times\n";
  let nonzeros = ref 0 in
  for i=0 to !max do
    let n = Array.get hist i in
    if n>0 then (incr nonzeros; log "%d: %d\n" i n)
  done;
  log "number of mappings: %d\n" !nonzeros;
  (* Count the number of times each proof rule is used. *)
  let index p =
    let Proof(_,c) = p in
    match c with
    | Prefl _ -> 0
    | Ptrans _ -> 1
    | Pmkcomb _ -> 2
    | Pabs _ -> 3
    | Pbeta _ -> 4
    | Passume _ -> 5
    | Peqmp _ -> 6
    | Pdeduct _ -> 7
    | Pinst _ -> 8
    | Pinstt _ -> 9
    | Paxiom _ -> 10
    | Pdef _ -> 11
    | Pdeft _ -> 12
    | Ptruth -> 13
    | Pconj _ -> 14
    | Pconjunct1 _ -> 15
    | Pconjunct2 _ -> 16
    | Pmp _ -> 17
    | Pdisch _ -> 18
    | Pspec _ -> 19
    | Pgen _ -> 20
    | Pexists _ -> 21
    | Pdisj1 _ -> 22
    | Pdisj2 _ -> 23
    | Pdisj_cases _ -> 24
  in
  let name = function
    | 0 -> "refl"
    | 1 -> "trans"
    | 2 -> "comb"
    | 3 -> "abs"
    | 4 -> "beta"
    | 5 -> "assume"
    | 6 -> "eqmp"
    | 7 -> "deduct"
    | 8 -> "term_subst"
    | 9 -> "type_subst"
    | 10 -> "axiom"
    | 11 -> "sym_def"
    | 12 -> "type_def"
    | 13 -> "truth"
    | 14 -> "conj"
    | 15 -> "conjunct1"
    | 16 -> "conjunct2"
    | 17 -> "mp"
    | 18 -> "disch"
    | 19 -> "spec"
    | 20 -> "gen"
    | 21 -> "exists"
    | 22 -> "disj1"
    | 23 -> "disj2"
    | 24 -> "disj_cases"
    | _ -> assert false
  in
  let rule_uses = Array.make 25 0 in
  let f k p =
    let i = index p in
    let n = Array.get rule_uses i + 1 in
    Array.set rule_uses i n
  in
  iter_proofs f;
  let total = float_of_int (nb_proofs()) in
  let part n = float_of_int (100 * n) /. total in
  let f i n = log "%10s %9d %2.f%%\n" (name i) n (part n) in
  Array.iteri f rule_uses;
  log "number of proof steps: %d\nnumber of unused theorems: %d (%2.f%%)\n"
    (nb_proofs()) hist.(0) (part hist.(0))
;;

(****************************************************************************)
(* Build a map associating to each constant c a list of positions
   [p1;..;pn] such that pi is the position in the type of c of its
   i-th type variable (as given by tyvars). *)
(****************************************************************************)

let update_map_const_typ_vars_pos() =
  map_const_typ_vars_pos :=
    List.fold_left
      (fun map (n,b) ->
        let l = typ_vars_pos b in
        let ps =
          List.map
            (fun v ->
              match v with
              | Tyvar n ->
                 begin
                   try List.assoc n l
                   with Not_found -> assert false
                 end
              | _ -> assert false)
            (tyvars b)
        in
        MapStr.add n ps map)
      MapStr.empty (constants())
;;

let typ_var_pos_list = list_sep "; " (list_sep "," int);;

let print_map_const_typ_vars_pos() =
  MapStr.iter
    (fun c ps -> log "%s %a\n" c (olist (olist int)) ps)
    !map_const_typ_vars_pos;;

let const_typ_vars_pos n =
  try MapStr.find n !map_const_typ_vars_pos
  with Not_found -> log "no const_typ_vars_pos for %s\n%!" n; assert false;;

(****************************************************************************)
(* Type and term abbreviations to reduce size of generated files. *)
(****************************************************************************)

(* [map_typ] is used to hold a map from types to type abbreviations. *)
let map_typ = ref (MapTyp.empty : (int * int) MapTyp.t);;
let reset_map_typ() = map_typ := MapTyp.empty;;

(* [map_term] is used to hold a map from terms to term abbreviations. *)
let map_term = ref (MapTrm.empty : (int * int * hol_type list) MapTrm.t);;
let reset_map_term() = map_term := MapTrm.empty;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
