(****************************************************************************)
(* Useful functions on types, terms and other data structures. *)
(****************************************************************************)

(*REMOVE
unset_jrh_lexer;;
REMOVE*)

open Xprelude
open Fusion

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

(* [iter_parts n k f] splits the interval [0..n-1] in [k] parts and
   calls [f 1 x1 y1], .., [f k xk yk] where [xi] and [yi] are the
   starting and ending indexes (starting from 0) of part [i]. *)
let iter_parts nb_proofs nb_parts f =
  let part_size = nb_proofs / nb_parts in
  let x = ref 0 in
  for i = 1 to nb_parts - 1 do
    let y = !x + part_size in f i !x (y-1); x := y
  done;
  f nb_parts !x (nb_proofs - 1)
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

(* [string_of_file f] puts the contents of file [f] in a string. *)
let string_of_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s
;;

(* [read_val f] reads value from file [f]. *)
let read_val dump_file =
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  let v = input_value ic in
  close_in ic;
  v

(* [write_val f v] write [v] in file [f]. *)
let write_val dump_file v =
  log "write %s ...\n%!" dump_file;
  let oc = open_out_bin dump_file in
  output_value oc v;
  close_out oc

(* [replace c1 c2 s] returns a new string identical to [s] but with
   every character [c1] replaced by [c2]. *)
let replace c1 c2 s =
  let b = String.to_bytes s in
  for i=0 to Bytes.length b - 1 do
    if Bytes.get b i = c1 then Bytes.set b i c2
  done;
  String.of_bytes b

(* [starts_with p s] says if the string [s] starts by [p]. *)
let starts_with p s =
  let n = String.length p in String.length s >= n && p = String.sub s 0 n

let _ =
  assert (starts_with "a" "" = false);
  assert (starts_with "a" "a" = true);
  assert (starts_with "a" "b" = false);
  assert (starts_with "a" "ab" = true);
  assert (starts_with "" "a" = true)

(* [change_prefix p q s] returns a string equal to [s] except if [s]
   starts with [p], in which case [p] is replaced by [q]. *)
let change_prefix p q s =
  let n = String.length p in
  if starts_with p s then q ^ String.sub s n (String.length s - n) else s

let _ =
  assert (change_prefix "a" "b" "" = "");
  assert (change_prefix "a" "b" "a" = "b");
  assert (change_prefix "a" "b" "c" = "c");
  assert (change_prefix "a" "b" "cd" = "cd");
  assert (change_prefix "a" "b" "ac" = "bc")

(* [change_prefixes l s] returns [s] if [s] starts with no string in
   [List.map fst l]. Otherwise it returns [change_prefix p q s] where
   [(p,q)] is the first element of [l] such that [starts_with p s]. *)
let rec change_prefixes l s =
  match l with
  | [] -> s
  | (p,q)::l ->
     let n = String.length p in
     if starts_with p s then q ^ String.sub s n (String.length s - n)
     else change_prefixes l s

(****************************************************************************)
(* Printing functions. *)
(****************************************************************************)

let int oc k = out oc "%d" k;;

let string oc s = out oc "%s" s;;

let ostring oc s = out oc "\"%s\"" s;;

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
    | (Tyapp(_,bs), p)::l ->
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

let rec size = function
  | Var _ | Const _ -> 1
  | Comb(u,v) -> 1 + size u + size v
  | Abs(_,v) -> 2 + size v
;;

(* Printing function for debug. *)
let rec oterm oc t =
  match t with
  | Var(n,b) -> out oc "Var(%s,%a)" n otyp b
  | Const(n,b) -> out oc "Const(%s,%a)" n otyp b
  | Comb(u,v) -> out oc "Comb(%a,%a)" oterm u oterm v
  | Abs(u,v) -> out oc "Abs(%a,%a)" oterm u oterm v
;;

let ovar oc = function Var(n,_) -> string oc n | _ -> assert false;;

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

(* Reserved names not to be used as variable names. *)
let reserved : SetStr.t ref = ref SetStr.empty;;

let update_reserved =
  let add_name s (n,_) = SetStr.add n s in
  fun () ->
  reserved :=
    let s = List.fold_left add_name SetStr.empty !the_type_constants in
    List.fold_left add_name s !the_term_constants
;;

(* [rename_var rmap v] returns a variable with the same type as the one
   of [v] but with a name not occuring in the codomain of [rmap]. *)
let rename_var rmap =
  let rec rename v =
    match v with
    | Var(n,b) ->
       if SetStr.mem n !reserved
          || let k = String.length n in
             (k > 1 && n.[0] = 'h' && n.[k-1] <> '\'')
             (* the last condition is important to avoid looping *)
          || List.exists (fun (_,s) -> s = n) rmap
       then rename (mk_var(n^"'",b))
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

(* [renaming_map tvs vs] returns an association list giving names to
   the term variables in [vs] that are distinct to one another and
   distinct from the type variables in [tvs]. This is needed to
   include type variables because HOL-Light may have type variables and
   term variables with the same name. *)
let renaming_map =
  let tyvar = function Tyvar n -> mk_var(n,bool_ty),n | _ -> assert false in
  fun tvs vs -> List.fold_left add_var (List.map tyvar tvs) vs;;

(* Add a new HOL-Light constant "el" that could be defined as:
let el b =
  mk_comb(mk_const("@",[b,aty]),mk_abs(mk_var("_",b),mk_const("T",[])))
*)
(*if not(!el_added) then (new_constant("el",aty); el_added := true);;*)
let mk_el b = mk_const("el",[b,aty]);;

(****************************************************************************)
(* Canonical term for alpha-equivalence without sharing. *)
(****************************************************************************)

(* [canonical_term t] returns the free type and term variables of [t]
   together with a term alpha-equivalent to [t] so that
   [canonical_term t = canonical_term u] if [t] and [u] are
   alpha-equivalent. *)
let canonical_term =
  (*let a_max = ref 0 and x_max = ref 0 and y_max = ref 0 in*)
  let va = Array.init 20 (fun i -> mk_vartype ("a" ^ string_of_int i))
  and sx = Array.init 50 (fun i -> "x" ^ string_of_int i)
  and sy = Array.init 50 (fun i -> "y" ^ string_of_int i) in
  let get_type = function Var(_,b) -> b | _ -> assert false in
  let type_var i tv =
    (*if i > !a_max then begin a_max := i; log "a_max = %d\n%!" i end;*)
    let v =
      if i < Array.length va then va.(i)
      else (log "a_max = %d\n%!" i; mk_vartype ("a" ^ string_of_int i))
    in v, tv
  in
  let term_var i v =
    (*if i > !x_max then begin x_max := i; log "x_max = %d\n%!" i end;*)
    match v with
    | Var(_,b) ->
       let s =
         if i < Array.length sx then sx.(i)
         else (log "x_max = %d\n%!" i; "x" ^ string_of_int i)
       in v, mk_var(s,b)
    | _ -> assert false
  in
  (* [subst i su t] applies [su] on [t] and rename abstracted
     variables as well by incrementing the integer [i]. *)
  let rec subst i su t =
    (*log "subst %d %a %a\n%!" i (olist (opair oterm oterm)) su oterm t;*)
    match t with
    | Var _ -> (try List.assoc t su with Not_found -> assert false)
    | Const _ -> t
    | Comb(u,v) -> mk_comb(subst i su u, subst i su v)
    | Abs(u,v) ->
       match u with
       | Var(_,b) ->
          (*if i > !y_max then begin y_max := i; log "y_max = %d\n%!" i end;*)
          let s =
            if i < Array.length sy then sy.(i)
            else (log "y_max = %d\n%!" i; "y" ^ string_of_int i)
          in
          let u' = mk_var(s,b) in
          mk_abs(u', subst (i+1) ((u,u')::su) v)
       | _ -> assert false
  in
  fun t ->
  let tvs = type_vars_in_term t and vs = frees t in
  let su = List.mapi type_var tvs in
  let t' = inst su t and vs' = List.map (inst su) vs in
  let bs = List.map get_type vs' and su' = List.mapi term_var vs' in
  tvs, vs, bs, subst 0 su' t'
;;

(****************************************************************************)
(* Sharing of strings, types and terms. *)
(****************************************************************************)

module StrHash = struct
  type t = string
  let equal x1 x2 = x1 = x2
  let hash x = Hashtbl.hash x
end;;

module StrHashtbl = Hashtbl.Make(StrHash);;

let hmap_string : string StrHashtbl.t = StrHashtbl.create 100_000;;

let share_string x =
  try StrHashtbl.find hmap_string x
  with Not_found -> StrHashtbl.add hmap_string x x; x;;

module TypHash = struct
  type t = hol_type
  let equal x1 x2 = x1 = x2
  let hash x = Hashtbl.hash x
end;;

module TypHashtbl = Hashtbl.Make(TypHash);;

let hmap_type : hol_type TypHashtbl.t = TypHashtbl.create 100_000;;

let share_type x =
  try TypHashtbl.find hmap_type x
  with Not_found -> TypHashtbl.add hmap_type x x; x;;

let hmk_tyvar s = share_type (Tyvar(share_string s));;
let hmk_tyapp(s,bs) = share_type (Tyapp(share_string s,bs));;

let rec htype = function
  | Tyvar s -> hmk_tyvar s
  | Tyapp(s,bs) -> hmk_tyapp(s, List.map htype bs);;

module TrmHash = struct
  type t = term
  let equal x1 x2 =
    match x1,x2 with
    | Var(s1,b1), Var(s2,b2)
    | Const(s1,b1), Const(s2,b2) -> s1 == s2 && b1 == b2
    | Comb(t1,u1), Comb(t2,u2)
    | Abs(t1,u1), Abs(t2,u2) -> t1 == t2 && u1 == u2
    | _ -> false
  let hash x = Hashtbl.hash x
end;;

module TrmHashtbl = Hashtbl.Make(TrmHash);;

let hmap_term : term TrmHashtbl.t = TrmHashtbl.create 1_000_000;;

let share_term x =
  try TrmHashtbl.find hmap_term x
  with Not_found -> TrmHashtbl.add hmap_term x x; x;;

let hmk_var(s,b) = share_term (Var(share_string s, htype b));;
let hmk_const(s,b) = share_term (Const(share_string s, htype b));;
let hmk_comb(t,u) = share_term (Comb(t,u));;
let hmk_abs(t,u) = share_term (Abs(t,u));;

(****************************************************************************)
(* Canonical term for alpha-equivalence with sharing. *)
(****************************************************************************)

(* [hcanonical_term t] returns the free type and term variables of [t]
   together with a term alpha-equivalent to [t] so that
   [canonical_term t = canonical_term u] if [t] and [u] are
   alpha-equivalent. *)
let hcanonical_term =
  (*let a_max = ref 0 and x_max = ref 0 and y_max = ref 0 in*)
  let va = Array.init 20 (fun i -> hmk_tyvar ("a" ^ string_of_int i))
  and sx = Array.init 50 (fun i -> "x" ^ string_of_int i)
  and sy = Array.init 50 (fun i -> "y" ^ string_of_int i) in
  let get_type = function Var(_,b) -> b | _ -> assert false in
  let type_var i tv =
    (*if i > !a_max then begin a_max := i; log "a_max = %d\n%!" i end;*)
    let v =
      if i < Array.length va then va.(i)
      else (log "a_max = %d\n%!" i; hmk_tyvar ("a" ^ string_of_int i))
    in v, tv
  in
  let term_var i v =
    (*if i > !x_max then begin x_max := i; log "x_max = %d\n%!" i end;*)
    match v with
    | Var(_,b) ->
       let s =
         if i < Array.length sx then sx.(i)
         else (log "x_max = %d\n%!" i; "x" ^ string_of_int i)
       in v, hmk_var(s,b)
    | _ -> assert false
  in
  (* [subst i su t] applies [su] on [t] and rename abstracted
     variables as well by incrementing the integer [i]. *)
  let rec subst i su t =
    (*log "subst %d %a %a\n%!" i (olist (opair oterm oterm)) su oterm t;*)
    match t with
    | Var _ -> (try List.assoc t su with Not_found -> assert false)
    | Const(s,b) -> hmk_const(s,b)
    | Comb(u,v) -> hmk_comb(subst i su u, subst i su v)
    | Abs(u,v) ->
       match u with
       | Var(_,b) ->
          (*if i > !y_max then begin y_max := i; log "y_max = %d\n%!" i end;*)
          let s =
            if i < Array.length sy then sy.(i)
            else (log "y_max = %d\n%!" i; "y" ^ string_of_int i)
          in
          let u' = hmk_var(s,b) in
          hmk_abs(u', subst (i+1) ((u,u')::su) v)
       | _ -> assert false
  in
  fun t ->
  let tvs = type_vars_in_term t and vs = frees t in
  let su = List.mapi type_var tvs in
  let t' = inst su t and vs' = List.map (inst su) vs in
  let bs = List.map get_type vs' and su' = List.mapi term_var vs' in
  tvs, vs, bs, subst 0 su' t'
;;

let sharing = ref false;;

let canonical_term t =
  if !sharing then hcanonical_term t else canonical_term t;;

(****************************************************************************)
(* Functions on proofs. *)
(****************************************************************************)

(* [proof oc p] prints the proof [p] on out_channel [oc] in a user
   readable format. *)
let proof oc (Proof(_,c)) =
  match c with
  | Prefl _ -> out oc "refl"
  | Ptrans(i,j) -> out oc "trans %d %d" i j
  | Pmkcomb(i,j) -> out oc "mkcomb %d %d" i j
  | Pabs(i,_) -> out oc "abs %d" i
  | Pbeta _ -> out oc "beta"
  | Passume _ -> out oc "assume"
  | Peqmp(i,j) -> out oc "eqmp %d %d" i j
  | Pdeduct(i,j) -> out oc "deduct %d %d" i j
  | Pinst(i,_) -> out oc "inst %d" i
  | Pinstt(i,_) -> out oc "inst_type %d" i
  | Paxiom _ -> out oc "axiom"
  | Pdef _ -> out oc "def"
  | Pdeft(i,_,_,_) -> out oc "def_type %d" i
  | Ptruth -> out oc "truth"
  | Pconj(i,j) -> out oc "conj %d %d" i j
  | Pconjunct1 i -> out oc "conjunct1 %d" i
  | Pconjunct2 i -> out oc "conjunct2 %d" i
  | Pmp(i,j) -> out oc "mp %d %d" i j
  | Pdisch(_,i) -> out oc "disch %d" i
  | Pspec(_,i) -> out oc "spec %d" i
  | Pgen(_,i) -> out oc "gen %d" i
  | Pexists(_,_,i) -> out oc "exists %d" i
  | Pdisj1(_,i) -> out oc "disj1 %d" i
  | Pdisj2(_,i) -> out oc "disj2 %d" i
  | Pdisj_cases(i,j,k) -> out oc "disj_cases %d %d %d" i j k
  | Pchoose(_,i,j) -> out oc "choose %d %d" i j
  | Psym i -> out oc "sym %d" i
;;

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
  | Pconj(k1,k2) | Pmp(k1,k2) | Pchoose(_,k1,k2)
    -> [k1;k2]
  | Pabs(k,_) | Pinst(k,_) | Pinstt(k,_)| Pdeft(k,_,_,_)
  | Pconjunct1 k | Pconjunct2 k | Pdisch(_,k) | Pspec(_,k) | Pgen(_,k)
  | Pexists(_,_,k) | Pdisj1(_,k) | Pdisj2(_,k) | Psym k
    -> [k]
  | Prefl _ | Pbeta _ | Passume _ | Paxiom _ | Pdef _ | Ptruth
    -> []
;;

(* [count_thm_uses a p] increments by 1 every [a.(i)] such that [i] is
   a dependence of [p]. *)
let count_thm_uses (a : int array) (p : proof) : unit =
  List.iter (fun k -> Array.set a k (Array.get a k + 1)) (deps p)
;;

(* [print_histogram a] prints on stdout the number of elements of [a]
   that are used [i] times, for each [i] from 0 to the maximum of
   [a]. *)
let print_histogram (a : int array) : unit =
  (* compute max and argmax *)
  let max = ref (-1) and argmax = ref (-1) and unused = ref (-1) in
  let f k n =
    if n > !max then (max := n; argmax := k);
    if n = 0 then unused := k
  in
  Array.iteri f a;
  let hist = Array.make (!max + 1) 0 in
  Array.iter (fun n -> Array.set hist n (Array.get hist n + 1)) a;
  log "(* \"i: n\" means that n proofs are used i times *)\n";
  let nonzeros = ref 0 in
  Array.iteri
    (fun i n -> if n > 0 then (incr nonzeros; log "%d: %d\n" i n)) hist;
  log "number of mappings: %d\n" !nonzeros;
  log "most used theorem: %d\n" !argmax;
  log "unused theorems (including named theorems): %d (%d%%)\n"
    hist.(0) ((100 * hist.(0)) / Array.length a);
  log "last unused theorem: %d\n" !unused
;;

(* [code_of_proof p] maps every Proof constructor to a unique integer. *)
let code_of_proof (Proof(_,c)) =
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
  | Pchoose _ -> 25
  | Psym _ -> 26
;;

(* [name_of_code k] maps every integer k in the image of
   [code_of_proof] to a unique string. *)
let name_of_code = function
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
  | 25 -> "choose"
  | 26 -> "sym"
  | _ -> assert false
;;

(* [nb_rules] is the total number of proof rules. *)
let nb_rules = 27;;

(* [count_rule_uses a p] increments [a.(code_of_proof p)] by 1. [a]
   must be an array of integers of size [nb_rules]. *)
let count_rule_uses (a : int array) (p : proof) : unit =
  let i = code_of_proof p in Array.set a i (Array.get a i + 1)
;;

(* [print_rule_uses a nb_proofs] prints on stdout the array [a] of
   integers of size [nb_rules] and the corresponding percentages wrt
   [nb_proofs]. *)
let print_rule_uses (a : int array) (nb_proofs : int) : unit =
  let l = ref [] in
  Array.iteri (fun i n -> l := (name_of_code i,n)::!l) a;
  let cmp (_,n1) (_,n2) = Stdlib.compare n2 n1 in
  let l = List.sort cmp !l in
  let total = float_of_int nb_proofs in
  let part n = float_of_int (100 * n) /. total in
  List.iter (fun (s,n) -> log "%10s %9d %3.0f%%\n" s n (part n)) l;
  let total = Array.fold_left (+) 0 a in
  log "%10s %9d %3.0f%%\n" "TOTAL" total (part total)
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
let map_typ : (int * int) MapTyp.t ref = ref MapTyp.empty;;

(* [map_term] is used to hold a map from terms to term abbreviations. *)
let map_term : (int * int * hol_type list) MapTrm.t ref = ref MapTrm.empty;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
