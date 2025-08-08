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
(* Functions on numbers. *)
(****************************************************************************)

let percent k n = (100 * k) / n;;

(****************************************************************************)
(* Functions on system calls. *)
(****************************************************************************)

let command s =
  match Sys.command s with
  | 0 -> ()
  | n -> log "Error: \"%s\" failed.\n" s; exit n
;;

(****************************************************************************)
(* Functions on files. *)
(****************************************************************************)

let log_open_out n = log_gen n; open_out n;;
let log_open_out_bin n = log_gen n; open_out_bin n;;

let log_open_in_bin n = log_read n; open_in_bin n;;

let create_file n f = let oc = log_open_out n in f oc; close_out oc;;
let create_file_bin n f = let oc = log_open_out_bin n in f oc; close_out oc;;

let read_file_bin n f = let ic = log_open_in_bin n in f ic; close_in ic;;

let concat fs out =
  log "generate %s ...\n%!" out;
  match fs with
  | [] -> command ("touch "^out)
  | _ -> command ("cat "^String.concat " " fs^" > "^out)
;;

let remove fs = command ("rm -f "^String.concat " " fs);;

let copy f1 f2 = log "generate %s ...\n%!" f2; command ("cp -f "^f1^" "^f2);;

let rename f1 f2 = log "generate %s ...\n%!" f2; command ("mv -f "^f1^" "^f2);;

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
  log_read dump_file;
  let ic = open_in_bin dump_file in
  let v = input_value ic in
  close_in ic;
  v

(* [write_val f v] write [v] in file [f]. *)
let write_val dump_file v =
  log_gen dump_file;
  let oc = open_out_bin dump_file in
  output_value oc v;
  close_out oc

(****************************************************************************)
(* Functions on strings. *)
(****************************************************************************)

let add_prefix prefix f x = prefix^f x;;

let concat_map f xs = String.concat "" (List.map f xs);;

let part i = "_part_" ^ string_of_int i;;

(* [get_part s suffix] returns [Some(n,k)] if [s=n^suffix^part(k)],
   and [None] otherwise. *)
let get_part s suffix =
  try
    let len_s = String.length s in
    let i = ref (len_s - 1) in
    (* compute part number *)
    let k =
      while !i >= 0 && s.[!i] <> '_' do decr i done;
      if !i < 0 then raise Exit;
      int_of_string (String.sub s (!i+1) (len_s - 1 - !i))
    in
    (* compute theorem name *)
    let len_suffix = String.length suffix + String.length "_part_" in
    if !i < len_suffix then raise Exit;
    let n = String.sub s 0 (!i - len_suffix + 1) in
    Some(n,k)
  with Exit -> None
;;

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
(* Functions on lists. *)
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

(* [remove_elts l l'] returns the elements of [l'] not in [l]. *)
let remove_elts l l' =
  List.fold_left (fun l' x -> if List.mem x l then l' else x::l') [] l'
;;

(****************************************************************************)
(* Functions on hash tables. *)
(****************************************************************************)

(* [bindings ht] returns the list of bindings in the hash table [ht]. *)
let bindings ht = Hashtbl.fold (fun x y acc -> (x,y)::acc) ht [];;
let sorted_bindings ht = List.sort Stdlib.compare (bindings ht);;

(* [array_of_hashtbl ht] turns an hash table into an array. *)
let array_of_hashtbl ht =
  Array.init (Hashtbl.length ht) (Hashtbl.find ht)
;;

(****************************************************************************)
(* Printing functions. See
https://www.lexifi.com/blog/ocaml/note-about-performance-printf-and-format/#*)
(****************************************************************************)

let char = output_char;;

let string = output_string;;

let int oc k = string oc (string_of_int k);;

let quote f oc x = char oc '\"'; f oc x; char oc '\"';;
let paren f oc x = char oc '('; f oc x; char oc ')';;
let set f oc x = char oc '{'; f oc x; char oc '}';;
let bracket f oc x = char oc '['; f oc x; char oc ']';;

let ostring = quote string;;

let digest oc d = string oc (Digest.to_hex d);;

let pair f g oc (x,y) = f oc x; char oc ','; g oc y;;
let opair f g = paren (pair f g);;

let prefix pre elt oc x = string oc pre; elt oc x;;
let suffix elt suf oc x = elt oc x; string oc suf;;

let list_sep sep elt oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs
;;

let list elt oc = List.iter (elt oc);;
let olist elt = bracket (list_sep "; " elt);;
let list_prefix p elt oc xs = list (prefix p elt) oc xs;;

let array elt oc = Array.iter (elt oc);;
let oarray elt = bracket (array (suffix elt "; "));;

let set_int oc s =
  char oc '{'; SetInt.iter (fun k -> int oc k; char oc ';') s; char oc '}';;
let set_str oc s =
  char oc '{'; SetStr.iter (fun s -> string oc s; char oc ';') s; char oc '}';;

let htbl ppkey ppval oc ht =
  (*Hashtbl.iter (opair oc)*)
  List.iter (opair ppkey ppval oc) (sorted_bindings ht);;

let hstats oc hs =
  let open Hashtbl in
  let avg = float_of_int hs.num_bindings /. float_of_int hs.num_buckets in
  out oc "%#d bindings, %#d buckets, %.2f bindings/bucket, max %#d\n"
    hs.num_bindings hs.num_buckets avg hs.max_bucket_length;
  let histo = hs.bucket_histogram in
  out oc "buckets with 0 bindings: %#d (%d%% of buckets)\n"
    histo.(0) (percent histo.(0) hs.num_buckets);
  out oc "| bindings | buckets |    %% | cumulated | %% bindings |\n";
  out oc "|----------|---------|-------|-----------|-------------|\n";
  let sum = ref 0 in
  for i = 1 to min 10 hs.max_bucket_length do
    let n = i * histo.(i) in
    sum := !sum + n;
    out oc "| %8d | %#7d | %3d%% | %#9d | %2d%% |\n"
      i histo.(i) (percent n hs.num_bindings)
      !sum (percent !sum hs.num_bindings)
  done
;;

(****************************************************************************)
(* Sharing of strings. *)
(****************************************************************************)

module StrHash = struct
  type t = string
  let equal x1 x2 = x1 == x2 || x1 = x2
  let hash x = Hashtbl.hash x
end;;

module StrHashtbl = Hashtbl.Make(StrHash);;

let htbl_string : string StrHashtbl.t = StrHashtbl.create 10_000;;

let share_string x =
  try StrHashtbl.find htbl_string x
  with Not_found -> StrHashtbl.add htbl_string x x; x;;

(****************************************************************************)
(* Sharing of types when building canonical types. *)
(****************************************************************************)

module TypHash = struct
  type t = hol_type
  let equal x1 x2 =
    x1 == x2 ||
      match x1, x2 with
      | Tyvar s1, Tyvar s2 -> s1 == s2
      | Tyapp(s1,bs1), Tyapp(s2,bs2) -> s1 == s2 && List.for_all2 (==) bs1 bs2
      | _ -> false
  let hash x = Hashtbl.hash x
end;;

module TypHashtbl = Hashtbl.Make(TypHash);;

let htbl_type : hol_type TypHashtbl.t = TypHashtbl.create 100_000;;

let share_type x =
  try TypHashtbl.find htbl_type x
  with Not_found -> TypHashtbl.add htbl_type x x; x;;

let hmk_vartype s = share_type (Tyvar(share_string s));;
let hmk_tyapp(s,bs) = share_type (Tyapp(share_string s,bs));;

let rec htype = function
  | Tyvar s -> hmk_vartype s
  | Tyapp(s,bs) -> hmk_tyapp(s, List.map htype bs);;

(****************************************************************************)
(* Sharing of terms when building canonical terms. *)
(****************************************************************************)

module TrmHash = struct
  type t = term
  let equal x1 x2 =
    x1 == x2 ||
      match x1,x2 with
      | Var(s1,b1), Var(s2,b2)
        | Const(s1,b1), Const(s2,b2) -> s1 == s2 && b1 == b2
      | Comb(t1,u1), Comb(t2,u2)
        | Abs(t1,u1), Abs(t2,u2) -> t1 == t2 && u1 == u2
      | _ -> false
  let hash x = Hashtbl.hash x
end;;

module TrmHashtbl = Hashtbl.Make(TrmHash);;

let htbl_term : term TrmHashtbl.t = TrmHashtbl.create 1_000_000;;

let share_term x =
  try TrmHashtbl.find htbl_term x
  with Not_found -> TrmHashtbl.add htbl_term x x; x;;

let hmk_var(s,b) = share_term (Var(share_string s, htype b));;
let hmk_const(s,b) = share_term (Const(share_string s, htype b));;
let hmk_comb(t,u) = share_term (Comb(t,u));;
let hmk_abs(t,u) = share_term (Abs(t,u));;

(****************************************************************************)
(* Functions on types. *)
(****************************************************************************)

let is_var_or_cst_type = function Tyvar _ | Tyapp(_,[]) -> true | _ -> false;;

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
  let rec aux b =
    match b with
    | Tyvar _ -> if List.mem b tvs then b else bool_ty
    | Tyapp(n,bs) -> mk_type(n, List.map aux bs)
  in aux
;;

(* [type_var i tv] returns [v, tv] where [v] is the type variable of
   name ["a" ^ string_of_int i]. *)
let type_var =
  let va = Array.init 20 (fun i -> hmk_vartype ("a" ^ string_of_int i)) in
  fun i tv ->
  let v =
    if i < Array.length va then va.(i)
    else (log "a_max = %d\n%!" i; hmk_vartype ("a" ^ string_of_int i))
  in v, tv
;;
(*
(* Without sharing, [canonical_typ b] returns the type variables of
   [b] together with a type alpha-equivalent to [b] such that, for any
   type [b'] alpha-equivalent to [b], [canonical_typ b' =
   canonical_typ b]. *)
let canonical_typ b =
  let tvs = tyvars b in tvs, type_subst (List.mapi type_var tvs) b
;;
*)
(* With sharing, [canonical_typ b] returns the type variables of [b]
   and a type similar to [b] except that type variables are replaced
   by the canonical type variables [a0, a1, ...]. *)
let canonical_typ =
  let rec type_subst s b =
    match b with
    | Tyapp(c,bs) -> hmk_tyapp (c, List.map (type_subst s) bs)
    | _ -> Lib.rev_assocd b s b
  in
  fun b ->
  let tvs = tyvars b in tvs, type_subst (List.mapi type_var tvs) b
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

(* [size_type b] computes the tree size of a type [b]. *)
let rec size_type = function
  | Tyvar _ -> 1
  | Tyapp(_,bs) -> add_size_types 1 bs

and add_size_types acc bs =
  List.fold_left (fun acc b -> acc + size_type b) acc bs;;

(****************************************************************************)
(* Functions on terms. *)
(****************************************************************************)

let is_var_or_cst_term = function Var _ | Const _ -> true | _ -> false;;

(* [get_vartype t] returns the type of [t] assuming that [t] is a variable. *)
let get_vartype = function Var(_,b) -> b | _ -> assert false;;

(* [nb_cons t] computes the number of term constructors in the term [t]. *)
let rec nb_cons = function
  | Var _ | Const _ -> 1
  | Comb(u,v) | Abs(u,v) -> 1 + nb_cons u + nb_cons v
;;

(* [size_term t] computes the tree size of the term [t]. *)
let rec size_term = function
  | Var (_,b) | Const(_,b) -> 1 + size_type b
  | Comb(u,v) | Abs(u,v) -> 1 + size_term u + size_term v
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

(* [head_args t] returns the pair [h,ts] such that [t] is the
   application of [h] to [ts] and [h] is not a [Comb]. *)
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

(* [type_vars_in_terms ts] returns an un ordered list possibly with
   duplicate of type variables occurring in the list of terms [ts]. *)
let type_vars_in_terms ts =
  List.fold_left (fun l t -> type_vars_in_term t @ l) [] ts
;;

(* [type_vars_in_terms th] returns an unordered list possibly with
   duplicate of type variables occurring in the theorem [th]. *)
let type_vars_in_thm thm =
  let ts,t = dest_thm thm in type_vars_in_terms (t::ts);;
;;

(* [extra_type_vars_in_proof_content p] returns possible extra type
   variables occurring in the proof content [pc]. *)
let extra_type_vars_in_proof_content proof_at pc =
  match pc with
  | Ptrans(i,_)
  | Peqmp(_,i)
  | Pmp(_,i)
  | Pchoose(_,_,i)
  | Pdisj_cases(i,_,_) ->
     let Proof(thm,_) = proof_at i in type_vars_in_thm thm
  | Pexists(_,t,_) -> type_vars_in_term t
  | _ -> []
;;

(* [type_vars_in_proof proof_at p] returns the ordered list with no
   duplicate of type variables occurring in the proof [p]. *)
let type_vars_in_proof proof_at p =
  let Proof(thm,pc) = p in
  List.sort_uniq compare
    (extra_type_vars_in_proof_content proof_at pc @ type_vars_in_thm thm)
;;

(* Redefinition of [type_vars_in_term] so that the output is sorted
   and has no duplicate. *)
let type_vars_in_term t = List.sort_uniq compare (type_vars_in_term t);;

(* Redefinition of [type_vars_in_terms] so that the output is sorted
   and has no duplicate. *)
let type_vars_in_terms ts = List.sort_uniq compare (type_vars_in_terms ts);;

(* Redefinition of [type_vars_in_thm] so that the output is sorted
   and has no duplicat. *)
let type_vars_in_thm thm = List.sort_uniq compare (type_vars_in_thm thm);;

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

(* [term_var i v] returns [v,v'] where [v'] is a variable of name ["x"
   ^ string_of_int i] with the same type as [v]. *)
let term_var =
  let sx = Array.init 50 (fun i -> "x" ^ string_of_int i) in
  fun i v ->
  match v with
  | Var(_,b) ->
     let s =
       if i < Array.length sx then sx.(i)
       else (log "x_max = %d\n%!" i; "x" ^ string_of_int i)
     in v, hmk_var(s,b)
  | _ -> assert false
;;
(*
(* [canonical_term t] returns the free type and term variables of [t]
   together with a term alpha-equivalent to [t] so that
   [canonical_term t = canonical_term u] if [t] and [u] are
   alpha-equivalent. *)
let canonical_term =
  (*let a_max = ref 0 and x_max = ref 0 and y_max = ref 0 in*)
  let sy = Array.init 50 (fun i -> "y" ^ string_of_int i) in
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
  let bs = List.map get_vartype vs' and su' = List.mapi term_var vs' in
  tvs, vs, bs, subst 0 su' t'
;;
 *)
(****************************************************************************)
(* Canonical term for alpha-equivalence with sharing. *)
(****************************************************************************)

(* [canonical_term t] returns [tvs,vs,bs,u,n] where:
- [tvs] are the type variables of [t],
- [vs] are the free term variables of [t],
- [bs] are the types of [vs],
- [u] is a term similar to [t] except that [tvs] are replaced by
   canonical type variables [a0, a1, ...], [vs] are replaced by
   canonical term variables [x0, x1, ...], and the abstracted term
   variables are replaced by canonical variables [y0, y1, ...]. Hence,
   if [t'] is alpha-equivalent to [t], then [canonical_term t' = u]. *)
let canonical_term
    : term -> hol_type list * term list * hol_type list * term =
  (*let a_max = ref 0 and x_max = ref 0 and y_max = ref 0 in*)
  let sy = Array.init 50 (fun i -> "y" ^ string_of_int i) in
  (* [subst i su t] applies [su] on [t] and rename abstracted
     variables as well by incrementing the integer [i]. [su] is a term
     substitution mapping term variables abstracted in [t] by the
     canonical term variables [y0, y1, ...]. *)
  let rec subst i su t =
    (*log "subst %d %a %a\n%!" i (olist (opair oterm oterm)) su oterm t;*)
    match t with
    | Var _ -> (try List.assoc t su with Not_found -> assert false)
    | Const(s,b) -> hmk_const(s,b)
    | Comb(u,v) -> hmk_comb(subst i su u, subst i su v)
    | Abs(u,v) ->
       match u with
       | Var(_,b) ->
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
  (* Type substitution mapping type variables of [t] to the canonical
     type variables [a0, a1, ...]. *)
  let su = List.mapi type_var tvs in
  let t' = inst su t and vs' = List.map (inst su) vs in
  let bs = List.map get_vartype vs'
  (* Term substitution mapping term variables of [t] to the canonical
     term variables [x0, x1, ...]. *)
  and su' = List.mapi term_var vs' in
  tvs, vs, bs, subst 0 su' t'
;;

(****************************************************************************)
(* Functions on proofs. *)
(****************************************************************************)

(* rename theorem indexes according to [map]. *)
let rename_pc map pc =
  let rename i = try MapInt.find i map with Not_found -> i in
  match pc with
  | Ptrans(i,j) -> Ptrans(rename i,rename j)
  | Pmkcomb(i,j) -> Pmkcomb(rename i,rename j)
  | Pabs(i,t) -> Pabs(rename i,t)
  | Peqmp(i,j) -> Peqmp(rename i,rename j)
  | Pdeduct(i,j) -> Pdeduct(rename i,rename j)
  | Pinst(i,s) -> Pinst(rename i,s)
  | Pinstt(i,s) -> Pinstt(rename i,s)
  | Pdeft(i,t,s,a) -> Pdeft(rename i,t,s,a)
  | Pconj(i,j) -> Pconj(rename i,rename j)
  | Pconjunct1 i -> Pconjunct1(rename i)
  | Pconjunct2 i -> Pconjunct2(rename i)
  | Pmp(i,j) -> Pmp(rename i,rename j)
  | Pdisch(t,i) -> Pdisch(t,rename i)
  | Pspec(t,i) -> Pspec(t,rename i)
  | Pgen(t,i) -> Pgen(t,rename i)
  | Pexists(t,u,i) -> Pexists(t,u,rename i)
  | Pchoose(t,i,j) -> Pchoose(t,rename i,rename j)
  | Pdisj1(t,i) -> Pdisj1(t,rename i)
  | Pdisj2(t,i) -> Pdisj2(t,rename i)
  | Pdisj_cases(i,j,k) -> Pdisj_cases(rename i,rename j,rename k)
  | Psym i -> Psym(rename i)
  | Prefl _ | Pbeta _ | Passume _ | Paxiom _ | Pdef _ | Ptruth -> pc
;;

(* [size_content nb_type_vars nb_term_vars content] computes an
   approximation of the tree size of the Dedukti representation of the
   proof [content]. *)
let size_content nb_type_vars nb_term_vars nb_hyps c =
  let typ = 1 + 2*nb_type_vars in
  let trm = typ + 2*nb_term_vars in
  let prf = trm + 2*nb_hyps in
  let step(nb_types,nb_terms,nb_proofs) =
    1 + nb_types*(1+typ) + nb_terms*(1+trm) + nb_proofs*(1+prf) in
  match c with
  | Prefl _ -> step(1,1,0)
  | Psym _ -> step(1,2,1)
  | Ptrans _ -> step(1,3,2)
  | Pmkcomb _ -> step(2,4,2)
  | Pabs _ -> step(3,2,1)
  | Pbeta _ -> step(1,1,0)
  | Passume _ -> 1
  | Peqmp _ -> step(0,2,2)
  | Pdeduct _ -> step(0,4,2)
  | Pinst(_,s) -> let n = List.length s in step(n,n,1)
  | Pinstt(_,s) -> let n = List.length s in step(n,n,1)
  | Paxiom _ -> step(1,1,0)
  | Pdef _ -> step(1,1,0)
  | Pdeft _ -> step(1,1,0)
  | Ptruth -> 1
  | Pconj _ -> step(0,2,2)
  | Pconjunct1 _ -> step(0,2,2)
  | Pconjunct2 _ -> step(0,2,2)
  | Pmp _ -> step(0,0,2)
  | Pdisch _ -> step(0,1,1)
  | Pspec _ -> step(0,1,1)
  | Pgen _ -> step(1,0,1)
  | Pexists _ -> step(1,2,1)
  | Pdisj1 _ -> step(0,2,1)
  | Pdisj2 _ -> step(0,2,1)
  | Pdisj_cases _ -> step(0,5,3)
  | Pchoose _ -> step(3,3,2)
;;

(* [size_proof p] computes an approximation of the tree size of the
   Dedukti representation of the proof [p]. *)
let size_proof (Proof(thm, content)) =
  let (ts,t) = dest_thm thm in
  let nb_type_vars = List.length (type_vars_in_thm thm)
  and nb_term_vars = List.length (Fusion.freesl (t::ts))
  and nb_hyps = List.length ts in
  let typ = 1 + 2*nb_type_vars in
  let trm = typ + 2*nb_term_vars in
  1 + 2*nb_type_vars + 2*nb_term_vars*typ + 2*nb_hyps*trm
  + size_content nb_type_vars nb_term_vars nb_hyps content
;;

(* [size_abbrev a] computes an approximation of the tree size of the
   Dedukti representation of the term abbreviation [a]. *)
let size_abbrev (t,(_,ltvs,bs)) =
  let nb_type_vars = ltvs in
  let nb_term_vars = List.length bs in
  let typ = 1 + 2*ltvs in
  1 + 2*nb_type_vars + 2*nb_term_vars*typ + size_term t
;;

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
(* Sharing of subterms. *)
(****************************************************************************)

(* [htype_of] is the composition of [htype] and [type_of]. *)
let rec htype_of =
  let arr = share_string "fun" in
  fun tm ->
  match tm with
    Var(_,ty) -> htype ty
  | Const(_,ty) -> htype ty
  | Comb(s,_) ->
     begin
       match htype_of s with
       | Tyapp("fun",[_;rty]) -> rty
       | _ -> assert false
     end
  | Abs(Var(_,ty),t) -> hmk_tyapp(arr, [ty; htype_of t])
  | _ -> assert false
;;

(* Table mapping a term [t] to [t,t',c,k] where [t'] is the alias for
   [t], [c] indicates if [t] contains some variable, and [k] indicates
   the rank of the alias. *)
let htbl_subterms : (term * term * bool * int) TrmHashtbl.t =
  TrmHashtbl.create 1_000_000;;

(* [contains_var_typ b] holds iff [b] contains a type variable. *)
let rec contains_var_typ b =
  match b with
  | Tyvar _ -> true
  | Tyapp(_,bs) -> List.exists contains_var_typ bs
;;

(* [contains_var t] holds iff [t] contains a term or type variable. *)
let rec contains_var t =
  match t with
  | Var _ | Abs _ -> true
  | Const(_,b) -> contains_var_typ b
  | Comb(u,v) -> contains_var v || contains_var u
;;

let share_subterm =
  let idx = ref (-1) in
  fun l t ->
  try let (t,t',c,_) as x = TrmHashtbl.find htbl_subterms t in
      if c && t != t' && List.for_all ((!=) x) !l then l := x::!l; t'
  with Not_found ->
    match t with
    | Var _ -> TrmHashtbl.add htbl_subterms t (t,t,true,-1); t
    | Const(_,b) ->
       TrmHashtbl.add htbl_subterms t (t,t,contains_var_typ b,-1); t
    | Comb(u,v) ->
       let k = !idx + 1 in
       idx := k;
       let s = share_string ("z" ^ string_of_int k) in
       let t' = mk_var(s, htype_of t) in
       let c =
         match TrmHashtbl.find_opt htbl_subterms v with
         | None -> contains_var v
         | Some(_,_,true,_) -> true
         | Some(_,_,false,_) ->
            match TrmHashtbl.find_opt htbl_subterms u with
            | Some(_,_,c,_) -> c
            | None -> contains_var u
       in
       let x = (t,t',c,k) in
       TrmHashtbl.add htbl_subterms t x;
       if c then l := x::!l; t'
    | Abs _ ->
       let k = !idx + 1 in
       idx := k;
       let s = share_string ("z" ^ string_of_int k) in
       let t' = mk_var(s, htype_of t) in
       let x = (t,t',true,k) in
       TrmHashtbl.add htbl_subterms t x;
       l := x::!l; t'
;;

let hmk_var l (s,b) = share_subterm l (Var(share_string s, htype b));;
let hmk_const l (s,b) = share_subterm l (Const(share_string s, htype b));;
let hmk_comb l (t,u) = share_subterm l (Comb(t,u));;
let hmk_abs l (t,u) = share_subterm l (Abs(t,u));;

(* [shared t] returns [u,l] where [u] is a variable and [l] is like a
   term substitution such that the repeated application of [l] to [u]
   gives [t]. *)
let shared t =
  (*log "\nshared %a\n" oterm t;*)
  let l = ref [] in
  let rec aux t =
    (*log "aux %a %a\n" (olist (opair oterm oterm)) !l oterm t;*)
    match t with
    | Var(s,b) -> hmk_var l (s,b)
    | Const(s,b) -> hmk_const l (s,b)
    | Comb(u,v) -> hmk_comb l (aux u, aux v)
    | Abs(u,v) -> hmk_abs l (u,v)
  in
  let t' = aux t in
  t', List.rev !l
;;

let use_sharing = ref false;;

(****************************************************************************)
(* Type and term abbreviations to reduce size of generated files. *)
(****************************************************************************)

(* Table mapping a type to its identifier and the number of its type
   variables. *)
let htbl_type_abbrev : (int * int) TypHashtbl.t = TypHashtbl.create 100_000;;

(* Table mapping a term to its identifier, the number of its type
   variables, and the types of its free term variables. *)
let htbl_term_abbrev : (int * int * hol_type list) TrmHashtbl.t =
  TrmHashtbl.create 1_000_000;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
