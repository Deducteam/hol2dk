(* Slight modification of fusion.ml to dump proofs. *)
(*REMOVE*)module [@warning "-8-32-27"] M = struct

(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib

module type Hol_kernel =
  sig
      type hol_type =
      (*REMOVE
      private
      REMOVE*)
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term =
      (*REMOVE
      private
      REMOVE*)
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term

      type thm

      type proof_content =
        | Prefl of term (* Prefl(t):t=t *)
        | Ptrans of int * int (* i:t=u j:u=v ==> Ptrans(i,j):t=v *)
        | Pmkcomb of int * int (* i:s=t j:u=v ==> Pmkcomb(i,j):s(u)=t(v) *)
        | Pabs of int * term (* i:s=t ==> Pabs(i,x):\x,s=\x,t *)
        | Pbeta of term (* Pbeta((\x,t)x):(\x,t)x=t *)
        | Passume of term (* Passume(p): {p} |- p *)
        | Peqmp of int * int (* i:p=q j:p ==> Peqmp(i,j):q *)
        | Pdeduct of int * int (* i:p j:q ==> Pdeduct(i,j):p=q *)
        | Pinst of int * (term * term) list (* i:p ==> Pinst(i,s):s(p) *)
        | Pinstt of int * (hol_type * hol_type) list
        (* i:p ==> Pinstt(i,s):s(p) *)
        | Paxiom of term (* Paxiom(p):p *)
        | Pdef of term * string * hol_type (* Pdef(t,n,b):n=t *)
        | Pdeft of int * term * string * hol_type (* Pdeft(i,t,n,b):? *)
        | Ptruth (* Ptruth:T *)
        | Pconj of int * int (* i:p j:q ==> Pconj(i,j):p/\q *)
        | Pconjunct1 of int (* i:p/\_ ==> Pconjunct1(i):p *)
        | Pconjunct2 of int (* i:_/\q ==> Pconjunct2(i):q *)
        | Pmp of int * int (* i:p=>q j:p ==> Pmp(i,j):q *)
        | Pdisch of term * int (* i:q ==> Pdisch(p,i):p=>q *)
        | Pspec of term * int (* i:∀p ==> Pspec(t,i):p(t) *)
        | Pgen of term * int (* i:p ==> Pgen(x,i):∀x,p *)
        | Pexists of term * term * int (* i:p(t) ==> Pexists(p,t,i):∃p *)
        | Pchoose of term * int * int
        (* i:∃p j:p(t)|-q ==> Pchoose(t,i,j):q *)
        | Pdisj1 of term * int (* i:p ==> Pdisj1(q,i):p\/q *)
        | Pdisj2 of term * int (* i:q ==> Pdisj2(p,i):p\/q *)
        | Pdisj_cases of int * int * int
        (* i:p\/q j:p|-r k:q|-r ==> Pdisj_cases(i,j,k):r *)
        | Psym of int (* i:p=q ==> Psym(i):q=p *)

      type proof = Proof of (thm * proof_content)

      val index_of : thm -> int
      val content_of : proof -> proof_content
      val change_content : proof -> proof_content -> proof

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      (*REMOVE
      val new_type : (string * int) -> unit
      REMOVE*)
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val get_const_type : string -> hol_type
      (*REMOVE
      val new_constant : string * hol_type -> unit
      REMOVE*)
      val type_of : term -> hol_type
      val alphaorder : term -> term -> int
      val is_var : term -> bool
      val is_const : term -> bool
      val is_abs : term -> bool
      val is_comb : term -> bool
      val mk_var : string * hol_type -> term
      val mk_const : string * (hol_type * hol_type) list -> term
      val mk_abs : term * term -> term
      val mk_comb : term * term -> term
      val dest_var : term -> string * hol_type
      val dest_const : term -> string * hol_type
      val dest_comb : term -> term * term
      val dest_abs : term -> term * term
      val frees : term -> term list
      val freesl : term list -> term list
      val freesin : term list -> term -> bool
      val vfree_in : term -> term -> bool
      val type_vars_in_term : term -> hol_type list
      val variant : term list -> term -> term
      val vsubst : (term * term) list -> term -> term
      val inst : (hol_type * hol_type) list -> term -> term
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      (*REMOVE
      val REFL : term -> thm
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
      val axioms : unit -> thm list
      val new_axiom : term -> thm
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm

      (*START_ND*)
      val TRUTH : thm
      val CONJ : thm -> thm -> thm
      val CONJUNCT1 : thm -> thm
      val CONJUNCT2 : thm -> thm
      val MP : thm -> thm -> thm
      val DISCH : term -> thm -> thm
      val SPEC : term -> thm -> thm
      val GEN : term -> thm -> thm
      val EXISTS : term * term -> thm -> thm
      val CHOOSE : (term * thm) -> thm -> thm
      val DISJ1 : thm -> term -> thm
      val DISJ2 : term -> thm -> thm
      val DISJ_CASES : thm -> thm -> thm -> thm
      val ALPHA : term -> term -> thm
      val SYM : thm -> thm
      val BETA_CONV : term -> thm
      (*END_ND*)

      val new_theorem : term list -> term -> proof_content -> thm
      val dump_nb_proofs : string -> unit
      val dump_signature : string -> unit
      val oc_dump : out_channel
      REMOVE*)
      (*REMOVE*)val the_type_constants : (string * int) list ref
      (*REMOVE*)val the_term_constants : (string * hol_type) list ref
      (*REMOVE*)val the_axioms : thm list ref
      (*REMOVE*)val the_definitions : thm list ref
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term


  type [@warning "-37"] thm = Sequent of (term list * term * int)

(*---------------------------------------------------------------------------*)
(* Proof dumping.                                                            *)
(*---------------------------------------------------------------------------*)

  type proof_content =
  | Prefl of term
  | Ptrans of int * int
  | Pmkcomb of int * int
  | Pabs of int * term
  | Pbeta of term
  | Passume of term
  | Peqmp of int * int
  | Pdeduct of int * int
  | Pinst of int * (term * term) list
  | Pinstt of int * (hol_type * hol_type) list
  | Paxiom of term
  | Pdef of term * string * hol_type
  | Pdeft of int * term * string * hol_type
  | Ptruth
  | Pconj of int * int
  | Pconjunct1 of int
  | Pconjunct2 of int
  | Pmp of int * int
  | Pdisch of term * int
  | Pspec of term * int
  | Pgen of term * int
  | Pexists of term * term * int
  | Pchoose of term * int * int
  | Pdisj1 of term * int
  | Pdisj2 of term * int
  | Pdisj_cases of int * int * int
  | Psym of int

  type proof = Proof of (thm * proof_content)

  let content_of (Proof(_,c)) = c
  let change_content p c = let Proof(th,_) = p in Proof(th,c)

  let thm_index = ref (-1)
  (*REMOVE
  let oc_dump = open_out_bin dump_filename

  let new_theorem hyps concl proof_content =
    let k = !thm_index + 1 in
    thm_index := k;
    let thm = Sequent(hyps, concl, k) in
    output_value oc_dump (Proof(thm,proof_content));
    thm
  ;;
  REMOVE*)
(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type and the function space            *)
(* constructor. Later on we add as primitive the type of individuals.        *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist ((o) union tyvars) args []
        | (Tyvar v as tv) -> [tv]

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty

  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)

  let the_term_constants =
     ref ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])]

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false

(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when Stdlib.compare ty (type_of a) = 0
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)

  let freesl tml = itlist ((o) union frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | _ -> Stdlib.compare tm v = 0

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)

  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Stdlib.compare (type_of t) y = 0
                        | _ -> false) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Stdlib.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

  let rec ordav env x1 x2 =
    match env with
      [] -> Stdlib.compare x1 x2
    | (t1,t2)::oenv -> if Stdlib.compare x1 t1 = 0
                       then if Stdlib.compare x2 t2 = 0
                            then 0 else -1
                       else if Stdlib.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Stdlib.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Stdlib.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c,_)) = (asl,c)

  let hyp (Sequent(asl,c,_)) = asl

  let concl (Sequent(asl,c,_)) = c

  let index_of (Sequent(_,_,k)) = k

(*REMOVE
(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm = new_theorem [] (safe_mk_eq tm tm) (Prefl tm)

  let TRANS (Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 ->
          new_theorem (term_union asl1 asl2) (Comb(eql,r)) (Ptrans(k1,k2))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1,k1),Sequent(asl2,c2,k2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Stdlib.compare ty (type_of r2) = 0
             -> new_theorem (term_union asl1 asl2)
                  (safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2))) (Pmkcomb(k1,k2))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c,p)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
        -> new_theorem asl (safe_mk_eq (Abs(v,l)) (Abs(v,r))) (Pabs(p,v))
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Stdlib.compare arg v = 0
        -> new_theorem [] (safe_mk_eq tm bod) (Pbeta tm)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Stdlib.compare (type_of tm) bool_ty = 0 then
      new_theorem [tm] tm (Passume tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq,k1)) (Sequent(asl2,c,k2)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> new_theorem (term_union asl1 asl2) r (Peqmp(k1,k2))
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    new_theorem (term_union asl1' asl2') (safe_mk_eq c1 c2) (Pdeduct(k1,k2))

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c,k) as th) = if theta = [] then th else
    let inst_fn = inst theta in
    new_theorem (term_image inst_fn asl) (inst_fn c) (Pinstt(k,theta))

  let INST theta (Sequent(asl,c,k) as th) = if theta = [] then th else
    let inst_fun = vsubst theta in
    new_theorem (term_image inst_fun asl) (inst_fun c) (Pinst(k,theta))

(* ------------------------------------------------------------------------- *)
(* Natural deduction rules.                                                  *)
(* ------------------------------------------------------------------------- *)

  let arrow b1 b2 = Tyapp("fun",[b1;b2]);;
  let conj_ty = arrow bool_ty (arrow bool_ty bool_ty);;
  let all_ty b = arrow (arrow b bool_ty) bool_ty;;

  let cst_imp = Const("==>",conj_ty);;
  let cst_conj = Const("/\\",conj_ty);;
  let cst_all b = Const("!",all_ty b);;
  let cst_ex b = Const("?",all_ty b);;
  let cst_disj = Const("\\/",conj_ty);;

  let head_args =
    let rec aux acc t =
      match t with
      | Comb(t1,t2) -> aux (t2::acc) t1
      | _ -> t, acc
    in aux []
  ;;

  let TRUTH = new_theorem [] (Const("T",bool_ty)) Ptruth;;

  let CONJ (Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) =
    let c = Comb(Comb(cst_conj,c1),c2) in
    new_theorem (term_union asl1 asl2) c (Pconj(k1,k2))
  ;;

  let CONJUNCT1 (Sequent(asl,c,k)) =
    match head_args c with
    | Const("/\\",_), [c1;_] -> new_theorem asl c1 (Pconjunct1 k)
    | _ -> failwith "CONJ_ELIM1"
  ;;

  let CONJUNCT2 (Sequent(asl,c,k)) =
    match head_args c with
    | Const("/\\",_), [_;c2] -> new_theorem asl c2 (Pconjunct2 k)
    | _ -> failwith "CONJ_ELIM2"
  ;;

  let MP (Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) =
    match head_args c1 with
    | Const("==>",_), [_;c] ->
      new_theorem (term_union asl1 asl2) c (Pmp(k1,k2))
    | _ -> failwith "MP"
  ;;

  let DISCH a (Sequent(asl,c,k)) =
    let asl = List.filter (fun h -> alphaorder a h <> 0) asl in
    new_theorem asl (Comb(Comb(cst_imp,a),c)) (Pdisch(a,k))
  ;;

  let SPEC t (Sequent(asl,c,k)) =
    match c with
    | Comb(Const("!",Tyapp(_,[Tyapp(_,[b;_]);_])),p) when b = type_of t ->
      new_theorem asl (Comb(p,t)) (Pspec(t,k))
    | _ -> failwith "SPEC"
  ;;

  let GEN x (Sequent(asl,c,k)) =
    match x with
    | Var(_,b) when not(exists (vfree_in x) asl) ->
      new_theorem asl (Comb(cst_all b,Abs(x,c))) (Pgen(x,k))
    | _ -> failwith "GEN"
  ;;

  let EXISTS (e,t) (Sequent(asl,c,k)) =
    match e with
    | Comb(Const("?",_),(Abs(Var(_,b),_) as p)) ->
      new_theorem asl (Comb(cst_ex b,p)) (Pexists(p,t,k))
    | _ -> failwith "EXISTS"
  ;;

  let CHOOSE (v,Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) =
    match c1 with
    | Comb(Const("?",_),(Abs(bv,bod) as p)) ->
      let asl2 = term_remove (mk_comb(p,v)) asl2 in
      let asl2 = term_remove (vsubst [v,bv] bod) asl2 in
      new_theorem (term_union asl1 asl2) c2 (Pchoose(v,k1,k2))
    | _ -> failwith "CHOOSE"
  ;;

  let DISJ1 (Sequent(asl,c,k)) p =
    new_theorem asl (Comb(Comb(cst_disj,c),p)) (Pdisj1(p,k));;

  let DISJ2 p (Sequent(asl,c,k)) =
    new_theorem asl (Comb(Comb(cst_disj,p),c)) (Pdisj2(p,k));;

  let DISJ_CASES
    (Sequent(asl1,c1,k1)) (Sequent(asl2,c2,k2)) (Sequent(asl3,c3,k3)) =
    let l,r =
      match c1 with
      | Comb(Comb(_,l),r) -> l,r
      | _ -> failwith "DISJ_CASES"
    in
    let asl2 = term_remove l asl2 and asl3 = term_remove r asl3 in
    new_theorem (term_union asl1 (term_union asl2 asl3)) c2
      (Pdisj_cases(k1,k2,k3))
  ;;

  let ALPHA tm1 tm2 =
    if alphaorder tm1 tm2 = 0 then
      new_theorem [] (safe_mk_eq tm1 tm2) (Prefl tm1)
    else failwith "ALPHA";;

  let SYM (Sequent(asl,c,k)) =
    let (l,r) = dest_eq c in
    new_theorem asl (safe_mk_eq r l) (Psym k);;

  let BETA_CONV tm =
    match tm with
    | Comb(Abs(v,bod),arg) ->
      new_theorem [] (safe_mk_eq tm (vsubst [arg,v] bod)) (Pbeta tm)
    | _ -> failwith "BETA_CONV: Not a beta-redex";;
REMOVE*)
(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)
(*REMOVE
  let axioms() = !the_axioms

  let new_axiom tm =
    if Stdlib.compare (type_of tm) bool_ty = 0 then
      let th = new_theorem [] tm (Paxiom tm) in
      (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"
REMOVE*)
(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let the_definitions = ref ([]:thm list)
(*REMOVE
  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then
          failwith ("new_definition: term not closed: " ^
              (String.concat ", " (map (fun (Var (name,_)) -> name) (frees r))))
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
             let dtm = safe_mk_eq c r in
             let dth = new_theorem [] dtm (Pdef(dtm,cname,ty)) in
             (the_definitions := dth::(!the_definitions); dth)
    | Comb(Comb(Const("=",_),Const(cname,ty)),r) ->
      failwith ("new_basic_definition: '" ^ cname ^ "' is already defined")
    | _ -> failwith "new_basic_definition"
REMOVE*)
(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)
(*REMOVE
  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c,p)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let pred,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] pred) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term pred) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    let atm = safe_mk_eq (Comb(abs,mk_comb(rep,a))) a in
    let ath = new_theorem [] atm (Pdeft(p,atm,absname,absty)) in
    let rtm = safe_mk_eq (Comb(pred,r))
                           (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r) in
    let rth = new_theorem [] rtm (Pdeft(p,rtm,repname,repty)) in
    let _ = new_axiom atm in
    let _ = new_axiom rtm in
    (ath,rth)

(* ------------------------------------------------------------------------- *)
(* Function to dump types, constants and axioms.                             *)
(* ------------------------------------------------------------------------- *)

  let dump_nb_proofs filename =
    Printf.printf "generate %s ...\n%!" filename;
    let oc = open_out filename in
    let nb_proofs = !thm_index + 1 in
    output_value oc nb_proofs;
    close_out oc;
    Printf.printf "%d proof steps\n%!" nb_proofs
  ;;

  let dump_signature filename =
    Printf.printf "generate %s ...\n%!" filename;
    let oc = open_out filename in
    output_value oc (types());
    output_value oc (constants());
    output_value oc (axioms());
    output_value oc (definitions());
    close_out oc
  ;;
REMOVE*)
end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;

(*REMOVE*)end include M
