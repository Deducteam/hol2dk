(* Check correctness of the types of all mappings in Rocq *)
(* Adapted from lambdapi export -o sttcoq. *)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Export.Coq

let unused_mappings = ref !erase

let check_that_unused_mappings_is_not_empty() = if StrSet.is_empty !unused_mappings
  then print_string "Sadly, unused_mappings is empty."
  else print_string "unused_mappings is, indeed, non-empty" 
  

(** Set encoding. *)

let map_qid_builtin = ref QidMap.empty

let set_encoding : string -> unit = fun f ->
  let found = Array.make nb_builtins false in
  let consume = function
    | {elt=P_builtin(n,lp_qid);pos} ->
        begin match index_of_name n with
        | Some i ->
            if Logger.log_enabled() then
              log "builtin \"%s\" = %a" n Pretty.qident lp_qid;
            builtin.(i) <- lp_qid.elt;
            found.(i) <- true;
            let b = builtin_of_index i in
            map_qid_builtin := QidMap.add lp_qid.elt b !map_qid_builtin;
            if b = El || b = Prf then
              (if Logger.log_enabled() then log "erase %s" (snd lp_qid.elt);
               erase := StrSet.add (snd lp_qid.elt) !erase)
        | None -> fatal pos "Unknown builtin."
        end
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f);
  Array.iteri
    (fun i b ->
      if not b then
        let pos =
          Some {fname=Some f;start_line=0;start_col=0;end_line=0;end_col=0}
        in fatal pos "Builtin %s undefined." (name_of_index i))
    found

(** Basic printing functions. We use Printf for efficiency reasons. *)
let out = Printf.printf

let char = output_char
let string = output_string

let prefix pre elt oc x = string oc pre; elt oc x
let suffix elt suf oc x = elt oc x; string oc suf

let list elt sep oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs

(** Translation of identifiers. *)

let translate_ident : string -> string = fun s ->
  try StrMap.find s !rmap with Not_found -> s

let raw_ident oc s = string oc (translate_ident s)

let ident oc {elt;_} = raw_ident oc elt

let untouched_ident oc ({elt;_} : p_ident) = string oc elt

let param_id oc idopt =
  match idopt with
  | Some id -> ident oc id
  | None    -> char oc '_'

let param_ids = list param_id " "

let raw_path = list string "."

let path oc {elt;_} = raw_path oc elt

let qident oc {elt=(mp,s);_} =
  match mp with
  | [] -> raw_ident oc s
  | _::_ -> raw_path oc mp; char oc '.'; raw_ident oc s

(** Translation of terms. *)

let stt = Stdlib.ref true
let use_implicits = Stdlib.ref false
let use_notations = Stdlib.ref true

(* redefinition of p_get_args ignoring P_Wrap's. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args t acc =
    match t.elt with
    | P_Appl(t, u) -> p_get_args t (u::acc)
    | P_Wrap t -> p_get_args t acc
    | _ -> t, acc
  in p_get_args t []

let app t default cases =
  let h, ts = p_get_args t in
  if !stt then
    match h.elt with
    | P_Iden({elt;_},expl) ->
        begin match QidMap.find_opt elt !map_qid_builtin with
        | None -> default h ts
        | Some builtin -> cases h ts expl builtin
        end
    | _ -> default h ts
  else default h ts

let rec term ?(implicits=true) oc t =
  (*if Logger.log_enabled() then
    log "pp %a" (*Pos.short t.pos*) Pretty.term t;*)
  match t.elt with
  | P_Meta _ -> wrn t.pos "TODO"; assert false
  | P_Patt _ -> wrn t.pos "TODO"; assert false
  | P_Expl _ -> wrn t.pos "TODO"; assert false
  | P_SLit _ -> wrn t.pos "TODO"; assert false
  | P_Type -> string oc "Type"
  | P_Wild -> char oc '_'
  | P_NLit i ->
      if !stt then
        match QidMap.find_opt ([],i) !map_erased_qid_coq with
        | Some s -> unused_mappings := StrSet.remove i !unused_mappings;
          string oc s
        | None -> raw_ident oc i
      else raw_ident oc i
  | P_Iden(qid,b) ->
      if b then char oc '@';
      if !stt then
        match QidMap.find_opt qid.elt !map_erased_qid_coq with
        | Some s ->
          unused_mappings := StrSet.remove (snd qid.elt) !unused_mappings;
          string oc s
        | None -> qident oc qid
      else qident oc qid
  | P_Arro(u,v) -> arrow oc u v ~implicits
  | P_Abst(xs,u) -> abst oc xs u ~implicits
  | P_Prod(xs,u) -> prod oc xs u ~implicits
  | P_LLet(x,xs,a,u,v) ->
    string oc "let "; ident oc x; params_list oc xs ~implicits ; typopt oc a ~implicits ;
    string oc " := "; term oc u ~implicits ; string oc " in "; term oc v ~implicits
  | P_Wrap u -> term oc u ~implicits
  | P_Appl _ ->
      let default h ts = paren oc h ~implicits ; char oc ' '; list (paren ~implicits) " " oc ts in
      app t default
        (fun h ts expl builtin ->
          match !use_notations, !use_implicits && not expl, builtin, ts with
          | _, _, (El|Prf), [u] -> term oc u ~implicits
          | _, _, (Arr|Imp), [u;v] -> arrow oc u v ~implicits
          | _, _, All, [_;{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
          | _, true, All, [{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
            -> prod oc xs u ~implicits
          | _, _, Ex, [_;{elt=P_Wrap({elt=P_Abst([x],u);_});_}]
          | _, true, Ex, [{elt=P_Wrap({elt=P_Abst([x],u);_});_}] ->
              string oc "exists "; raw_params oc x ~implicits; string oc ", "; term oc u ~implicits
          | true, _, Eq, [_;u;v]
          | true, true, Eq, [u;v] -> paren oc u ~implicits; string oc " = "; paren oc v ~implicits
          | true, _, Or, [u;v] -> paren oc u ~implicits; string oc " \\/ "; paren oc v ~implicits
          | true, _, And, [u;v] ->  paren oc u ~implicits; string oc " /\\ "; paren oc v ~implicits
          | true, _, Not, [u] -> string oc "~ "; paren oc u ~implicits
          | _ -> default h ts)

and arrow ?(implicits=true) oc u v = paren oc u ~implicits ; string oc " -> "; term oc v ~implicits
and abst ?(implicits=true) oc xs u =
  string oc "fun"; params_list_in_abs oc xs ~implicits; string oc " => "; term oc u ~implicits
and prod ?(implicits=true) oc xs u =
  string oc "forall"; params_list_in_abs oc xs ~implicits; string oc ", "; term oc u ~implicits

and paren ?(implicits=true) oc t =
  let default() = char oc '('; term oc t ~implicits ; char oc ')' in
  match t.elt with
  | P_Arro _ | P_Abst _ | P_Prod _ | P_LLet _ | P_Wrap _ -> default()
  | P_Appl _ ->
      app t (fun _ _ -> default())
        (fun _ ts _ builtin ->
          match builtin, ts with
          | (El|Prf), [u] -> paren oc u ~implicits
          | _ -> default())
  | _ -> term oc t ~implicits

and raw_params ?(implicits=true) oc (ids,t,_) = param_ids oc ids; typopt oc t ~implicits

and params ?(implicits=true) oc ((ids,t,b) as x) =
  match b, t , implicits with
  | true, _ , true -> char oc '{'; raw_params oc x ~implicits; char oc '}'
  | _ , Some _ , _ -> char oc '('; raw_params oc x ~implicits; char oc ')'
  | _ , None , _ -> param_ids oc ids

(* starts with a space if the list is not empty *)
and params_list ?(implicits=true) oc l =
  List.iter (prefix " " (params ~implicits) oc) l

(* starts with a space if the list is not empty *)
and params_list_in_abs ?(implicits=true) oc l =
  match l with
  | [ids,t,false] -> char oc ' '; param_ids oc ids; typopt oc t ~implicits
  | _ -> params_list oc l ~implicits

(* starts with a space if <> None *)
and typopt ?(implicits=true) oc t = Option.iter (prefix " : " (term ~implicits) oc) t

(** Translation of commands. *)

let is_lem x = is_opaq x || is_priv x

type unmapped_def_kind =
| UMLem of string
| UMDef of string

let last_unmapped = ref (UMLem "")
let axlist : (string*p_term) list ref = ref []

(* Identify types, possibly parametrized *)
let rec is_Set t =
  match t.elt with
  | P_Iden (qid,_) -> qid.elt = sym Set
  | P_Prod (_,t) | P_Arro (_,t) -> is_Set t
  | _ -> false

(* mappings that have incorrect type but it's ok. *)
let ignore_mappings = ["fun_ext";"∧ᵢ"]

let command oc {elt; pos} =
  begin match elt with
  | P_open _ | P_require _ -> ()
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf=_; p_sym_def } ->
      let p_sym_arg =
        if !stt then
          let pos = None in
          (* Parameters with no type are assumed to be of type [Set]. *)
          let _Set = {elt=P_Iden({elt=sym Set;pos},false);pos} in
          List.map (function ids, None, b -> ids, Some _Set, b | x -> x)
            p_sym_arg
          else p_sym_arg
      in
      begin match QidMap.find_opt ([],p_sym_nam.elt) !map_erased_qid_coq with
(* Instead of erasing mapped terms, check their type *)
      | Some s ->
        unused_mappings := StrSet.remove p_sym_nam.elt !unused_mappings;
        if List.mem p_sym_nam.elt ignore_mappings
        then ()
        else
        let s = match p_sym_typ with
          | Some t when not (is_Set t) && not (String.starts_with ~prefix:"@" s) -> "@" ^ s
          | _ -> s
        in 
        begin match p_sym_arg, p_sym_typ with
          | [], Some t ->
            string oc "check \""; untouched_ident oc p_sym_nam; string oc "\" (" ;
            string oc s ; string oc ") (" ; term oc t ~implicits:false ; string oc ").\n"
          |  _, Some t ->
            string oc "check \""; untouched_ident oc p_sym_nam; string oc "\" (" ;
            string oc s ; string oc ") (forall" ; params_list oc p_sym_arg ~implicits:false ;
            string oc ", " ; term oc t ~implicits:false ; string oc ").\n"
          | _ -> wrn pos "Command not translated."
        end
      | None -> 
        begin match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
          | true, Some _, _, Some _ when List.exists is_lem p_sym_mod ->
            (* Do not translate lemmas to avoid nested proofs but still print them. *)
            begin match !last_unmapped with
            | UMLem s | UMDef s when s ^ "_def" <> p_sym_nam.elt ->
              string oc "idtac \"Error: " ; untouched_ident oc p_sym_nam ;
              string oc "was not mapped, yet the object it defines was.\".\n"
            | _ -> ()
            end ; last_unmapped := UMLem p_sym_nam.elt
          | true, Some t, _, _ ->
            begin match !last_unmapped with
            | UMDef s ->
              string oc "idtac \"Error: " ; string oc s ;
              string oc "was not mapped but its definitional Lemma was\".\n"
            | _ -> ()
            end ; last_unmapped := UMDef p_sym_nam.elt ;
            string oc "Definition "; ident oc p_sym_nam;
            params_list oc p_sym_arg; typopt oc p_sym_typ;
            string oc " := "; term oc t; string oc ".\n"
          | false, _, [], Some t ->
            let s = p_sym_nam.elt in
            if s = "El" || s = "Prf"
            then ()
            else (
            axlist := (s,t) :: !axlist ;
            string oc "Axiom "; ident oc p_sym_nam; string oc " : ";
            term oc t; string oc ".\n" )
          | false, _, _, Some t ->
            axlist := (p_sym_nam.elt,t) :: !axlist ;
            string oc "Axiom "; ident oc p_sym_nam; string oc " : forall";
            params_list oc p_sym_arg; string oc ", "; term oc t;
            string oc ".\n"
          | _ -> wrn pos "Command not translated."
          end
        end
  | _ -> ()
  end

let ast oc = Stream.iter (command oc)

(* Rocq code to print mapping errors. *)

let check_file_header =
"Variant error : forall constrtype, constrtype -> Type -> Type :=
obj ctype c atype : error ctype c atype.

Tactic Notation \"check\" string(ident) uconstr(constr) uconstr(type) :=
  let temp := fresh in
  tryif assert_fails assert (temp := type)
  then idtac \"Type\" type \"of\" ident \"is not a correct Rocq type.\";
    idtac \"If it is not because of a previous mapping error (in particular if it is the first error), please report the error.\" 
  else 
  tryif assert_fails assert (temp := constr)
  then idtac ident \"is not mapped to an existing object.\";
    idtac \"Try checking for a typo or adding a path.\"
  else
  tryif assert_succeeds assert (temp := (constr : type))
  then idtac
  else
  match type of constr with ?T =>
    idtac \"Incorrect mapping:\" ;
    idtac ident \"is mapped to\" constr \"of type\" T ;
    idtac \"while it is expected to have type\" type ;
    try lazymatch goal with |- True => generalize (obj T constr type) end end.

Ltac conclusion := match goal with
| |- error ?ctype ?c ?atype -> _ => idtac \"the first error was:\" ;
     idtac c \"has type\" ctype ;
     idtac \"while it it is expected to have type\" atype
| _ => idtac \"All checks passed, all mapped objects are correctly typed.\" end.

Goal True.\n"

let base = ref ""

let requiring = ref ""

let lpfile name = !base ^ "_" ^ name ^ ".lp"

let chainread oc = List.iter (fun name -> ast oc (Parser.parse_file (lpfile name)))

let outputfile = !base ^ "_checkmappings.v"

let unmappedaxiom oc (name,typ) = string oc (name ^ " of type ") ; term oc typ 

let generate_check_file_in oc =
  string oc ("Require Import " ^ !requiring ^ ".\n") ;
  string oc check_file_header ; ast oc (Parser.parse_file "theory_hol.lp") ;
  chainread oc ["types";"axioms";"terms"] ;
  string oc "conclusion.\n";
  begin match !axlist with
  | [] -> string oc "idtac \"All axioms are mapped.\".\n"
  | _ as l -> string oc "idtac \"Warning, the following axioms were not mapped:\n" ;
    list unmappedaxiom ",\n" oc l ; string oc ".\".\n"
  end ;
  let l = StrSet.elements !unused_mappings in
  if l = [] then string oc "idtac \"All mappings are used.\".\nAbort."
  else (string oc "idtac \"Warning, the following mappings were not used: ";
  list string " " oc l ; string oc "\".\nAbort.")
  
let generate_check_file () =
  let outputfile = !base ^ "_checkmappings.v" in
  let check_file = Out_channel.open_text outputfile
  in generate_check_file_in check_file ; Out_channel.close check_file