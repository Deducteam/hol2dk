(* Check correctness of the types of all mappings in Rocq *)
(* Adapted from lambdapi export -o sttcoq. *)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Export.Coq

(* Initialised to Export.Coq.erase in main.ml *)
let unused_mappings = ref StrSet.empty

(* Initialised to !rmap right after set_renaming in main.ml *)
let initial_rmap : string StrMap.t ref = ref StrMap.empty

let untouched_ident oc ({elt;_} : p_ident) = string oc elt

(* Export.Coq.term but for each identifier encountered, update unused_mappings.
   The other difference is that we assume use_notations = true, use_implicits = false*)
let rec term ?(implicits=true) oc t =
  (*if Logger.log_enabled() then
    log "pp %a" (*Pos.short t.pos*) Pretty.term t;*)
  match t.elt with
  | P_Meta _ -> wrn t.pos "TODO"; assert false
  | P_Patt _ -> wrn t.pos "TODO"; assert false
  | P_Expl _ -> wrn t.pos "TODO"; assert false
  | P_SLit _ -> wrn t.pos "TODO"; assert false
  | P_NLit _ -> wrn t.pos "TODO"; assert false
  | P_Type -> string oc "Type"
  | P_Wild -> char oc '_'
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
        (fun h ts _ builtin ->
          match builtin, ts with
          | (El|Prf), [u] -> term oc u ~implicits
          | (Arr|Imp), [u;v] -> arrow oc u v ~implicits
          | All, [_;{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}] -> prod oc xs u ~implicits
          | Ex, [_;{elt=P_Wrap({elt=P_Abst([x],u);_});_}] ->
              string oc "exists "; raw_params oc x ~implicits; string oc ", "; term oc u ~implicits
          | Eq, [_;u;v] -> paren oc u ~implicits; string oc " = "; paren oc v ~implicits
          | Or, [u;v] -> paren oc u ~implicits; string oc " \\/ "; paren oc v ~implicits
          | And, [u;v] ->  paren oc u ~implicits; string oc " /\\ "; paren oc v ~implicits
          | Not, [u] -> string oc "~ "; paren oc u ~implicits
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

(* Store the last unmapped object *)
type unmapped_def_kind =
| UMLem of string
| UMDef of string
let last_unmapped = ref (UMLem "")

(* List of unmapped axioms with their type *)
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
        let name = Option.get p_sym_nam.elt (StrMap.find_opt p_sym_nam.elt !initial_rmap)
        in 
        (* remove implicit arguments, as they cannot be parsed by tactics. with
           types have no implicit arguments in the first place and should not start
           with an @ (example: (list term) is a valid mapping for a type and won't work
           with an @ in front) *)
        let s = match p_sym_typ with
          | Some t when not (is_Set t) && not (String.starts_with ~prefix:"@" s) -> "@" ^ s
          | _ -> s
        in 
        begin match p_sym_arg, p_sym_typ with
          | [], Some t ->
            string oc ("check " ^ name ^ " (") ; string oc s ; string oc ") (" ;
            term oc t ~implicits:false ; string oc ").\n"
          |  _, Some t ->
            string oc ("check " ^ name ^ " (") ; string oc s ; string oc ") (forall" ;
            params_list oc p_sym_arg ~implicits:false ; string oc ", " ;
            term oc t ~implicits:false ; string oc ").\n"
          | _ -> wrn pos "Command not translated."
        end
      | None -> 
        begin match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
          | true, Some _, _, Some _ when List.exists is_lem p_sym_mod ->
            (* Do not translate lemmas to avoid nested proofs. *)
            (* Also, use the last unmapped object to catch definitions mapped without the
               definitional lemma or the converse *)
            (* Notice that, for lemmas, the condition s ^ "_def" <> ... is always true. *)
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
"Variant wrong : forall constrtype, constrtype -> Type -> Type :=
wrongC ctype c atype : wrong ctype c atype.

Variant inexistant : Type := inexistantC.

Tactic Notation \"check\" simple_intropattern(ident) uconstr(constr) uconstr(type) :=
  let temp := fresh in
  tryif assert_fails assert (temp := type)
  then idtac \"Type\" type \"of\" ident \"is not a correct Rocq type.\";
    idtac \"If this is not a numbered axiom and the error is not because of a previous mapping error, please report the error.\";
    try lazymatch goal with | _ := _ |- _ => fail | |- True => set (failwitness := true) end
  else
  tryif assert_fails assert (temp := constr)
  then idtac ident \"is not mapped to an existing object.\";
    idtac \"Try checking for a typo or adding a path or import.\";
    try lazymatch goal with |- True => generalize inexistantC as ident end
  else
  tryif assert_succeeds assert (temp := (constr : type))
  then idtac
  else
  match type of constr with ?T =>
    idtac \"Incorrect mapping:\" ;
    idtac ident \"is mapped to\" constr \"of type\" T ;
    idtac \"while it is expected to have type\" type ;
    try lazymatch goal with |- True => generalize (wrongC T constr type) as ident end end.

Ltac conclusion := lazymatch goal with
| |- forall ident : wrong ?ctype ?c ?atype, _ =>
     idtac \"the first error was:\" ;
     idtac ident \"is mapped to\" c \"of type\" ctype ;
     idtac \"while it it is expected to have type\" atype
| |- forall ident : inexistant, _ =>
     idtac \"the first error was:\" ;
     idtac ident \"is not mapped to an existing object.\" ;
     idtac \"Try checking for a typo or adding a path or import\"
| failwitness := _ |- True =>
     idtac \"There is a problem, as only (an) incorrect type error(s) occurred.\" ;
     idtac \"Please investigate, and report if abnormal.\"
| |- _ => idtac \"All checks passed, all mapped objects are correctly typed.\" end.

Goal True.\n"

(* the $(BASE) library name *)
let base = ref ""

(* the $(REQUIRING) files to import *)
let requiring = ref ""

let lpfile name = !base ^ "_" ^ name ^ ".lp"

(* read all lp files in a list *)
let chainread oc = List.iter (fun name -> ast oc (Parser.parse_file (lpfile name)))

(* Error printing for an unmapped axiom *)
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
  list string " " oc l ; string oc ("\".\nidtac \"think about looking in renamings.lp " ^
    "for names that differ between HOL Light and rocq\".\nAbort."))
  
let generate_check_file () =
  let outputfile = !base ^ "_checkmappings.v" in
  let check_file = Out_channel.open_text outputfile
  in generate_check_file_in check_file ; Out_channel.close check_file