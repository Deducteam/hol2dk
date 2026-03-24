open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Export.Coq

(* true to translate with a big class, false to translate with a big module type *)
let to_classes = ref true
(* The name chosen for the current library *)
let libname = ref ""
(* The name of the HOL Light file being translated *)
let originalfilename = ref ""
(* True when writing file context.v*)
let context = ref false

let bind_params bound ((idos,_,_) : p_params) = List.fold_left (fun s ido ->
    Option.fold (fun s {elt;_} -> StrSet.add elt s) s ido
  ) bound idos

let rec term bound oc t =
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
      qident oc qid;
      if not (!context || StrSet.mem (snd qid.elt) bound)
      then string oc " Ctx"
  | P_Arro(u,v) -> arrow bound oc u v
  | P_Abst(xs,u) -> abst bound oc xs u
  | P_Prod(xs,u) -> prod bound oc xs u
  | P_LLet(x,xs,a,u,v) ->
    let newbound = StrSet.add x.elt bound in
    string oc "let "; ident oc x; let letbound = params_list bound oc xs in
    typopt letbound oc a; string oc " := "; term letbound oc u; string oc " in "; term newbound oc v
  | P_Wrap u -> term bound oc u
  | P_Appl _ ->
      let default h ts = head bound oc h ; char oc ' '; list (paren bound) " " oc ts in
      app t default
        (fun h ts expl builtin ->
          match !use_notations, !use_implicits && not expl, builtin, ts with
          | _, _, (El|Prf), [u] -> term bound oc u
          | _, _, (Arr|Imp), [u;v] -> arrow bound oc u v
          | _ -> default h ts)

and arrow bound oc u v = paren bound oc u ; string oc " -> "; term bound oc v
and abst bound oc xs u =
  string oc "fun"; let newbound = params_list_in_abs bound oc xs in
  string oc " => "; term newbound oc u
and prod bound oc xs u  =
  string oc "forall"; let newbound = params_list_in_abs bound oc xs in
  string oc ", "; term newbound oc u

and head bound oc t = match t.elt with
  | P_Iden _ -> term bound oc t
  | _ -> paren bound oc t
and paren bound oc t =
  let default() = char oc '('; term bound oc t; char oc ')' in
  match t.elt with
  | P_Arro _ | P_Abst _ | P_Prod _ | P_LLet _ | P_Wrap _ -> default()
  | P_Appl _ ->
      app t (fun _ _ -> default())
        (fun _ ts _ builtin ->
          match builtin, ts with
          | (El|Prf), [u] -> paren bound oc u
          | _ -> default())
  | P_Iden (qid,_) when not (!context || StrSet.mem (snd qid.elt) bound) -> default()
  | _ -> term bound oc t

and raw_params bound oc (ids,t,_) = param_ids oc ids; typopt bound oc t

and params bound oc ((ids,t,b) as x) =
  match b, t with
  | true, _ -> char oc '{'; raw_params bound oc x; char oc '}'
  | false, Some _ -> char oc '('; raw_params bound oc x; char oc ')'
  | false, None -> param_ids oc ids

(* starts with a space if the list is not empty *)
and params_list bound oc = List.fold_left (
    fun s x -> prefix " " (params s) oc x ; bind_params s x
  ) bound


(* starts with a space if the list is not empty *)
and params_list_in_abs bound oc l =
  match l with
  | [(ids,t,false) as x] -> char oc ' '; param_ids oc ids; typopt bound oc t;
    bind_params bound x
  | _ -> params_list bound oc l

(* starts with a space if <> None *)
and typopt bound oc t = Option.iter (prefix " : " (term bound) oc) t

let rec allowedpath p = match p with
  | [] -> false
  | [mdl] -> mdl <> "theory_hol" && not (List.mem mdl
    (List.map (String.cat !originalfilename) ["_terms" ; "_axioms" ; "_opam" ; "_types"]))
  | _::rest -> allowedpath rest

let first_symbol = ref true
let modules : p_path list ref = ref []

let imports prefix oc paths =
  let updatedpaths = List.filter (function {elt;_} -> allowedpath elt) paths
  in if not (List.is_empty updatedpaths)
  then (modules := !modules @ updatedpaths; string oc (prefix ^ " ") ;
    list path " " oc updatedpaths ; string oc ".\n")

let symbol_command symbolfun (oc : out_channel) {elt;pos} = match elt with
  | P_symbol { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
    p_sym_trm; p_sym_prf; p_sym_def } ->
    if not (StrSet.mem p_sym_nam.elt !erase) then (
      let p_sym_arg =
        let pos = None in
        (* Parameters with no type are assumed to be of type [Set]. *)
        let _Set = {elt=P_Iden({elt=sym Set;pos},false);pos} in
        List.map (function ids, None, b -> ids, Some _Set, b | x -> x) p_sym_arg
      in symbolfun oc {p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
        p_sym_trm;p_sym_prf;p_sym_def} pos
    )
  | _ -> ()

let command header symbol oc {elt; pos} =
  begin match elt with
  | P_open(true,ps) ->
      imports "Import" oc ps
  | P_open(false,ps) ->
      imports "Export" oc ps
  | P_require (None, ps) ->
      imports "Require" oc ps
  | P_require (Some true, ps) ->
      imports "Require Import" oc ps
  | P_require (Some false, ps) ->
      imports "Require Export)" oc ps
  | P_require_as (p,i) ->
    if allowedpath p.elt
    then (string oc "Module "; ident oc i; string oc " := "; path oc p;
          string oc ".\n")
  | P_symbol _ ->
      if !first_symbol then (first_symbol := false ; header oc !modules);
      symbol_command symbol oc {elt;pos}
  | _ -> wrn pos "Command not translated."
  end

let symbol_default oc
  { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ; p_sym_trm; p_sym_prf=_; p_sym_def } pos =
  let bound = !erase in
  let p_sym_arg = if !to_classes
    then ([Some {elt="Ctx";pos=None}],Some {elt=P_Iden({elt=([],"HOL_Light_Theory");pos=None},false);pos=None},false):: p_sym_arg
    else p_sym_arg
  in
    match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
    | true, Some t, _, Some a when List.exists is_lem p_sym_mod ->
      string oc "Lemma "; ident oc p_sym_nam ; let newbound = params_list bound oc p_sym_arg in
      string oc " : "; term newbound oc a; string oc ".\nProof. exact (";
      term newbound oc t; string oc "). Qed.\n"
    | true, Some t, _, _ ->
      string oc "Definition "; ident oc p_sym_nam;
      let newbound = params_list bound oc p_sym_arg in typopt newbound oc p_sym_typ;
      string oc " := "; term newbound oc t;
      if List.exists is_opaq p_sym_mod then
        (string oc ".\nOpaque "; ident oc p_sym_nam);
      string oc ".\n"
    | false, _, _, Some t ->
      string oc "Axiom "; ident oc p_sym_nam; string oc " : forall";
      let newbound = params_list bound oc p_sym_arg in string oc ", "; term newbound oc t;
      string oc ".\n"
    | _ -> wrn pos "Command not translated." 

let symbol_decl prefix suffix oc {p_sym_nam; p_sym_arg; p_sym_typ; _} pos =
  (* symbol_decl is only used for deriving context.v, in which there is no need for
     dealing with explicit arguments, so no need to remember bound identifiers *)
  let bound = StrSet.empty in
  match p_sym_arg, p_sym_typ with
  | [], Some t ->
    string oc prefix; ident oc p_sym_nam; string oc " : ";
    term bound oc t; string oc suffix
  | _, Some t ->
    string oc prefix; ident oc p_sym_nam; string oc " : forall";
    let _ = params_list bound oc p_sym_arg in string oc ", "; term bound oc t;
    string oc suffix
  | _, _ -> wrn pos "Command not translated."

let includemodule oc mdl =
  string oc ("Module Import " ^ snd (List.split_last mdl.elt) ^ "_copy := ");
  path oc mdl; string oc ".content(HOL_Light_Context).\n"

let regular_file_header oc modules =
  if not !to_classes
  then (
    string oc "Module content (HOL_Light_Context : HOL_Light_Theory).\n";
    string oc "Import HOL_Light_Context.\n";
    list includemodule "" oc modules
  )

let context_header oc (_ : string list loc list) =
  string oc (if !to_classes
    then "Record HOL_Light_Theory := {\n"
    else "Module Type HOL_Light_Theory.\n"
  )

let get_context() =
  context := true;
  let oc = stdout in
  string oc ("Require Export " ^ !libname ^ ".HOL_Light.\n");
  let (prefix,suffix) = if !to_classes then ("  "," ;\n") else ("Parameter ",".\n") in
  let andthen name =
    let filename = !originalfilename ^ "_" ^ name ^ ".lp" in
    let ast = Parser.parse_file filename in
    Stream.iter (symbol_command (symbol_decl prefix suffix) oc) ast
  in
    let ast = Parser.parse_file ("theory_hol.lp") in
    Stream.iter (command context_header (symbol_decl prefix suffix) oc) ast;
    andthen "types"; andthen "terms"; andthen "axioms";
    string oc (if !to_classes
      then "}."
      else "End HOL_Light_Theory."
    )

let translate file =
  erase := StrSet.add "HOL_Light_Theory" !erase;
  let oc = stdout in
  let ast = Parser.parse_file file in
  string oc ("Require Import " ^ !libname ^ ".context.\n");
  Stream.iter (command regular_file_header symbol_default oc) ast;
  if !first_symbol then regular_file_header oc !modules;
  if not !to_classes then string oc "End content."