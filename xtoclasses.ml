let theoryfile = ref ""
let outputpath = "output/"
let originalfilename = ref ""
let file name = outputpath ^ !originalfilename ^ "_" ^ name ^ ".v"
let read_file name = In_channel.open_text (file name)

let str_to_list s = List.init (String.length s) (String.get s)
let str_of_list l = List.fold_left String.cat "" (List.map (String.make 1) l)

(* a list of functions that should still be used with @ *)
let at_exceptions = List.map str_to_list
  [ "all" ; "ex" ; "ex1" ; "ε" ; "COND" ; "REP_prod" ; "ABS_prod" ;
  "pair" ; "mk_pair" ; "fst" ; "snd" ; "ONTO" ; "ONE_ONE" ; "eq" ]
let clear_implicits s = let open String in
  let n = length s - 1 in
  if s.[0] = '{' then "(" ^ sub s 1 n else
  if s.[n] = '}' then sub s 0 n ^ ")" else
  if n!=0 && s.[n-1] = '}' then sub s 0 (n-1) ^ ")," else
  let rec remove_at l s0 = match l with
    | [] -> s0
    | '@'::l0 -> if List.mem l0 at_exceptions
      then s
      else (s0 ^ str_of_list l0)
    | c::l0 -> remove_at l0 (s0 ^ String.make 1 c)
  in remove_at (str_to_list s) ""

let read_line ic = Option.map
  (fun s -> List.map clear_implicits (String.split_on_char ' ' s))
  (In_channel.input_line ic)

let remake l = String.concat " " l

let write_line oc s = output_string oc (s ^ "\n")

let rewrite oc l = write_line oc (remake l)

let file_to_reverse_list ic =
  let rec file_to_reverse_list_rec ic l = match read_line ic with
    | Some s -> file_to_reverse_list_rec ic (s::l)
    | None -> In_channel.close ic ; l
  in
    file_to_reverse_list_rec ic []

let get_type expr =
  let rec get_type_rec list_of_file = match list_of_file with
    | ("Axiom"::name::l)::list_of_file' ->
      if List.mem name expr || List.mem (name ^ ".") expr
      then (name,l)
      else get_type_rec list_of_file'
    | _ -> raise Exit
  in
    get_type_rec (file_to_reverse_list (read_file "types"))

let get_axioms pat =
  let rec get_axioms_rec ic l =
    match read_line ic with
    | Some ("Require"::_) -> get_axioms_rec ic l
    | Some ("Axiom"::l') ->
      if List.exists (String.ends_with ~suffix:pat) l'
      then get_axioms_rec ic (l @ [l'])
      else get_axioms_rec ic l
    | None -> In_channel.close ic ; l
    | _ -> raise Exit
  in
    get_axioms_rec (read_file "axioms") []

let first_field = ref true

let create_object oc name type_container field_list =
  let write_field l =
    let rec until_type l = match l with
      | [s] -> [String.sub s 0 (String.length s -1)]
      | [] -> []
      | s0::l0 -> if s0 = ":=" then [] else s0::(until_type l0)
    in
      let prefix = if !first_field
        then (first_field := false ; "\n  ")
        else " ;\n  "
      in
        output_string oc (prefix ^ (remake (until_type l)))
  in
      List.iter write_field ((name::type_container)::field_list)

let translate_theory_to oc =
  let rec translate_opam_file ic oc =
    match read_line ic with
    | Some ("Require"::_) -> translate_opam_file ic oc
    | Some l -> rewrite oc l ; translate_opam_file ic oc
    | None -> Out_channel.output_string oc "End theory." ;
      In_channel.close ic ; Out_channel.close oc
  in 
    let rec translate_terms_file ic oc = 
      let nextline() = translate_terms_file ic oc
      in
        match read_line ic with
        | Some ("Require"::l) -> rewrite oc ("Require"::l) ;
          begin match read_line ic, read_line ic with
            |_ -> output_string oc "Class HOL_Light_theory := {" ; nextline()
          end
        | Some ("Proof."::_) -> nextline()
        | Some ("Definition"::name::l) -> 
          ( match read_line ic with
          | Some ("Lemma"::l') ->
            create_object oc name l [l'] ; nextline()
          | _ -> raise Exit )
        | Some ("Axiom"::proj::l) ->
          let name,l_type = get_type l in
          ( match read_line ic with
          | Some ("Axiom"::l') ->
            create_object oc name l_type ((proj::l)::l'::(get_axioms proj)) ;
            nextline()
          | _ -> raise Exit )
        | None -> In_channel.close ic ;
          output_string oc "\n}.\nSection theory.\nContext {HOL_Light_context : HOL_Light_theory}.\nExisting Instance HOL_Light_context.\n" ;
          translate_opam_file (read_file "opam") oc
        | Some l -> print_endline (remake l) ; raise Exit
      in translate_terms_file (read_file "terms") oc

let get_theory_file() = translate_theory_to (Out_channel.open_text (!theoryfile))