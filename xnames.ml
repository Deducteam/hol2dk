(****************************************************************************)
(* Compute the named theorems of each file, following ProofTrace/proofs.ml. *)
(****************************************************************************)

unset_jrh_lexer;;

let search_1 =
  let re =
    Str.regexp
      (String.concat ""
         ("\\(let\\|and\\)[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
          ::"=[ \n\t]*"
          ::"\\(prove\\|"
          ::"prove_by_refinement\\|"
          ::"new_definition\\|"
          ::"new_basic_definition\\|"
          ::"new_axiom\\|"
          ::"new_infix_definition\\|"
          ::"INT_OF_REAL_THM\\|"
          ::"define_finite_type\\|"
          ::"TAUT\\|"
          ::"INT_ARITH\\|"
          ::"new_recursive_definition\\)"
          ::[]))
  in fun content ->
  let rec search acc start =
    try
      let _ = Str.search_forward re content start in
      let matches = (Str.matched_group 2 content)::[] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let search_2 =
  let re =
    Str.regexp
      (String.concat ""
         ("\\(let\\|and\\)[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
          ::"=[ \n\t]*"
          ::"\\(define_type\\|"
          ::"(CONJ_PAIR o prove)\\)"
          ::[]))
  in fun content ->
  let rec search acc start =
    try
      let _ = Str.search_forward re content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let search_3 =
  let re =
    Str.regexp
      (String.concat ""
         ("\\(let\\|and\\)[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
          ::"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
          ::"=[ \n\t]*"
          ::"\\(new_inductive_definition\\)"
          ::[]))
  in fun content ->
  let rec search acc start =
    try
      let _ = Str.search_forward re content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    (Str.matched_group 4 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s
;;

let theorems_of_file f =
  let s = load_file f in search_1 s @ search_2 s @ search_3 s
;;

let files =
  log "compute list of files from %s ...\n%!" (Sys.getcwd());
  let rec walk acc = function
  | [] -> acc
  | dir::tail ->
     let contents = Array.to_list (Sys.readdir dir) in
     let dirs, files =
       List.fold_left
         (fun (dirs,files) f ->
           try
             if f <> "" && f.[0] = '.' then (dirs, files) else
             if Filename.check_suffix f ".ml"
                || Filename.check_suffix f ".hl" then
               let f = if dir = "." then f else Filename.concat dir f in
               (dirs, f::files)
             else
               (*FIXME:temporary hack to avoid following links*)
               if f = "_opam" then (dirs, files) else
               let f = if dir = "." then f else Filename.concat dir f in
               (*Unix.(match (stat f).st_kind with
               | S_DIR -> (f::dirs, files)
               | _ -> (dirs, files))*)
               if Sys.is_directory f then (f::dirs, files)
               else (dirs, files)
           with Sys_error _ -> (dirs, files))
         ([],[]) contents
     in
     walk (files @ acc) (dirs @ tail)
  in walk [] ["."]
;;

let update_map_file_thms() =
  log "compute theorem names in each file ...\n%!";
  map_file_thms :=
    List.fold_left
      (fun map f -> MapStr.add f (theorems_of_file f) map)
      MapStr.empty files
;;

let theorems_of_file fn = MapStr.find fn !map_file_thms;;

(****************************************************************************)
(* Compute the maps thm_id <-> name. *)
(****************************************************************************)

let eval code =
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed)

let idx = ref (-1);;

let cmd_set_idx name = Printf.sprintf "idx := index_of %s;;" name;;

let update_map_thm_id_name() =
  log "compute map theorem number -> theorem name ...\n%!";
  map_thm_id_name :=
    MapStr.fold
      (fun filename thm_names map ->
        List.fold_left
          (fun map name ->
            if name = "_" then map else
            let name = if name = "_FALSITY_" then name ^ "DEF" else name in
              (* to give a name to the theorem "_FALSITY_" different
                 from the constant "_FALSITY_". *)
            try eval (cmd_set_idx name); MapInt.add !idx name map
            with _ -> map)
          map thm_names)
      !map_file_thms MapInt.empty
;;

let print_map_thm_id_name() =
  MapInt.iter (fun k name -> log "%d %s\n" k name) !map_thm_id_name;;

let update_map_thm_name_id() =
  log "compute map theorem name -> theorem number ...\n%!";
  map_thm_name_id :=
    MapStr.fold
      (fun filename thm_names map ->
        List.fold_left
          (fun map name ->
            if name = "_" then map else
            let name = if name = "_FALSITY_" then name ^ "DEF" else name in
              (* to give a name to the theorem "_FALSITY_" different
                 from the constant "_FALSITY_". *)
            try
              eval (cmd_set_idx name);
              let n = (*filename ^ "." ^*) name in
              let f = function
                | None -> Some !idx
                | Some _ -> assert false
              in
              MapStr.update n f map
            with _ -> map)
          map thm_names)
      !map_file_thms MapStr.empty
;;

let print_map_thm_name_id() =
  MapStr.iter (fun name k -> log "%s %d\n" name k) !map_thm_name_id;;

let thm_id name = MapStr.find name !map_thm_name_id;;

(****************************************************************************)
(* Compute the dependancy graph of HOL-Light files. *)
(****************************************************************************)

let search =
  let re =
    Str.regexp "^\\(load[st]\\|needs\\|#use\\)[ \t]+\"\\([^\.]+\.[mh]l\\)\"" in
  fun content ->
  let rec search acc start =
    try
      let _ = Str.search_forward re content start in
      search (Str.matched_group 2 content :: acc) (Str.match_end())
    with _ -> acc
  in search [] 0
;;

(* [update_map_file_deps()] computes the dependency graph of HOL-Light
   [files]. *)
let update_map_file_deps() =
  map_file_deps :=
    List.fold_left
      (fun map filename ->
        MapStr.add filename (search (load_file filename)) map)
      MapStr.empty files
;;

(* [out_map_file_deps oc] prints on [oc] the dependency graph in
   [map_file_deps] in a Makefile format. *)
let out_map_file_deps oc =
  MapStr.iter
    (fun name deps ->
      if deps <> [] then out oc "%s:%a\n" name (list_prefix " " string) deps)
    !map_file_deps;
;;

let print_map_file_deps() = out_map_file_deps stdout;;

let print_map_file_deps_to filename =
  let oc = open_out filename in
  out_map_file_deps oc;
  close_out oc
;;

(* [deps f] returns the list of filenames on while file [f] depends. *)
let deps filename =
  try MapStr.find filename !map_file_deps with Not_found -> []
;;

(* [trans_deps f] returns the list of filenames on while file [f]
   depends, and their dependencies recursively. *)
let trans_deps filename =
  let rec trans visited to_visit =
    match to_visit with
    | [] -> visited
    | f::to_visit ->
       if List.mem f visited then trans visited to_visit
       else trans (f::visited) (deps f @ to_visit)
  in trans [] [filename]
;;

set_jrh_lexer;;
