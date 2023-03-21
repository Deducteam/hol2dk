open Xprelude;;
open Xlib;;

(* [files()] computes the list of HOL-Light files in the current
   directory and its subdirectories recursively. *)
let files() : string list =
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

(* [dep_graph files] computes the dependency graph of [files]. *)
let dep_graph =
  let re =
    Str.regexp "^\\(load[st]\\|needs\\|#use\\)[ \t]+\"\\([^.]+.[mh]l\\)\"" in
  let search content =
    let rec search acc start =
      try
        let _ = Str.search_forward re content start in
        search (Str.matched_group 2 content :: acc) (Str.match_end())
      with _ -> acc
    in search [] 0
  in
  fun (files : string list) : string list MapStr.t ->
  List.fold_left
    (fun map filename ->
      MapStr.add filename (search (string_of_file filename)) map)
    MapStr.empty files
;;

(* [out_dep_graph oc dg] prints on [oc] the dependency graph [dg] in
   the Makefile format. *)
let out_dep_graph oc dg =
  MapStr.iter
    (fun name deps -> out oc "%s:%a\n" name (list_prefix " " string) deps)
    dg;
;;

(* [deps dg f] returns the immediate dependencies of [f] in [dg]. *)
let deps dg filename = try MapStr.find filename dg with Not_found -> [];;

(* [trans_deps dg f] returns all the dependencies of [f] in [dg],
   recursively. *)
let trans_deps dg filename =
  let rec trans visited to_visit =
    match to_visit with
    | [] -> visited
    | f::to_visit ->
       if List.mem f visited then trans visited to_visit
       else trans (f::visited) (deps dg f @ to_visit)
  in trans [] [filename]
;;

(* [thms_of_file f] computes the list of named theorems in [f]. *)
let thms_of_file =
  let search_1 =
    let re =
      Str.regexp
        ("\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
         ^"=[ \n\t]*"
         ^"\\(prove\\|"
         ^"prove_by_refinement\\|"
         ^"new_definition\\|"
         ^"new_basic_definition\\|"
         ^"new_axiom\\|"
         ^"new_infix_definition\\|"
         ^"INT_OF_REAL_THM\\|"
         ^"define_finite_type\\|"
         ^"TAUT\\|"
         ^"INT_ARITH\\|"
         ^"new_recursive_definition\\)")
    in
    fun content ->
    let rec search acc start =
      try
        let _ = Str.search_forward re content start in
        let matches = [Str.matched_group 2 content] in
        search (matches @ acc) (Str.match_end())
      with e -> (acc)
    in
    search [] 0
  in
  let search_2 =
    let re =
      Str.regexp
        ("\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
         ^"=[ \n\t]*"
         ^"\\(define_type\\|"
         ^"(CONJ_PAIR o prove)\\)")
    in
    fun content ->
    let rec search acc start =
      try
        let _ = Str.search_forward re content start in
        let matches =
          [Str.matched_group 2 content
          ;Str.matched_group 3 content] in
        search (matches @ acc) (Str.match_end())
      with e -> acc
    in search [] 0
  in
  let search_3 =
    let re =
      Str.regexp
        ("\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_-]+\\)[ \n\t]*"
         ^"=[ \n\t]*"
         ^"\\(new_inductive_definition\\)")
    in
    fun content ->
    let rec search acc start =
      try
        let _ = Str.search_forward re content start in
        let matches =
          [Str.matched_group 2 content
          ;Str.matched_group 3 content
          ;Str.matched_group 4 content]
        in
        search (matches @ acc) (Str.match_end())
      with e -> acc
    in search [] 0
  in
  fun f -> let s = string_of_file f in search_1 s @ search_2 s @ search_3 s
;;
