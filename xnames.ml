(* Compute the map thm_id -> name. *)

(*REMOVE
unset_jrh_lexer;;
REMOVE*)

(*REMOVE*)open Xprelude;;
(*REMOVE*)open Xlib;;

let eval (code : string) : unit =
  () (*REMOVE
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed)
  REMOVE*)

let idx = ref (-1);;

let cmd_set_idx name = Printf.sprintf "idx := index_of %s;;" name;;

let map_thid_name tnames =
  List.fold_left
    (fun map tname ->
      if tname = "_" then map
      else
        try eval (cmd_set_idx tname); MapInt.add !idx tname map
        with _ -> map)
    MapInt.empty tnames
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

let dump_map_thid_name ifile ofile =
  let oc = open_out_bin ofile in
  output_value oc (map_thid_name (thms_of_file ifile));
  close_out oc
;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
