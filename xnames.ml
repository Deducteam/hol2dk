(* Compute the map thm_id -> name. *)

(*REMOVE*)open Xprelude;;
(*REMOVE*)open Xlib;;

(*REMOVE
unset_jrh_lexer;;

module OrdInt = struct type t = int let compare = (-) end;;
module MapInt = Map.Make(OrdInt);;

(* [string_of_file f] puts the contents of file [f] in a string. *)
let string_of_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s
;;
REMOVE*)

(* [eval code] evaluates [code] in the OCaml toplevel. *)
let eval (code : string) : unit =
  () (*REMOVE
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed)
  REMOVE*)

(* [map_thid_name tnames] get the index of every theorem which name is
   in [tnames] and build a map associating its name to each theorem
   index. *)
let map_thid_name =
  let idx = ref (-1) in
  (* OCaml code for setting [idx] to the index of theorem [name]. *)
  let cmd_set_idx = Printf.sprintf "idx := index_of %s;;" in
  List.fold_left
    (fun map tname ->
      if tname = "_" then map else
      try eval (cmd_set_idx tname); MapInt.add !idx tname map
      with _ -> map)
    MapInt.empty
;;

(* [thms_of_file f] computes the list of named theorems in [f]. *)
let thms_of_file =
  let search_1 =
    let re =
      Str.regexp
        ("^\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*"
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
        ("^\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*"
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
        ("^\\(let\\|and\\)[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*"
         ^"\\([a-zA-Z0-9_]+\\)[ \n\t]*"
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

let dump_map_thid_name ofile ifiles =
  let oc = open_out_bin ofile in
  output_value oc (map_thid_name (List.concat_map thms_of_file ifiles));
  close_out oc
;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
