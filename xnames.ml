(* Compute the map thm_id -> name. *)

(*REMOVE*)open Xprelude;;
(*REMOVE*)open Xlib;;

(*REMOVE
unset_jrh_lexer;;

module OrdInt = struct type t = int let compare = (-) end;;
module MapInt = Map.Make(OrdInt);;

(* [string_of_file f] puts the contents of file [f] in a string. *)
let string_of_file f =
  let ic = Stdlib.open_in f in
  let n = Stdlib.in_channel_length ic in
  let s = Bytes.create n in
  Stdlib.really_input ic s 0 n;
  Stdlib.close_in ic;
  Bytes.to_string s
;;
REMOVE*)

(* [thms_of_file f] computes the list of named theorems in [f]. *)
let thms_of_string content =
  let search1 =
    let re =
      Str.regexp
        "^\\(let\\|and\\)[ \n\t]+\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*\
         =[ \n\t]*\
         \\(prove\\|\
         prove_by_refinement\\|\
         new_definition\\|\
         new_basic_definition\\|\
         new_axiom\\|\
         new_infix_definition\\|\
         INT_OF_REAL_THM\\|\
         define_finite_type\\|\
         TAUT\\|\
         INT_ARITH\\|\
         new_recursive_definition\\)"
    in
    let rec search start acc =
      try
        let _ = Str.search_forward re content start in
        search (Str.match_end()) (Str.matched_group 2 content :: acc)
      with _ -> acc
    in
    search 0
  in
  let search2 =
    let re =
      Str.regexp
        "^\\(let\\|and\\)[ \n\t]+\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*\
         =[ \n\t]*\
         \\(define_type\\|\
         (CONJ_PAIR o prove)\\)"
    in
    let rec search start acc =
      try
        let _ = Str.search_forward re content start in
        search (Str.match_end())
          (Str.matched_group 2 content :: Str.matched_group 3 content :: acc)
      with _ -> acc
    in search 0
  in
  let search3 =
    let re =
      Str.regexp
        "^\\(let\\|and\\)[ \n\t]+\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*,[ \n\t]*\
         \\([a-zA-Z0-9_]+\\)[ \n\t]*\
         =[ \n\t]*\
         \\(new_inductive_definition\\)"
    in
    let rec search start acc =
      try
        let _ = Str.search_forward re content start in
        search (Str.match_end())
          (Str.matched_group 2 content :: Str.matched_group 3 content
           :: Str.matched_group 4 content :: acc)
      with _ -> acc
    in search 0
  in
  let search4 =
    let re_list = Str.regexp "^let[ \n\t]+\\[\\([A-Z0-9_]+\\)[ \n\t]*"
    and re_elt = Str.regexp ";[ \n\t]*\\([A-Z0-9_]+\\)[ \n\t]*" in
    let rec search_list start acc =
      try
        let _ = Str.search_forward re_list content start in
        (*log "search_list %d %s\n" start (Str.matched_group 1 content);*)
        search_elt (Str.match_end()) (Str.matched_group 1 content :: acc)
      with _ -> acc
    and search_elt start acc =
      (*let n = min 40 (String.length content - start) in
      log "search_elt <- %s...\n" (String.sub content start n);*)
      match content.[start] with
      | ';' ->
         let _ = Str.search_forward re_elt content start in
         (*log "search_elt -> %d %s\n" start (Str.matched_group 1 content);*)
         search_elt (Str.match_end()) (Str.matched_group 1 content :: acc)
      | ']' ->
         search_list (Str.match_end()) acc
      | _ -> assert false
    in
    search_list 0
  in
  search4 (search3 (search2 (search1 [])))
;;

let thms_of_file f = thms_of_string (string_of_file f);;

(* [eval code] evaluates [code] in the OCaml toplevel. *)
let [@warning "-27"] eval (code : string) : unit =
  () (*REMOVE
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  Stdlib.ignore (Toploop.execute_phrase true Format.std_formatter parsed)
  REMOVE*)

(* Top-level reference to compute index of named theorems. Must be
   kept at the toplevel to work. *)
let idx = Stdlib.ref (-1);;

(* [map_thid_name tnames] get the index of every theorem which name is
   in [tnames] and build a map associating its name to each theorem
   index. *)
let map_thid_name =
  List.fold_left
    (fun map tname ->
      try eval ("idx := index_of "^tname^";;"); MapInt.add !idx tname map
      with _ -> Printf.printf "%s not found\n" tname; map)
    MapInt.empty
;;

let dump_map_thid_name ofile ifiles =
  let map = map_thid_name (List.concat_map thms_of_file ifiles) in
  (*MapInt.iter (Printf.printf "%d %s\n") map;*)
  Printf.printf "%d named theorems\n" (MapInt.cardinal map);
  let oc = Stdlib.open_out_bin ofile in
  Stdlib.output_value oc map;
  Stdlib.close_out oc
;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
