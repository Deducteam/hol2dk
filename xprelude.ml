(****************************************************************************)
(* Definitions shared between all files for Dedukti/Lambdapi export. *)
(****************************************************************************)

(*REMOVE
unset_jrh_lexer;;
REMOVE*)

(* Remark: we use Printf since it is more efficient than Format. *)

(* [out oc s args] outputs [s] with [args] on out_channel [oc]. *)
let out = Printf.fprintf;;

(* [log oc s args] outputs [s] with [args] on stdout. *)
let log = Printf.printf;;

let log_gen s =
  print_string "generate "; print_string s; print_string " ...\n";
  flush stdout;;

let log_read s =
  print_string "read "; print_string s; print_string " ...\n";
  flush stdout;;

(* [err oc s args] outputs [s] with [args] on stderr. *)
let err = Printf.eprintf;;

(* [time_of p] executes [p:unit -> unit] and prints on stdout the time
   taken to execute [p]. *)
let time_of p =
  let t0 = Sys.time() in
  p();
  let t1 = Sys.time() in
  log "time: %f s\n" (t1 -. t0)
;;

(* [print_time()] prints on stout the time elapsed since the last call
   to [rpint_time()]. *)
let print_time =
  let t = ref (Sys.time()) in
  fun () ->
  let t' = Sys.time() in log "time: %f s\n" (t' -. !t); t := t'
;;

(* Maps on integers. *)
module OrdInt = struct type t = int let compare = (-) end;;
module MapInt = Map.Make(OrdInt);;
module SetInt = Set.Make(OrdInt);;

(* [map_thm_id_name] is used to hold the map from theorem numbers to
   theorem names. *)
let map_thm_id_name = ref (MapInt.empty : string MapInt.t);;

(* Maps and sets on strings. *)
module OrdStr = struct type t = string let compare = compare end;;
module MapStr = Map.Make(OrdStr);;
module SetStr = Set.Make(OrdStr);;

(* [map_thm_name_id] is used to hold the map from theorem names to
   theorem numbers. *)
let map_thm_name_id = ref (MapStr.empty : int MapStr.t);;

(* [map_const_typ_vars_pos] is used to hold a map from constant names
   to the positions of type variables in the types of the constants. *)
let map_const_typ_vars_pos = ref (MapStr.empty : int list list MapStr.t);;

(* [map_file_thms] is used to hold the map from file names to theorem
   names. *)
let map_file_thms = ref (MapStr.empty : string list MapStr.t);;

(* [map_file_deps] is used to hold the dependency graph of HOL-Light
   files, that is, the map from file names to their dependencies. *)
let map_file_deps = ref (MapStr.empty : string list MapStr.t);;

(* indicates whether the constant "el" has been added. *)
(*let el_added = ref false;;*)

(* indicates whether type and term abbreviations should be used. *)
let use_abbrev = ref true;;

(*REMOVE
set_jrh_lexer;;
REMOVE*)
