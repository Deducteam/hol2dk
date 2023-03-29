(****************************************************************************)
(* Accessing proofs from their indexes. *)
(****************************************************************************)

open Fusion
open Xlib
open Xprelude

(* [read_prf basename f] runs [f] on every proof of [basename.prf]. *)
let read_prf (basename : string) (f : int -> proof -> unit) =
  let dump_file = basename ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  let idx = ref 0 in
  try while true do f !idx (input_value ic); incr idx done
  with End_of_file -> close_in ic
;;

let prf_pos : int array ref = ref [||];;

let read_pos basename =
  let dump_file = basename ^ ".pos" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  prf_pos := input_value ic;
  close_in ic

(* Can be used after [read_pos] only. *)
let nb_proofs() = Array.length !prf_pos;;

let ic_prf : in_channel ref = ref stdin;;

let init_proof_reading basename =
  let dump_file = basename ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  ic_prf := open_in_bin dump_file

(* [proof_at k] returns the proof of index [k]. Can be used after
   [read_pos] and [init_proof_reading] only. *)
let proof_at k =
  let ic = !ic_prf in
  seek_in ic (Array.get !prf_pos k);
  input_value ic
;;

(* [iter_proofs f] runs [f k (proof_at k)] on all proof index [k] from
   0 to [nb_proofs() - 1]. Can be used after [read_pos] and
   [init_proof_reading] only. *)
let iter_proofs_at (f : int -> proof -> unit) =
  let idx = ref 0 in
  let n = nb_proofs() in
  try
    while !idx < n do
      let k = !idx in
      f k (proof_at k);
      idx := k + 1
    done
  with Failure _ as e ->
    log "proof %d\n%!" !idx;
    raise e
;;

let thm_uses : int array ref = ref [||];;

let read_use basename = thm_uses := read_val (basename ^ ".use");;

let cur_part_max : int ref = ref (-1);;
