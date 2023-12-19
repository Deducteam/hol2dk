(****************************************************************************)
(* Accessing proofs from their indexes. *)
(****************************************************************************)

open Fusion
open Xlib
open Xprelude

(* [read_prf b f] runs [f] on every proof of [b.prf]. *)
let read_prf (b : string) (f : int -> proof -> unit) =
  let dump_file = b ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  let idx = ref 0 in
  try while true do f !idx (input_value ic); incr idx done
  with End_of_file -> close_in ic
;;

(* [!ic_prf] is the input channel used to read proofs. *)
let ic_prf : in_channel ref = ref stdin;;

let init_proof_reading b =
  let dump_file = b ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  ic_prf := open_in_bin dump_file

(* [!prf_pos] gives the position in [!ic_prf] of each proof. *)
let prf_pos : int array ref = ref [||];;
let start_pos : int ref = ref 0;;

let read_pos b =
  start_pos := read_val (b ^ ".stp");
  prf_pos := read_val (b ^ ".pos");;

let get_pos k = Array.get !prf_pos (k - !start_pos);;

(* [proof_at k] returns the proof of index [k]. Can be used after
   [read_pos] and [init_proof_reading] only. *)
let proof_at k = let ic = !ic_prf in seek_in ic (get_pos k); input_value ic;;

(* [!last_use.(i) = 0] if [i] is a named theorem, the highest theorem
   index using [i] if there is one, and -1 otherwise. *)
let last_use : int array ref = ref [||];;

let read_use b = last_use := read_val (b ^ ".use");;

(* [!cur_part_max] indicates the maximal index of the current part. *)
let cur_part_max : int ref = ref (-1);;

(* [iter_proofs_at f] runs [f k (proof_at k)] on all proof index [k]
   from 0 to [nb_proofs - 1] (including unused proofs), where
   [nb_proofs = Array.length !prf_pos]. Can be used after [read_pos]
   and [init_proof_reading] only. *)
let iter_proofs_at (f : int -> proof -> unit) =
  let idx = ref 0 in
  let nb_proofs = Array.length !prf_pos in
  try
    while !idx < nb_proofs do
      let k = !idx in
      f k (proof_at k);
      idx := k + 1
    done
  with Failure _ as e ->
    log "proof %d\n%!" !idx;
    raise e
;;
