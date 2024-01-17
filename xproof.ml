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
  ic_prf := open_in_bin dump_file;;

(* [!the_start_idx] is the starting proof index of the current pos file. *)
let the_start_idx : int ref = ref 0;;

(* [(!prf_pos).(i)] gives the position in [!ic_prf] of the proof of
   index [!the_start_idx + i]. *)
let prf_pos : int array ref = ref [||];;

let read_pos b = prf_pos := read_val (b ^ ".pos");;

(* [!map_thid_pos] maps proof indexes to positions. *)
let map_thid_pos : (string * int) MapInt.t ref = ref MapInt.empty;;

let thdeps = ref SetStr.empty;;

let get_pos k =
  let k' = k - !the_start_idx in
  (*log "get_pos %d - %d = %d\n%!" k !the_start_idx k';*)
  if k' >= 0 then Array.get !prf_pos k'
  else
    try
      let n,p = MapInt.find k !map_thid_pos in
      thdeps := SetStr.add n !thdeps; p
    with Not_found ->
      log "theorem %d not found\n%!" k; raise Not_found
;;

(* [proof_at k] returns the proof of index [k]. Can be used after
   [read_pos] and [init_proof_reading] only. *)
let proof_at k =
  let ic = !ic_prf in
  let p = get_pos k in
  (*log "get_pos %d = %d\n%!" k p;*)
  seek_in ic p;
  input_value ic;;

(* [(!last_use).(i) = 0] if [i] is a named theorem, the highest
   theorem index using [i] if there is one, and -1 otherwise. *)
let last_use : int array ref = ref [||];;

let read_use b = last_use := read_val (b ^ ".use");;

let get_use k =
  let k' = k - !the_start_idx in
  (*log "get_use %d - %d = %d\n%!" k !the_start_idx k';*)
  Array.get !last_use k';;

(* [!cur_part_max] indicates the maximal index of the current part. *)
let cur_part_max : int ref = ref (-1);;
