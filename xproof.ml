(****************************************************************************)
(* Accessing proofs from their indexes. *)
(****************************************************************************)

open Fusion
open Xlib
open Xprelude

let ic_prf : in_channel ref = ref stdin;;
let prf_pos : int array ref = ref [||];;
let nb_proofs() = Array.length !prf_pos;;

(* [proof_at k] returns the proof of index [k]. *)
let proof_at k =
  let ic = !ic_prf in
  seek_in ic (Array.get !prf_pos k);
  input_value ic
;;

(* [iter_proofs f] runs [f k (proof_at k)] on all proof index [k] from
   0 to [nb_proofs() - 1]. *)
let iter_proofs (f : int -> proof -> unit) =
  let idx = ref 0 in
  try
    while !idx < Array.length !prf_pos do
      let k = !idx in
      f k (proof_at k);
      idx := k + 1
    done
  with Failure _ as e ->
    log "proof %d\n%!" !idx;
    raise e
;;

let thm_uses : int array ref = ref [||];;
let cur_part_max : int ref = ref (-1);;
