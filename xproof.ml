(****************************************************************************)
(* Accessing proofs from their indexes. *)
(****************************************************************************)

open Fusion
open Xlib
open Xprelude

let ic_dump : in_channel ref = ref stdin;;
let pos_dump : int array ref = ref [||];;
let thm_uses : int array ref = ref [||];;
let thm_uses_max : int ref = ref (-1);;
let thm_uses_argmax : int ref = ref (-1);;
let rule_uses : int array = Array.make 25 0;;

let set_dump_file (filename : string) (n : int) : unit =
  let ic = open_in_bin filename in
  ic_dump := ic;
  pos_dump := Array.make n (-1);
  thm_uses :=  Array.make n 0
;;

let nb_proofs() : int = Array.length !pos_dump;;

(* [proof_at k] returns the proof of index [k]. *)
let proof_at k =
  let ic = !ic_dump in
  let pos = !pos_dump in
  let cur_pos = pos_in ic in
  let p = Array.get pos k in
  if p < 0 then
    (* proof not yet read *)
    begin
      Array.set pos k cur_pos;
      input_value ic
    end
  else
    (* proof already read *)
    begin
      seek_in ic p;
      let prf = input_value ic in
      seek_in ic cur_pos;
      prf
    end
;;

(* [iter_proofs f] runs [f k (proof_at k)] on all proof index [k] from
   0 to [nb_proofs() - 1]. *)
let iter_proofs (f : int -> proof -> unit) =
  let idx = ref 0 in
  try
    while !idx < Array.length !pos_dump do
      let k = !idx in
      f k (proof_at k);
      idx := k + 1
    done
  with Failure _ as e ->
    log "proof %d\n%!" !idx;
    raise e
;;

let count_thm_uses : proof -> unit =
  let use k =
    let n = Array.get !thm_uses k + 1 in
    Array.set !thm_uses k n;
    if n > !thm_uses_max then (thm_uses_max := n; thm_uses_argmax := k)
  in
  fun p -> List.iter use (deps p)
;;

let count_rule_uses (p : proof) : unit =
  let i = code_of_proof p in
  Array.set rule_uses i (Array.get rule_uses i + 1)
;;

(* Prints on stdout the number of theorems that are used i times, for
   each i from 0 to !thm_uses_max. *)
let print_thm_uses_histogram() : unit =
  let hist = Array.make (!thm_uses_max + 1) 0 in
  let f nb_uses = Array.set hist nb_uses (Array.get hist nb_uses + 1) in
  Array.iter f !thm_uses;
  log "(* \"i: n\" means that n proofs are used i times *)\n";
  let nonzeros = ref 0 in
  for i=0 to !thm_uses_max do
    let n = Array.get hist i in
    if n > 0 then (incr nonzeros; log "%d: %d\n" i n)
  done;
  log "number of mappings: %d\n" !nonzeros;
  log "theorem most used: %d\n" !thm_uses_argmax
;;

let print_rule_uses() : unit =
  let total = float_of_int (nb_proofs()) in
  let part n = float_of_int (100 * n) /. total in
  let f i n = log "%10s %9d %2.f%%\n" (name_of_code i) n (part n) in
  Array.iteri f rule_uses
;;
