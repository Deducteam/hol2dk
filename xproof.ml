(****************************************************************************)
(* Accessing proofs from their indexes. *)
(****************************************************************************)

open Fusion
open Xlib
open Xprelude

(*
let the_proofs : proof array ref = ref [||]
let proof_at k = Array.get (!the_proofs) k
let the_proofs_idx : int ref = ref (-1)
let nb_proofs() = !the_proofs_idx + 1
let iter_proofs f = for k = 0 to !the_proofs_idx do f k (proof_at k) done
*)

let ic_dump : in_channel ref = ref stdin
let pos_dump : int array ref = ref [||]

let set_dump_file filename n =
  let ic = open_in_bin filename in
  ic_dump := ic;
  pos_dump := Array.make n (-1)

let nb_proofs() = Array.length !pos_dump

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

let iter_proofs f =
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

(****************************************************************************)
(* Print statistics on proofs. *)
(****************************************************************************)

let print_proof_stats() =
  (* Array for mapping each proof index to the number of times it is used. *)
  let proof_uses = Array.make (nb_proofs()) 0 in
  (* Maximum number of times a proof is used. *)
  let max = ref 0 in
  (* Actually compute [proof_uses]. *)
  let use k =
    let n = Array.get proof_uses k + 1 in
    Array.set proof_uses k n;
    if n > !max then max := n
  in
  iter_proofs (fun _ p -> List.iter use (deps p));
  (* Array for mapping to each number n <= !max the number of proofs which
     is used n times. *)
  let hist = Array.make (!max + 1) 0 in
  let f nb_uses = Array.set hist nb_uses (Array.get hist nb_uses + 1) in
  Array.iter f proof_uses;
  (* Print histogram *)
  log "i: n means that n proofs are used i times\n";
  let nonzeros = ref 0 in
  for i=0 to !max do
    let n = Array.get hist i in
    if n>0 then (incr nonzeros; log "%d: %d\n" i n)
  done;
  log "number of mappings: %d\n" !nonzeros;
  (* Count the number of times each proof rule is used. *)
  let index p =
    let Proof(_,c) = p in
    match c with
    | Prefl _ -> 0
    | Ptrans _ -> 1
    | Pmkcomb _ -> 2
    | Pabs _ -> 3
    | Pbeta _ -> 4
    | Passume _ -> 5
    | Peqmp _ -> 6
    | Pdeduct _ -> 7
    | Pinst _ -> 8
    | Pinstt _ -> 9
    | Paxiom _ -> 10
    | Pdef _ -> 11
    | Pdeft _ -> 12
    | Ptruth -> 13
    | Pconj _ -> 14
    | Pconjunct1 _ -> 15
    | Pconjunct2 _ -> 16
    | Pmp _ -> 17
    | Pdisch _ -> 18
    | Pspec _ -> 19
    | Pgen _ -> 20
    | Pexists _ -> 21
    | Pdisj1 _ -> 22
    | Pdisj2 _ -> 23
    | Pdisj_cases _ -> 24
  in
  let name = function
    | 0 -> "refl"
    | 1 -> "trans"
    | 2 -> "comb"
    | 3 -> "abs"
    | 4 -> "beta"
    | 5 -> "assume"
    | 6 -> "eqmp"
    | 7 -> "deduct"
    | 8 -> "term_subst"
    | 9 -> "type_subst"
    | 10 -> "axiom"
    | 11 -> "sym_def"
    | 12 -> "type_def"
    | 13 -> "truth"
    | 14 -> "conj"
    | 15 -> "conjunct1"
    | 16 -> "conjunct2"
    | 17 -> "mp"
    | 18 -> "disch"
    | 19 -> "spec"
    | 20 -> "gen"
    | 21 -> "exists"
    | 22 -> "disj1"
    | 23 -> "disj2"
    | 24 -> "disj_cases"
    | _ -> assert false
  in
  let rule_uses = Array.make 25 0 in
  let f k p =
    let i = index p in
    let n = Array.get rule_uses i + 1 in
    Array.set rule_uses i n
  in
  iter_proofs f;
  let total = float_of_int (nb_proofs()) in
  let part n = float_of_int (100 * n) /. total in
  let f i n = log "%10s %9d %2.f%%\n" (name i) n (part n) in
  Array.iteri f rule_uses;
  log "number of proof steps: %d\nnumber of unused theorems: %d (%2.f%%)\n"
    (nb_proofs()) hist.(0) (part hist.(0))
;;
