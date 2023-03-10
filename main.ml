(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof

let usage() =
  log "usage: %s [--stats] file.[dk|lp] [number [number]]]\n%!"
    Sys.argv.(0)

let wrong_arg_nb() =
  Printf.eprintf "wrong number of arguments\n%!"; usage(); exit 1

(* [split x l] returns a pair of lists [l1,l2] such that [l = rev l1 @
   x :: l2], and raises [Not_found] if [x] does not occur in [l]. *)
let split x =
  let rec aux acc l =
    match l with
    | [] -> raise Not_found
    | y::m -> if y = x then acc, m else aux (y::acc) m
  in aux []

let main() =

  (* check number of arguments *)
  let n = Array.length Sys.argv - 1 in
  if n < 1 || n > 4 then wrong_arg_nb();

  (* parse arguments *)
  let args = List.tl (Array.to_list Sys.argv) in
  let stats, args =
    try let l1, l2 = split "--stats" args in true, List.rev_append l1 l2
    with Not_found -> false, args
  in
  let filename, args =
    match args with
    | [] -> wrong_arg_nb()
    | filename :: args -> filename, args
  in
  let dk =
    match Filename.extension filename with
      | ".dk"  -> true
      | ".lp" -> false
      | _ -> Printf.eprintf "wrong file extension\n%!"; usage(); exit 1
  in
  let basename = Filename.chop_extension filename in
  let range =
    match args with
    | [] -> All
    | [x] -> Only (int_of_string x)
    | [x;y] -> Inter (int_of_string x, int_of_string y)
    | _ -> wrong_arg_nb()
  in

  (* read signature file *)
  let dump_file = basename ^ ".sig" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  the_type_constants := input_value ic;
  the_term_constants := ("el",aty)::input_value ic;
  the_axioms := input_value ic;
  the_definitions := input_value ic;
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;

  (* prepare proof reading *)
  let dump_file = basename ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  init_proof_reading dump_file nb_proofs;

  (* print stats *)
  if stats then
    begin
      iter_proofs (fun _ p -> count_thm_uses p; count_rule_uses p);
      log "compute statistics ...\n";
      print_thm_uses_histogram();
      print_rule_uses();
      exit 0
    end;

  (* read proofs up to range start *)
  begin match range with
  | Only x | Inter(x,_) -> for k = 0 to x-1 do ignore (proof_at k) done
  | All -> ()
  | Upto _ -> assert false
  end;

  (* generate output *)
  update_map_const_typ_vars_pos();
  if dk then Xdk.export_to_dk_file basename range
  else
    begin
      Xlp.export_types basename;
      Xlp.export_terms basename;
      Xlp.export_axioms basename;
      Xlp.export_proofs basename range
      Xlp.export_term_abbrevs basename;
      Xlp.export_type_abbrevs basename;
    end

let _ = main()
