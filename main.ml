(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof

let usage() =
  log "usage: %s file.sig file.prf [file.[dk|lp] [number]]\n%!"
    Sys.argv.(0)

let main() =

  (* check number of arguments *)
  let n = Array.length Sys.argv - 1 in
  if n < 2 || n > 4 then
    begin
      Printf.eprintf "wrong number of arguments\n%!";
      usage();
      exit 1
    end;

  (* read signature *)
  let dump_file = Sys.argv.(1) in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  the_type_constants := input_value ic;
  the_term_constants := ("el",aty)::input_value ic;
  the_axioms := input_value ic;
  the_definitions := input_value ic;
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;

  (* set dump file for proofs *)
  let dump_file = Sys.argv.(2) in
  set_dump_file dump_file nb_proofs;

  (* if no output file is given, read proofs, print stats and exit *)
  if n = 2 then
    begin
      log "read %s ...\n%!" dump_file;
      let f _ p = count_thm_uses p; count_rule_uses p in
      iter_proofs f;
      log "compute statistics ...\n";
      print_thm_uses_histogram();
      print_rule_uses();
      ignore (Sys.command "rm -f .dump.prf");
      exit 0
    end;

  (* check file extension *)
  let filename = Sys.argv.(3) in
  let ext = Filename.extension filename in
  let dk =
    match ext with
    | ".dk"  -> true
    | ".lp" -> false
    | _ ->
       Printf.eprintf "%s: wrong file extension\n%!" ext;
       usage();
       exit 1
  in
  let basename = Filename.chop_extension filename in

  (* generate output *)
  let export = if dk then Xdk.export_to_dk_file else Xlp.export_to_lp_file in
  let range =
    if n = 4 then
      let x = int_of_string Sys.argv.(4) in
      log "read %s ...\n%!" dump_file;
      for k = 0 to x-1 do ignore (proof_at k) done;
      Only x
    else All
  in
  export basename range

let _ = main()
