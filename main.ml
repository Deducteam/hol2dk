(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof

let usage() =
  log "usage: %s [--stats] file.[dk|lp] [number [number]]]\n%!"
    Sys.argv.(0)

let wrong_arg_nb() =
  Printf.eprintf "wrong number of arguments\n%!";
  usage();
  exit 1

let main() =

  (* check number of arguments *)
  let n = Array.length Sys.argv - 1 in
  if n < 1 || n > 4 then wrong_arg_nb();

  (* parse arguments *)
  let stats, filename, (*other*) args =
    if Sys.argv.(1) = "--stats" then
      if n <> 2 then wrong_arg_nb() else true, Sys.argv.(2), [||]
    else false, Sys.argv.(1), Array.sub Sys.argv 2 (n-1)
  in
  let dk =
    match Filename.extension filename with
      | ".dk"  -> true
      | ".lp" -> false
      | _ -> Printf.eprintf "wrong file extension\n%!"; usage(); exit 1
  in
  let basename = Filename.chop_extension filename in
  let range =
    match Array.length args with
    | 0 -> All
    | 1 -> Only (int_of_string args.(0))
    | 2 -> Inter (int_of_string args.(0), int_of_string args.(1))
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
  update_map_const_typ_vars_pos();

  (* print stats *)
  if stats then
    begin
      let dump_file = basename ^ ".prf" in
      set_dump_file dump_file nb_proofs;
      log "read %s ...\n%!" dump_file;
      iter_proofs (fun _ p -> count_thm_uses p; count_rule_uses p);
      log "compute statistics ...\n";
      print_thm_uses_histogram();
      print_rule_uses();
      exit 0
    end;

  (* generate signature related files *)
  if not dk then
    begin
      Xlp.export_types basename;
      Xlp.export_terms basename;
      Xlp.export_axioms basename
    end;

  (* read proofs before range start *)
  let dump_file = basename ^ ".prf" in
  set_dump_file dump_file nb_proofs;
  log "read %s ...\n%!" dump_file;
  begin match range with
  | Only x | Inter(x,_) -> for k = 0 to x-1 do ignore (proof_at k) done
  | Upto _ -> assert false
  | All -> iter_proofs (fun _ _ -> ())
  end;

  (* generate output *)
  if dk then Xdk.export_to_dk_file basename range
  else
    begin
      Xlp.export_proofs basename range;
      Xlp.export_term_abbrevs basename;
      Xlp.export_type_abbrevs basename;
    end

let _ = main()
