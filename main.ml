(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude

let usage() =
  log "usage: %s file_sig.dump file_proofs.dump [file.[dk|lp] [number]]\n%!"
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
  let read() = Marshal.from_channel ic in
  the_type_constants := read();
  the_term_constants := ("el",aty)::read();
  the_axioms := read();
  the_definitions := read();
  let nb_proofs = read() in
  Printf.printf "%d proof steps\n%!" nb_proofs;
  the_proofs := Array.make nb_proofs dummy_proof;

  (* read proofs *)
  begin
    let dump_file = Sys.argv.(2) in
    log "read %s ...\n%!" dump_file;
    let ic = open_in_bin dump_file in
    the_proofs_idx := -1;
    try
      while true do
        let k = !the_proofs_idx + 1 in
        Array.set (!the_proofs) k (Marshal.from_channel ic);
        the_proofs_idx := k
      done
    with End_of_file -> close_in ic
  end;
  log "compute statistics ...";
  print_proof_stats();
  if n = 2 then exit 0;

  (* get filename and check file extension *)
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
  let range = if n = 4 then Only (int_of_string Sys.argv.(4)) else All in
  (if dk then Xdk.export_to_dk_file else Xlp.export_to_lp_file) basename range

let _ = main()
