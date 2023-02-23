(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib

let usage() =
  Printf.printf "usage: %s proofs.dump file.[dk|lp]\n%!" Sys.argv.(0)

let main() =
  let n = Array.length Sys.argv - 1 in
  if n > 2 then
    begin
      Printf.eprintf "wrong number of arguments\n";
      usage();
      exit 1
    end;
  let filename = Sys.argv.(2) in
  let ext = Filename.extension filename in
  let dk =
    match ext with
    | ".dk"  -> true
    | ".lp" -> false
    | _ ->
       Printf.eprintf "%s: wrong file extension" ext;
       usage();
       exit 1
  in
  let basename = Filename.chop_extension filename in
  let dump_file = Sys.argv.(1) in
  let ic = open_in_bin dump_file in
  let read() = Marshal.from_channel ic in
  let idx = ref (-1) in
  the_type_constants := read();
  the_term_constants := read();
  the_axioms := read();
  the_definitions := read();
  update_map_const_typ_vars_pos();
  let proofs_in_range oc _r =
    try
      while true do
        let p = read() in
        incr idx;
        Xlp.theorem oc !idx p
      done
    with End_of_file -> close_in ic
  in
  if dk then Xlp.export_to_lp_file proofs_in_range basename All
  else Xdk.export_to_dk_file proofs_in_range basename All

let _ = main()
