(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib

let usage() =
  Printf.printf "usage: %s proofs.dump file.[dk|lp]\n%!" Sys.argv.(0)

let main() =
  let n = Array.length Sys.argv - 1 in
  if n > 2 then
    begin
      Printf.eprintf "wrong number of arguments\n%!";
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
       Printf.eprintf "%s: wrong file extension\n%!" ext;
       usage();
       exit 1
  in
  let basename = Filename.chop_extension filename in
  let dump_file = Sys.argv.(1) in
  let ic = open_in_bin dump_file in
  let read() = Marshal.from_channel ic in
  let _nb_proofs = read() in
  the_type_constants := read();
  the_term_constants := read();
  new_constant("el",aty);
  the_axioms := read();
  the_definitions := read();
  (*update_map_const_typ_vars_pos();*)
  let proofs_in_range theorem =
    fun oc r ->
    try
      the_proofs_idx := -1;
      while true do
        let k = !the_proofs_idx + 1 in
        let p = read() in
        Array.set the_proofs k p;
        theorem oc k p;
        the_proofs_idx := k
      done
    with End_of_file -> close_in ic
  in
  if dk then Xdk.export_to_dk_file (proofs_in_range Xdk.theorem) basename All
  else Xlp.export_to_lp_file (proofs_in_range Xlp.theorem) basename All

let _ = main()
