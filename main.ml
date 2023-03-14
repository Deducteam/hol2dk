(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof

let usage() =
  log
"usage: %s [option] file.[dk|lp] [number [number]]]
option: --stats | --sig | --part number\n%!"
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

  (* parse arguments *)
  let args = List.tl (Array.to_list Sys.argv) in
  let stats, args =
    try let l1, l2 = split "--stats" args in true, List.rev_append l1 l2
    with Not_found -> false, args
  in
  let sig_only, args =
    try let l1, l2 = split "--sig" args in true, List.rev_append l1 l2
    with Not_found -> false, args
  in
  let part, args =
    try match split "--part" args with
        | l1, x::l2 when not sig_only ->
           Some (int_of_string x), List.rev_append l1 l2
        | l1, [] -> wrong_arg_nb()
    with Not_found -> None, args
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
  (* we add "el" to use mk_const without failing *)
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
  match dk, part, range with

  | _, Some k, All ->
     let b = basename in
     let mk = b ^ ".mk" in
     log "generate %s ...\n%!" mk;
     let oc = open_out mk in
     let part_size = nb_proofs / k in

     out oc ".SUFFIXES:\n";
     out oc ".PHONY: default dk lp\n";
     out oc "default: dk lp\n";

     (* dk part *)
     out oc "dk: %s.dk\n" b;
     out oc "%s.dk: hol_theory.dk %s_types.dk %s_terms.dk %s_axioms.dk"
       b b b b;
     for i = 1 to k do
       (* we do not put all files so that make does not duplicate works *)
       out oc (* %s_part_%d_type_abbrevs.dk %s_part_%d_term_abbrevs.dk *)
         " %s_part_%d.dk" (*b i b i*) b i
     done;
     out oc "\n\tcat $+ > $@\n";
     out oc "%s_types.dk %s_terms.dk %s_axioms.dk : %s.sig\n\
             \thol2dk %s.dk --sig\n" b b b b b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.dk %s_part_%d_type_abbrevs.dk \
               %s_part_%d_term_abbrevs.dk: %s.sig %s.prf\n\
               \thol2dk %s.dk --part %d %d %d\n"
         b i b i b i b b b i !x y
     in
     for i = 1 to k-1 do let y = !x + part_size in cmd i (y-1); x := y done;
     cmd k (nb_proofs - 1);

     (* lp part *)
     out oc "lp: hol_theory.lp %s_types.lp %s_terms.lp %s_axioms.lp" b b b;
     for i = 1 to k do
       (* we do not put all files so that make does not duplicate works *)
       out oc (* %s_part_%d_type_abbrevs.lp %s_part_%d_term_abbrevs.lp *)
         " %s_part_%d.lp" (*b i b i*) b i
     done;
     out oc "\n%s_types.lp %s_terms.lp %s_axioms.lp : %s.sig\n\
             \thol2dk %s.lp --sig\n" b b b b b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.lp %s_part_%d_type_abbrevs.lp \
               %s_part_%d_term_abbrevs.lp: %s.sig %s.prf\n\
               \thol2dk %s.lp --part %d %d %d\n"
         b i b i b i b b b i !x y
     in
     for i = 1 to k-1 do let y = !x + part_size in cmd i (y-1); x := y done;
     cmd k (nb_proofs - 1);

  | false, Some k, Inter(x,y) ->
     Xlp.export_proofs_part basename k x y;
     let suffix = "_part_" ^ string_of_int k in
     Xlp.export_term_abbrevs basename suffix;
     Xlp.export_type_abbrevs basename suffix

  | true, Some k, Inter(x,y) ->
     Xdk.export_proofs_part basename k x y;
     let suffix = "_part_" ^ string_of_int k in
     Xdk.export_term_abbrevs basename suffix;
     Xdk.export_type_abbrevs basename suffix

  | _, Some _, _ -> wrong_arg_nb()

  | false, _, _ ->
     Xlp.export_types basename;
     Xlp.export_terms basename;
     Xlp.export_axioms basename;
     if sig_only then exit 0;
     Xlp.export_proofs basename range;
     Xlp.export_term_abbrevs basename "";
     Xlp.export_type_abbrevs basename ""

  | true, _, _ ->
     (*Xdk.export_to_dk_file basename range;*)
     Xdk.export_types basename;
     Xdk.export_terms basename;
     Xdk.export_axioms basename;
     if sig_only then exit 0;
     Xdk.export_proofs basename range;
     Xdk.export_term_abbrevs basename "";
     Xdk.export_type_abbrevs basename "";
     log "generate %s.dk ...\n%!" basename;
     let infiles =
       List.map (fun s -> basename ^ "_" ^ s ^ ".dk")
         ["types";"type_abbrevs";"terms";"term_abbrevs";"axioms";"proofs"] in
     exit
       (Sys.command
          ("cat hol_theory.dk " ^ String.concat " " infiles
           ^ " > " ^ basename ^ ".dk"))

let _ = main()
