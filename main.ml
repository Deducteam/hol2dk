(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof

let usage() =
  log
"usage: %s [option] file.[dk|lp] [number [number]]]
option: --stats | --sig | --pos | --part number\n%!"
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
  let nb_part, args =
    try match split "--part" args with
        | l1, x::l2 when not sig_only ->
           let k = int_of_string x in
           if k < 1 then wrong_arg_nb();
           k, List.rev_append l1 l2
        | l1, [] -> wrong_arg_nb()
    with Not_found -> 0, args
  in
  let pos, args =
    try let l1, l2 = split "--pos" args in true, List.rev_append l1 l2
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

  (* read nb_proofs *)
  let dump_file = basename ^ ".sig" in
  let ic = open_in_bin dump_file in
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;

  (* compute proof positions *)
  if pos then
    begin
      close_in ic;
      let dump_file = basename ^ ".prf" in
      log "read %s ...\n%!" dump_file;
      let ic = open_in_bin dump_file in
      let pos = Array.make nb_proofs 0 in
      let idx = ref 0 in
      begin
        try
          while !idx < nb_proofs do
            Array.set pos (!idx) (pos_in ic);
            ignore (input_value ic);
            incr idx;
          done
        with End_of_file -> assert false
      end;
      close_in ic;
      let dump_file = basename ^ ".pos" in
      log "generate %s ...\n%!" dump_file;
      let oc = open_out_bin dump_file in
      output_value oc pos;
      close_out oc;
      exit 0
    end;

  (* print stats *)
  if stats then
    begin
      close_in ic;
      let dump_file = basename ^ ".prf" in
      log "read %s ...\n%!" dump_file;
      let ic = open_in_bin dump_file in
      Xproof.thm_uses := Array.make nb_proofs 0;
      begin
        try
          while true do
            let p = input_value ic in
            count_thm_uses p;
            count_rule_uses p
          done
        with End_of_file -> close_in ic
      end;
      log "compute statistics ...\n";
      print_thm_uses_histogram();
      print_rule_uses();
      exit 0
    end;

  (* generate mk file *)
  if nb_part > 1 && range = All then
    begin
      let b = basename in
      let mk = b ^ ".mk" in
      log "generate %s ...\n%!" mk;
      let oc = open_out mk in
      let part_size = nb_proofs / nb_part in

      out oc ".SUFFIXES :\n";
      out oc ".PHONY : dk lp\n";

      (* dk part *)
      out oc "dk : %s.dk\n" b;
      out oc "%s.dk : hol_theory.dk %s_types.dk %s_terms.dk %s_axioms.dk"
        b b b b;
      for i = 1 to nb_part do
        out oc " %s_part_%d_type_abbrevs.dk %s_part_%d_term_abbrevs.dk \
                %s_part_%d.dk" b i b i b i
      done;
      out oc "\n\tcat $+ > $@\n";
      out oc "%s_types.dk %s_terms.dk %s_axioms.dk &: %s.sig\n\
              \thol2dk %s.dk --sig\n" b b b b b;
      out oc "%s.pos : %s.prf\n\thol2dk %s.dk --pos\n" b b b;
      let x = ref 0 in
      let cmd i y =
        out oc "%s_part_%d.dk %s_part_%d_type_abbrevs.dk \
                %s_part_%d_term_abbrevs.dk &: %s.sig %s.prf %s.pos\n\
                \thol2dk %s.dk --part %d %d %d\n"
          b i b i b i b b b b i !x y
      in
      for i = 1 to nb_part - 1 do
        let y = !x + part_size in cmd i (y-1); x := y
      done;
      cmd nb_part (nb_proofs - 1);

      (* lp part *)
      out oc "lp : hol_theory.lp %s_types.lp %s_terms.lp %s_axioms.lp" b b b;
      for i = 1 to nb_part do
        out oc " %s_part_%d_type_abbrevs.lp %s_part_%d_term_abbrevs.lp \
                %s_part_%d.lp" b i b i b i
      done;
      out oc "\n%s_types.lp %s_terms.lp %s_axioms.lp &: %s.sig\n\
              \thol2dk %s.lp --sig\n" b b b b b;
      let x = ref 0 in
      let cmd i y =
        out oc "%s_part_%d.lp %s_part_%d_type_abbrevs.lp \
                %s_part_%d_term_abbrevs.lp &: %s.sig %s.prf %s.pos\n\
                \thol2dk %s.lp --part %d %d %d\n"
          b i b i b i b b b b i !x y
      in
      for i = 1 to nb_part - 1 do
        let y = !x + part_size in cmd i (y-1); x := y
      done;
      cmd nb_part (nb_proofs - 1);
      exit 0
    end;

  (* read signature *)
  log "read %s ...\n%!" dump_file;
  the_type_constants := input_value ic;
  (* we add "el" to use mk_const without failing *)
  the_term_constants := ("el",aty)::input_value ic;
  the_axioms := input_value ic;
  the_definitions := input_value ic;
  close_in ic;
  update_map_const_typ_vars_pos();
  update_reserved();

  (* generate signature related files *)
  if sig_only then
    begin
      if dk then
        begin
          Xdk.export_types basename;
          Xdk.export_terms basename;
          Xdk.export_axioms basename;
        end
      else
        begin
          Xlp.export_types basename;
          Xlp.export_terms basename;
          Xlp.export_axioms basename
        end;
      exit 0
    end;

  (* read pos file *)
  let dump_file = basename ^ ".pos" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  Xproof.prf_pos := input_value ic;
  close_in ic;

  (* read and translate proof file *)
  let dump_file = basename ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  Xproof.ic_prf := open_in_bin dump_file;
  match dk, range with
  | false, Inter(x,y) ->
     Xlp.export_proofs_part basename nb_part x y;
     let suffix = "_part_" ^ string_of_int nb_part in
     Xlp.export_term_abbrevs basename suffix;
     Xlp.export_type_abbrevs basename suffix

  | true, Inter(x,y) ->
     Xdk.export_proofs_part basename nb_part x y;
     let suffix = "_part_" ^ string_of_int nb_part in
     Xdk.export_term_abbrevs basename suffix;
     Xdk.export_type_abbrevs basename suffix

  | false, _ ->
     Xlp.export_proofs basename range;
     Xlp.export_term_abbrevs basename "";
     Xlp.export_type_abbrevs basename ""

  | true, _ ->
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
