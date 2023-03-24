(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof
open Xfiles
open Xnames

let usage() =
  log
"hol2dk uses:

hol2dk [-h|--help]
  print this help

hol2dk dump file.[ml|hl]
  run OCaml to check file.[ml|hl] and generate file.sig, file.prf and file.thm

hol2dk sig basename
  generate dk/lp signature files from basename.sig

hol2dk thm basename
  generate dk/lp theorems from basename.thm

hol2dk stat basename
  print statistics on basename.prf

hol2dk pos basename
  generate file.pos from basename.prf

hol2dk file.[dk|lp]
  generate file.[dk|lp] from file.sig, file.prf and file.pos

hol2dk file.[dk|lp] $thm_id
  generate file.[dk|lp] from file.sig, file.prf and file.pos
  but for theorem index $thm_id only (useful for debug)

hol2dk mk $n basename
  generate basename.mk from basename.prf
  (to generate dk/lp files using $n processors)

hol2dk part $k $x $y file.[dk|lp]
  generate dk/lp proof files of part $k (in [1..$n])
  from proof index $x to proof index $y

hol2dk dep
  print on stdout a Makefile giving the dependencies of all HOL-Light files
  in the working directory and all its subdirectories recursively

hol2dk dep file.[ml|hl]
  print on stdout all the HOL-Light files required to check file.[ml|hl]

hol2dk name file.[ml|hl]
  print on stdout the named theorems proved in file.[ml|hl]

hol2dk name upto file.[ml|hl]
  print on stdout the named theorems proved in file.[ml|hl]
  and all its dependencies

hol2dk name
  print on stdout the named theorems proved in all HOL-Light files
  in the working directory and all its subdirectories recursively
%!"

let wrong_arg() = Printf.eprintf "wrong argument(s)\n%!"; exit 1

let read_nb_proofs basename =
  let dump_file = basename ^ ".sig" in
  let ic = open_in_bin dump_file in
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;
  close_in ic;
  nb_proofs

let is_dk filename =
  match Filename.extension filename with
  | ".dk"  -> true
  | ".lp" -> false
  | _ -> wrong_arg()

let read_sig basename =
  let dump_file = basename ^ ".sig" in
  let ic = open_in_bin dump_file in
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;
  log "read %s ...\n%!" dump_file;
  the_type_constants := input_value ic;
  (* we add "el" to use mk_const without failing *)
  the_term_constants := ("el",aty)::input_value ic;
  the_axioms := input_value ic;
  the_definitions := input_value ic;
  close_in ic;
  update_map_const_typ_vars_pos();
  update_reserved()

let read_pos basename =
  let dump_file = basename ^ ".pos" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  Xproof.prf_pos := input_value ic;
  close_in ic

let read_map_thid_name basename =
  let dump_file = basename ^ ".thm" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin (basename ^ ".thm") in
  let map_thid_name = input_value ic in
  close_in ic;
  map_thid_name

let init_proof_reading basename =
  let dump_file = basename ^ ".prf" in
  log "read %s ...\n%!" dump_file;
  Xproof.ic_prf := open_in_bin dump_file

let int s = try int_of_string s with Failure _ -> wrong_arg()

let main() =
  match List.tl (Array.to_list Sys.argv) with

  | [] | ["-"|"--help"] -> usage(); exit 0

  | ["dep";f] ->
     let dg = dep_graph (files()) in
     out stdout "%a\n" (list_sep " " string) (trans_deps dg f);
     exit 0

  | ["dep"] ->
     out_dep_graph stdout (dep_graph (files()));
     exit 0

  | ["name";f] ->
     out stdout "%a\n" (list_sep "\n" string) (thms_of_file f);
     exit 0

  | ["name";"upto";f] ->
     let dg = dep_graph (files()) in
     List.iter
       (fun d -> List.iter (out stdout "%s %s\n" d) (thms_of_file d))
       (trans_deps dg f);
     exit 0

  | ["name"] ->
     List.iter
       (fun f -> List.iter (out stdout "%s %s\n" f) (thms_of_file f))
       (files());
     exit 0

  | ["dump";f] ->
     begin match Filename.extension f with
     | ".ml" | ".hl" ->
        let b = Filename.chop_extension f in
        log "generate .dump.ml ...\n%!";
        let oc = open_out ".dump.ml" in
        out oc
{|#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
#use "%s";;
dump_signature "%s.sig";;
#load "str.cma";;
#use "xnames.ml";;
dump_map_thid_name "%s.thm" %a;;
|} f b b (olist ostring) (trans_deps (dep_graph (files())) f);
        close_out oc;
        exit (Sys.command ("ocaml .dump.ml && mv -f .dump.prf "^b^".prf"))
     | _ -> wrong_arg()
     end

  | ["stat";basename] ->
     let nb_proofs = read_nb_proofs basename in
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

  | ["pos";basename] ->
     let nb_proofs = read_nb_proofs basename in
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

  | ["mk";nb_part;b] ->
     let nb_part = int nb_part in
     if nb_part < 2 then wrong_arg();
     let nb_proofs = read_nb_proofs b in
     let mk = b ^ ".mk" in
     log "generate %s ...\n%!" mk;
     let oc = open_out mk in
     let part_size = nb_proofs / nb_part in

     out oc ".SUFFIXES :\n";
     out oc ".PHONY : dk lp\n";

     (* dk part *)
     out oc "\ndk : %s.dk\n" b;
     out oc "%s.dk : theory_hol.dk %s_types.dk %s_terms.dk %s_axioms.dk"
       b b b b;
     for i = 1 to nb_part do
       out oc " %s_part_%d_type_abbrevs.dk %s_part_%d_term_abbrevs.dk \
               %s_part_%d.dk" b i b i b i
     done;
     out oc " %s_theorems.dk\n\tcat $+ > $@\n" b;
     out oc "%s_types.dk %s_terms.dk %s_axioms.dk &: %s.sig\n\
             \thol2dk sig %s.dk\n" b b b b b;
     out oc "%s_theorems.dk : %s.sig %s.prf %s.pos %s.thm\n\
             \thol2dk thm %d %s.dk\n" b b b b b nb_part b;
     out oc "%s.pos : %s.prf\n\thol2dk pos %s\n" b b b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.dk %s_part_%d_type_abbrevs.dk \
               %s_part_%d_term_abbrevs.dk &: %s.sig %s.prf %s.pos\n\
               \thol2dk part %d %d %d %s.dk\n"
         b i b i b i b b b i !x y b
     in
     for i = 1 to nb_part - 1 do
       let y = !x + part_size in cmd i (y-1); x := y
     done;
     cmd nb_part (nb_proofs - 1);

     (* lp part *)
     out oc "\nlp : %s.lp theory_hol.lp %s_types.lp %s_terms.lp %s_axioms.lp"
       b b b b;
     for i = 1 to nb_part do
       out oc " %s_part_%d_type_abbrevs.lp %s_part_%d_term_abbrevs.lp \
               %s_part_%d.lp" b i b i b i
     done;
     out oc "\n%s_types.lp %s_terms.lp %s_axioms.lp &: %s.sig\n\
             \thol2dk sig %s.lp\n" b b b b b;
     out oc "%s.lp : %s.sig %s.prf %s.pos %s.thm\n\
             \thol2dk thm %d %s.lp\n" b b b b b nb_part b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.lp %s_part_%d_type_abbrevs.lp \
               %s_part_%d_term_abbrevs.lp &: %s.sig %s.prf %s.pos\n\
               \thol2dk part %d %d %d %s.lp\n"
         b i b i b i b b b i !x y b
     in
     for i = 1 to nb_part - 1 do
       let y = !x + part_size in cmd i (y-1); x := y
     done;
     cmd nb_part (nb_proofs - 1);
     exit 0

  | ["sig";f] ->
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     if dk then
       begin
         Xdk.export_types basename;
         Xdk.export_terms basename;
         Xdk.export_axioms basename
       end
     else
       begin
         Xlp.export_types basename;
         Xlp.export_terms basename;
         Xlp.export_axioms basename
       end;
     exit 0

  | ["thm";nb_part;f] ->
     let nb_part = int nb_part in
     if nb_part < 2 then wrong_arg();
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     let map_thid_name = read_map_thid_name basename in
     read_pos basename;
     init_proof_reading basename;
     if dk then Xdk.export_theorems basename map_thid_name
     else Xlp.export_theorems_part nb_part basename map_thid_name

  | ["part";nb_part;x;y;f] ->
     let nb_part = int nb_part in
     if nb_part < 0 then wrong_arg();
     let x = int x in
     if x < 0 then wrong_arg();
     let y = int y in
     if y < x then wrong_arg();
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     read_pos basename;
     init_proof_reading basename;
     if dk then
       begin
         Xdk.export_proofs_part basename nb_part x y;
         let suffix = "_part_" ^ string_of_int nb_part in
         Xdk.export_term_abbrevs basename suffix;
         Xdk.export_type_abbrevs basename suffix
       end
     else
       begin
         Xlp.export_proofs_part basename nb_part x y;
         let suffix = "_part_" ^ string_of_int nb_part in
         Xlp.export_term_abbrevs basename suffix;
         Xlp.export_type_abbrevs basename suffix
       end;
     exit 0

  | f::args ->
     let range =
       match args with
       | [] -> All
       | [x] ->
          let x = int x in
          if x < 0 then wrong_arg();
          Only x
       | [x;y] ->
          let x = int x in
          if x < 0 then wrong_arg();
          let y = int y in
          if y < x then wrong_arg();
          Inter(x,y)
     in
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     (* read and translate sig file *)
     read_sig basename;
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
     read_pos basename;
     let map_thid_name = read_map_thid_name basename in
     init_proof_reading basename;
     if dk then
       begin
         Xdk.export_proofs basename range;
         Xdk.export_theorems basename map_thid_name;
         Xdk.export_term_abbrevs basename "";
         Xdk.export_type_abbrevs basename "";
         log "generate %s.dk ...\n%!" basename;
         let infiles =
           List.map (fun s -> basename ^ "_" ^ s ^ ".dk")
             ["types";"type_abbrevs";"terms";"term_abbrevs";"axioms"
              ;"proofs";"theorems"]
         in
         exit
           (Sys.command
              ("cat theory_hol.dk " ^ String.concat " " infiles
               ^ " > " ^ basename ^ ".dk"))
       end
     else
       begin
         Xlp.export_proofs basename range;
         Xlp.export_theorems basename map_thid_name;
         Xlp.export_term_abbrevs basename "";
         Xlp.export_type_abbrevs basename "";
         exit 0
       end

let _ = main()
