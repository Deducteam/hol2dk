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

Dumping commands:

hol2dk dump $file.[ml|hl]
  run OCaml toplevel to check $file.[ml|hl] and generate
  $file.sig (type and term constants), $file.prf (proof steps)
  and $file.thm (named theorems)

hol2dk pos $file
  generate $file.pos, the positions of proofs in $file.prf

Single-threaded dk/lp file generation:

hol2dk $file.[dk|lp]
  generate $file.[dk|lp]

hol2dk $file.[dk|lp] $thm_id
  generate $file.[dk|lp] but with theorem index $thm_id only (useful for debug)

Multi-threaded dk/lp file generation:

hol2dk dg $n $file
  generate $file.dg, the dependency graph of parts
  when $file.prf is split in $n parts

hol2dk mk $n $file [$coq_file.v]
  generate $file.mk and _CoqProject to generate, translate and check files
  when $file.prf is split in $n parts
  ($coq_file.v is a Coq file required in every generated Coq file)

hol2dk sig $file
  generate dk/lp signature files from $file.sig

hol2dk thm $n $file.[dk|lp]
  generate dk/lp theorem files from $file.thm

hol2dk use $file
  generate $file.use, the number of times each proof step is used

hol2dk part $n $k $x $y $file.[dk|lp]
  generate dk/lp proof files of part $k in [1..$n]
  from proof index $x to proof index $y

Other commands:

hol2dk stat $file
  print statistics on $file.prf

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

let read_thm basename =
  let map = read_val (basename ^ ".thm") in
  log "%d named theorems\n%!" (MapInt.cardinal map);
  map

let integer s = try int_of_string s with Failure _ -> wrong_arg()

let make nb_part b req =
     let nb_part = integer nb_part in
     if nb_part < 2 then wrong_arg();
     let nb_proofs = read_nb_proofs b in
     let part_size = nb_proofs / nb_part in
     let dg = read_val (b ^ ".dg") in
     let dump_file = b ^ ".mk" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out dump_file in
     out oc "# file generated with: hol2dk mk %d %s\n\n" nb_part b;
     out oc ".SUFFIXES :\n";

     (* dk files generation *)
     out oc "\n.PHONY : dk\n";
     out oc "dk : %s.dk\n" b;
     out oc "%s.dk : theory_hol.dk %s_types.dk %s_terms.dk %s_axioms.dk"
       b b b b;
     for i = 1 to nb_part do
       out oc " %s_part_%d_type_abbrevs.dk %s_part_%d_term_abbrevs.dk \
               %s_part_%d.dk" b i b i b i
     done;
     out oc " %s_theorems.dk\n\tcat $+ > $@\n" b;
     out oc "%s_types.dk %s_terms.dk %s_axioms.dk &: %s.sig\n\
             \thol2dk sig %s.dk\n" b b b b b;
     out oc "%s_theorems.dk : %s.sig %s.thm %s.pos %s.prf\n\
             \thol2dk thm %d %s.dk\n" b b b b b nb_part b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.dk %s_part_%d_type_abbrevs.dk \
               %s_part_%d_term_abbrevs.dk &: %s.sig %s.prf %s.pos\n\
               \thol2dk part %d %d %d %d %s.dk\n"
         b i b i b i b b b nb_part i !x y b
     in
     for i = 1 to nb_part - 1 do
       let y = !x + part_size in cmd i (y-1); x := y
     done;
     cmd nb_part (nb_proofs - 1);

     (* lp files generation *)
     out oc "\n.PHONY : lp\n";
     out oc "lp : %s.lp theory_hol.lp %s_types.lp %s_terms.lp %s_axioms.lp"
       b b b b;
     for i = 1 to nb_part do
       out oc " %s_part_%d_type_abbrevs.lp %s_part_%d_term_abbrevs.lp \
               %s_part_%d.lp" b i b i b i
     done;
     out oc "\n%s_types.lp %s_terms.lp %s_axioms.lp &: %s.sig\n\
             \thol2dk sig %s.lp\n" b b b b b;
     out oc "%s.lp : %s.sig %s.thm %s.pos %s.prf\n\
             \thol2dk thm %d %s.lp\n" b b b b b nb_part b;
     let x = ref 0 in
     let cmd i y =
       out oc "%s_part_%d.lp %s_part_%d_type_abbrevs.lp \
               %s_part_%d_term_abbrevs.lp &: %s.sig %s.pos %s.prf %s.use\n\
               \thol2dk part %d %d %d %d %s.lp\n"
         b i b i b i b b b b nb_part i !x y b
     in
     for i = 1 to nb_part - 1 do
       let y = !x + part_size in cmd i (y-1); x := y
     done;
     cmd nb_part (nb_proofs - 1);

     (* targets common to dk and lp files part *)
     out oc "\n%s.pos : %s.prf\n\thol2dk pos %s\n" b b b;
     out oc "%s.use : %s.sig %s.prf %s.thm\n\thol2dk use %s\n" b b b b b;

     (* generic function for lpo/vo file generation *)
     let check e c r =
       let s = if r = "" then "" else r ^ "o " in
       out oc "\n.PHONY : %so\n" e;
       out oc "%so : %s.%so\n" e b e;
       if r <> "" then out oc "theory_hol.%so : %so\n" e r;
       out oc "%s.%so : %stheory_hol.%so %s_types.%so %s_terms.%so \
               %s_axioms.%so" b e s e b e b e b e;
       for i = 1 to nb_part do out oc " %s_part_%d.%so" b i e done;
       out oc "\n%s_types.%so : %stheory_hol.%so\n" b e s e;
       out oc "%s_terms.%so : %stheory_hol.%so %s_types.%so\n" b e s e b e;
       out oc "%s_axioms.%so : %stheory_hol.%so %s_types.%so %s_terms.%so\n"
         b e s e b e b e;
       for i = 0 to nb_part - 1 do
         let j = i+1 in
         out oc "%s_part_%d_type_abbrevs.%so : %stheory_hol.%so %s_types.%so\n"
           b j e s e b e;
         out oc "%s_part_%d_term_abbrevs.%so : %stheory_hol.%so %s_types.%so \
                 %s_part_%d_type_abbrevs.%so %s_terms.%so\n"
           b j e s e b e b j e b e;
         out oc "%s_part_%d.%so : %stheory_hol.%so %s_types.%so \
                 %s_part_%d_type_abbrevs.%so %s_terms.%so \
                 %s_part_%d_term_abbrevs.%so %s_axioms.%so"
           b j e s e b e b j e b e b j e b e;
         for j = 0 to i - 1 do
           if dg.(i).(j) > 0 then out oc " %s_part_%d.%so" b (j+1) e
         done;
         out oc "\n"
       done;
       out oc "%%.%so : %%.%s\n\t%s $<\n" e e c
     in

     (* lp files checking *)
     check "lp" "lambdapi check -c" "";

     (* v files generation *)
     out oc "\n.PHONY : v\nv : %stheory_hol.v %s_types.v %s_terms.v"
       (if req = "" then "" else req ^ " ") b b;
     for i = 1 to nb_part do
       out oc " %s_part_%d_type_abbrevs.v %s_part_%d_term_abbrevs.v \
               %s_part_%d.v" b i b i b i
     done;
     out oc " %s.v\n" b;
     out oc "LAMBDAPI = lambdapi\n";
     out oc "%%.v : %%.lp\n\t$(LAMBDAPI) export -o stt_coq \
             --encoding encoding.lp --renaming renaming.lp \
             --erasing erasing.lp";
     if req <> "" then string oc (" --requiring " ^ req);
     out oc {| $< | sed -e 's/^Require Import hol-light\./Require Import /g'|};
     out oc " | sed -e 's/^Require /From HOLLight Require /' > $@\n";

     (* coq files checking *)
     check "v" "coqc" req;

     (* _CoqProject *)
     log "generate _CoqProject ...\n";
     let dump_file = "_CoqProject" in
     let oc = open_out dump_file in
     out oc "%stheory_hol.v\n%s_types.v\n%s_terms.v\n"
       (if req = "" then "" else req ^ "\n") b b;
     for i = 1 to nb_part do
       out oc "%s_part_%d_type_abbrevs.v\n%s_part_%d_term_abbrevs.v\n\
               %s_part_%d.v\n" b i b i b i
     done;
     out oc "%s.v\n" b;
     exit 0

let main() =
  match List.tl (Array.to_list Sys.argv) with

  | [] | ["-"|"--help"|"help"] -> usage(); exit 0

  | ["dep";f] ->
     let dg = dep_graph (files()) in
     log "%a\n" (list_sep " " string) (trans_file_deps dg f);
     exit 0

  | ["dep"] ->
     out_dep_graph stdout (dep_graph (files()));
     exit 0

  | ["name";f] ->
     log "%a\n" (list_sep "\n" string) (thms_of_file f);
     exit 0

  | ["name";"upto";f] ->
     let dg = dep_graph (files()) in
     List.iter
       (fun d -> List.iter (log "%s %s\n" d) (thms_of_file d))
       (trans_file_deps dg f);
     exit 0

  | ["name"] ->
     List.iter
       (fun f -> List.iter (log "%s %s\n" f) (thms_of_file f))
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
|} f b b (olist ostring) (trans_file_deps (dep_graph (files())) f);
        close_out oc;
        exit (Sys.command ("ocaml .dump.ml && mv -f .dump.prf "^b^".prf"))
     | _ -> wrong_arg()
     end

  | ["pos";basename] ->
     let nb_proofs = read_nb_proofs basename in
     let pos = Array.make nb_proofs 0 in
     let dump_file = basename ^ ".prf" in
     log "read %s ...\n%!" dump_file;
     let ic = open_in_bin dump_file in
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

  | ["stat";basename] ->
     let nb_proofs = read_nb_proofs basename in
     let thm_uses = Array.make nb_proofs 0 in
     let rule_uses = Array.make nb_rules 0 in
     read_prf basename
       (fun _ p -> count_thm thm_uses p; count_rule rule_uses p);
     log "compute statistics ...\n";
     print_histogram thm_uses;
     print_stats rule_uses nb_proofs;
     exit 0

  | ["use";basename] ->
     (* The .use file records an array uses such that uses[i] = 0 if
        i is a named theorem, the highest theorem index j>i using i if
        there is one, and -1 otherwise. *)
     let nb_proofs = read_nb_proofs basename in
     let uses = Array.make nb_proofs (-1) in
     read_prf basename
       (fun idx p -> List.iter (fun k -> Array.set uses k idx) (deps p));
     MapInt.iter (fun k _ -> Array.set uses k 0) (read_thm basename);
     let dump_file = basename ^ ".use" in
     log "generate %s ...\n" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc uses;
     close_out oc;
     exit 0

  | ["dg";nb_part;b] ->
     let nb_part = integer nb_part in
     if nb_part < 2 then wrong_arg();
     let nb_proofs = read_nb_proofs b in
     let part_size = nb_proofs / nb_part in
     let part idx =
       let k = idx / part_size in if k >= nb_part then k - 1 else k in
     (*let thdg = Array.make nb_part 0 in*)
     (*let map_thid_name = read_thm b in*)
     let dg = Array.init nb_part (fun i -> Array.make i 0) in
     let add_dep x =
       (*let named_thm = ref (MapInt.mem x map_thid_name) in*)
       let px = part x in
       fun y ->
       let py = part y in
       (*if !named_thm then thdg.(py) <- thdg.(py) + 1;*)
       if px <> py then
         begin
           (*log "add_dep %d (%d) %d (%d)\n" x (px+1) y (py+1);*)
           dg.(px).(py) <- dg.(px).(py) + 1
         end
     in
     read_prf b (fun idx p -> List.iter (add_dep idx) (deps p));
     for i = 1 to nb_part - 1 do
       log "%d:" (i+1);
       for j = 0 to i - 1 do
         if dg.(i).(j) > 0 then log " %d (%d)" (j+1) dg.(i).(j)
       done;
       log "\n"
     done;
     (*log "th:";
     for i = 0 to nb_part - 1 do
       if thdg.(i) > 0 then log " %d (%d)" (i+1) thdg.(i)
     done;
     log "\n";*)
     let dump_file = b ^ ".dg" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc dg;
     close_out oc;
     exit 0

  | ["mk";nb_part;b] -> make nb_part b ""
  | ["mk";nb_part;b;req] -> make nb_part b req

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
     let nb_part = integer nb_part in
     if nb_part < 2 then wrong_arg();
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     let map_thid_name = read_thm basename in
     read_pos basename;
     init_proof_reading basename;
     if dk then Xdk.export_theorems basename map_thid_name
     else Xlp.export_theorems_part nb_part basename map_thid_name

  | ["part";nb_part;k;x;y;f] ->
     let nb_part = integer nb_part in
     if nb_part < 2 then wrong_arg();
     let k = integer k in
     if k < 1 then wrong_arg();
     let x = integer x in
     if x < 0 then wrong_arg();
     let y = integer y in
     if y < x then wrong_arg();
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     read_pos basename;
     init_proof_reading basename;
     cur_part_max := k * (nb_proofs() / nb_part);
     if dk then
       begin
         Xdk.export_proofs_part basename k x y;
         let suffix = "_part_" ^ string_of_int k in
         Xdk.export_term_abbrevs basename suffix;
         Xdk.export_type_abbrevs basename suffix
       end
     else
       begin
         read_use basename;
         Xlp.export_proofs_part basename (read_val (basename ^ ".dg")) k x y;
         let suffix = "_part_" ^ string_of_int k in
         Xlp.export_term_abbrevs basename suffix;
         Xlp.export_type_abbrevs basename suffix
       end;
     exit 0

  | f::args ->
     let range =
       match args with
       | [] -> All
       | [x] ->
          let x = integer x in
          if x < 0 then wrong_arg();
          Only x
       | [x;y] ->
          let x = integer x in
          if x < 0 then wrong_arg();
          let y = integer y in
          if y < x then wrong_arg();
          Inter(x,y)
       | _ -> wrong_arg()
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
     init_proof_reading basename;
     if dk then
       begin
         Xdk.export_proofs basename range;
         if range = All then Xdk.export_theorems basename (read_thm basename);
         Xdk.export_term_abbrevs basename "";
         Xdk.export_type_abbrevs basename "";
         log "generate %s.dk ...\n%!" basename;
         let infiles =
           List.map (fun s -> basename ^ "_" ^ s ^ ".dk")
             (["types";"type_abbrevs";"terms";"term_abbrevs";"axioms"
              ;"proofs"] @ if range = All then ["theorems"] else [])
         in
         exit
           (Sys.command
              ("cat theory_hol.dk " ^ String.concat " " infiles
               ^ " > " ^ basename ^ ".dk"))
       end
     else
       begin
         Xlp.export_proofs basename range;
         if range = All then Xlp.export_theorems basename (read_thm basename);
         Xlp.export_term_abbrevs basename "";
         Xlp.export_type_abbrevs basename "";
         exit 0
       end

let _ = main()
