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
------------

hol2dk [-h|--help]
  print this help

Dumping commands:
-----------------

hol2dk dump $file.[ml|hl]
  run OCaml toplevel to check $file.[ml|hl] and generate
  $file.sig (type and term constants), $file.prf (proof steps)
  and $file.thm (named theorems)

hol2dk dump-use $file.[ml|hl]
  same as hol2dk dump except that \"hol.ml\" is not loaded first

hol2dk pos $file
  generate $file.pos, the positions of proofs in $file.prf

Single-threaded dk/lp file generation:
--------------------------------------

hol2dk $file.[dk|lp]
  generate $file.[dk|lp]

hol2dk $file.[dk|lp] $thm_id
  generate $file.[dk|lp] but with theorem index $thm_id only (for debug)

Multi-threaded dk/lp file generation:
-------------------------------------

hol2dk dg $n $file
  generate $file.dg, the dependency graph of parts
  when $file.prf is split in $n parts

hol2dk mk $file
  generate $file.mk to generate, translate and check files in parallel

hol2dk sig $file
  generate dk/lp signature files from $file.sig

hol2dk thm $file.[dk|lp]
  generate $file.[dk|lp] from $file.thm

hol2dk axm $file.[dk|lp]
  generate $file_opam.[dk|lp] from $file.thm

hol2dk use $file
  generate $file.use, the number of times each proof step is used

hol2dk part $n $k $x $y $file.[dk|lp]
  generate dk/lp proof files of part $k in [1..$n]
  from proof index $x to proof index $y using type and term abbreviations

Experimental (not efficient):
-----------------------------

hol2dk prf $x $y $file
  generate a lp file for each proof from index $x to index $y in $file.prf
  without using type and term abbreviations

hol2dk mk-lp $jobs $file
  generate Makefile.lp for generating with the option -j $jobs a lp file
  (without type and term abbreviations) for each proof of $file.prf

hol2dk mk-coq $n $file
  generate a Makefile for translating to Coq each lp file generated
  by Makefile.lp and check them by using $n sequential calls to make

Other commands:
---------------

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
  log "read %s ...\n%!" dump_file;
  let nb_proofs = input_value ic in
  log "%d proof steps\n%!" nb_proofs;
  the_type_constants := List.rev (input_value ic);
  (* we add "el" to use mk_const without failing *)
  the_term_constants := ("el",aty)::List.rev (input_value ic);
  the_axioms := List.rev (input_value ic);
  the_definitions := List.rev (input_value ic);
  close_in ic;
  update_map_const_typ_vars_pos();
  update_reserved()

let read_thm basename =
  let map = read_val (basename ^ ".thm") in
  log "%d named theorems\n%!" (MapInt.cardinal map);
  map

let integer s = try int_of_string s with Failure _ -> wrong_arg()

(* [make b] generates a makefile for handling the proofs of [b] in
   parallel, according to the file [b.dg]. *)
let make b =
  let nb_proofs = read_nb_proofs b in

  let dump_file = b ^ ".dg" in
  log "read %s ...\n%!" dump_file;
  let ic = open_in_bin dump_file in
  let nb_parts = input_value ic in
  let dg = input_value ic in
  close_in ic;

  let dump_file = b ^ ".mk" in
  log "generate %s ...\n%!" dump_file;
  let oc = open_out dump_file in
  out oc "# file generated with: hol2dk mk %d %s\n" nb_parts b;
  out oc "\nLAMBDAPI = lambdapi\n";
  out oc "\n.SUFFIXES:\n";

  (* dk files generation *)
  out oc "\n.PHONY: dk\n";
  out oc "dk: %s.dk\n" b;
  out oc "%s.dk: theory_hol.dk %s_types.dk %s_terms.dk %s_axioms.dk"
    b b b b;
  for i = 1 to nb_parts do
    out oc " %s_part_%d_type_abbrevs.dk %s_part_%d_term_abbrevs.dk \
            %s_part_%d.dk" b i b i b i
  done;
  out oc " %s_theorems.dk\n\tcat $+ > $@\n" b;
  out oc "%s_types.dk %s_terms.dk %s_axioms.dk &: %s.sig\n\
          \thol2dk sig %s.dk\n" b b b b b;
  out oc "%s_theorems.dk: %s.sig %s.thm %s.pos %s.prf\n\
          \thol2dk thm %s.dk\n" b b b b b b;
  let cmd i x y =
    out oc "%s_part_%d.dk %s_part_%d_type_abbrevs.dk \
            %s_part_%d_term_abbrevs.dk &: %s.sig %s.prf %s.pos\n\
            \thol2dk part %d %d %d %s.dk\n" b i b i b i b b b i x y b
  in
  Xlib.iter_parts nb_proofs nb_parts cmd;
  out oc ".PHONY: clean-dk\nclean-dk:\n\trm -f %s*.dk\n" b;

  (* lp files generation *)
  out oc "\n.PHONY: lp\n";
  out oc "lp: theory_hol.lp %s.lp %s_types.lp %s_terms.lp \
          %s_axioms.lp %s_opam.lp" b b b b b;
  for i = 1 to nb_parts do
    out oc " %s_part_%d_type_abbrevs.lp %s_part_%d_term_abbrevs.lp \
            %s_part_%d.lp" b i b i b i
  done;
  out oc "\n%s_types.lp %s_terms.lp %s_axioms.lp &: %s.sig\n\
          \thol2dk sig %s.lp\n" b b b b b;
  out oc "%s.lp: %s.sig %s.thm %s.pos %s.prf\n\
          \thol2dk thm %s.lp\n" b b b b b b;
  let cmd i x y =
    out oc "%s_part_%d.lp %s_part_%d_type_abbrevs.lp \
            %s_part_%d_term_abbrevs.lp &: %s.sig %s.pos %s.prf %s.use\n\
            \thol2dk part %d %d %d %s.lp\n"
      b i b i b i b b b b i x y b
  in
  Xlib.iter_parts nb_proofs nb_parts cmd;
  out oc "%s_opam.lp: %s.sig %s.thm %s.pos %s.prf\n\
          \thol2dk axm %s.lp\n" b b b b b b;
  out oc ".PHONY: clean-lp\nclean-lp:\n\trm -f %s*.lp\n" b;

  (* targets common to dk and lp files part *)
  out oc "\n%s.pos: %s.prf\n\thol2dk pos %s\n" b b b;
  out oc "%s.use: %s.sig %s.prf %s.thm\n\thol2dk use %s\n" b b b b b;

  (* generic function for lpo/vo file generation *)
  let check e c clean =
    out oc "\n.PHONY: %so\n" e;
    out oc "%so: %s.%so\n" e b e;
    out oc "%s.%so: theory_hol.%so %s_types.%so \
            %s_terms.%so %s_axioms.%so %s_opam.%so" b e e b e b e b e b e;
    for i = 1 to nb_parts do out oc " %s_part_%d.%so" b i e done;
    out oc "\n%s_types.%so: theory_hol.%so\n" b e e;
    out oc "%s_terms.%so: theory_hol.%so %s_types.%so\n" b e e b e;
    out oc "%s_axioms.%so: theory_hol.%so %s_types.%so \
            %s_terms.%so\n" b e e b e b e;
    for i = 0 to nb_parts - 1 do
      let j = i+1 in
      out oc "%s_part_%d_type_abbrevs.%so: theory_hol.%so \
              %s_types.%so\n" b j e e b e;
      out oc "%s_part_%d_term_abbrevs.%so: \
              theory_hol.%so %s_types.%so %s_part_%d_\
              type_abbrevs.%so %s_terms.%so\n" b j e e b e b j e b e;
      out oc "%s_part_%d.%so: theory_hol.%so \
              %s_types.%so %s_part_%d_type_abbrevs.%so %s_terms.%so \
              %s_part_%d_term_abbrevs.%so %s_axioms.%so"
        b j e e b e b j e b e b j e b e;
      for j = 0 to i - 1 do
        if dg.(i).(j) > 0 then out oc " %s_part_%d.%so" b (j+1) e
      done;
      out oc "\n"
    done;
    out oc "%s_opam.%so: theory_hol.%so %s_types.%so %s_terms.%so \
            %s_axioms.%so\n" b e e b e b e b e;
    out oc "%%.%so: %%.%s\n\t%s $<\n" e e c;
    out oc
      ".PHONY: clean-%so\nclean-%so:\n\trm -f theory_hol.%so %s*.%so%a\n"
      e e e b e clean b;
  in

  (* lp files checking *)
  check "lp" "$(LAMBDAPI) check -c" (fun _ _ -> ());

  (* v files generation *)
  out oc "\n.PHONY: v\nv: coq.v theory_hol.v \
          %s_types.v %s_terms.v %s_axioms.v %s_opam.v" b b b b;
  for i = 1 to nb_parts do
    out oc " %s_part_%d_type_abbrevs.v %s_part_%d_term_abbrevs.v \
            %s_part_%d.v" b i b i b i
  done;
  out oc " %s.v\n" b;
  out oc "%%.v: %%.lp\n\t$(LAMBDAPI) export -o stt_coq \
          --encoding $(HOL2DK_DIR)/encoding.lp \
          --renaming $(HOL2DK_DIR)/renaming.lp \
          --erasing $(HOL2DK_DIR)/erasing.lp \
          --use-notations --requiring coq.v";
  out oc {| $< | sed -e 's/^Require Import hol-light\./Require Import /g'|};
  out oc " > $@\n";
  out oc ".PHONY: clean-v\nclean-v:\n\trm -f theory_hol.v %s*.v\n" b;

  (* coq files checking *)
  let clean oc _b = out oc " coq.vo *.vo[sk] *.glob .*.aux .[nl]ia.cache" in
  check "v" "coqc -R . HOLLight" clean;
  out oc "theory_hol.vo: coq.vo\n";

  (* clean-all target *)
  out oc "\n.PHONY: clean-all\nclean-all: \
          clean-dk clean-lp clean-lpo clean-v clean-vo\n";
  exit 0

let range args =
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
     if x=0 then Upto y else Inter(x,y)
  | _ -> wrong_arg()

let main() =
  match List.tl (Array.to_list Sys.argv) with

  | [] | ["-"|"--help"|"help"] -> usage()

  | ["dep";f] ->
     let dg = dep_graph (files()) in
     log "%a\n" (list_sep " " string) (trans_file_deps dg f)

  | ["dep"] ->
     out_dep_graph stdout (dep_graph (files()))

  | ["name";f] ->
     log "%a\n" (list_sep "\n" string) (thms_of_file f)

  | ["name";"upto";f] ->
     let dg = dep_graph (files()) in
     List.iter
       (fun d -> List.iter (log "%s %s\n" d) (thms_of_file d))
       (trans_file_deps dg f)

  | ["name"] ->
     List.iter
       (fun f -> List.iter (log "%s %s\n" f) (thms_of_file f))
       (files())

  | ["dump";f] ->
     begin match Filename.extension f with
     | ".ml" | ".hl" ->
        let b = Filename.chop_extension f in
        log "generate dump.ml ...\n%!";
        let oc = open_out "dump.ml" in
        out oc
{|(* file generated with: hol2dk dump %s *)
#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
#use "hol.ml";;
needs "%s";;
dump_signature "%s.sig";;
#load "str.cma";;
#use "xnames.ml";;
dump_map_thid_name "%s.thm" %a;;
|} f f b b (olist ostring) (trans_file_deps (dep_graph (files())) f);
        close_out oc;
        exit (Sys.command
                ("ocaml -w -A dump.ml && mv -f dump.prf "^b^"-origin.prf"))
     | _ -> wrong_arg()
     end

  | ["dump-use";f] ->
     begin match Filename.extension f with
     | ".ml" | ".hl" ->
        let b = Filename.chop_extension f in
        log "generate dump.ml ...\n%!";
        let oc = open_out "dump.ml" in
        out oc
{|(* file generated with: hol2dk dump-use %s *)
#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
#use "%s";;
dump_signature "%s.sig";;
#load "str.cma";;
#use "xnames.ml";;
dump_map_thid_name "%s.thm" %a;;
|} f f b b (olist ostring) (trans_file_deps (dep_graph (files())) f);
        close_out oc;
        exit (Sys.command ("ocaml -w -A dump.ml && mv -f dump.prf "^b^".prf"))
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
     output_value oc pos

  | ["stat";basename] ->
     let nb_proofs = read_nb_proofs basename in
     let thm_uses = Array.make nb_proofs 0 in
     let rule_uses = Array.make nb_rules 0 in
     read_prf basename
       (fun _ p -> count_thm_uses thm_uses p; count_rule_uses rule_uses p);
     log "compute statistics ...\n";
     print_histogram thm_uses;
     print_rule_uses rule_uses nb_proofs

  | ["nb-simps";basename] ->
     read_pos basename;
     read_use basename;
     init_proof_reading basename;
     let n = ref 0 in
     let simp k p =
       if Array.get !last_use k >= 0 then
       let Proof(_,c) = p in
       match c with
       | Ptrans(i,j) ->
          begin match proof_at i with
          | Proof(_,Prefl _) -> incr n
          | _ ->
             match proof_at j with
             | Proof(_,Prefl _) -> incr n
             | _ -> ()
          end
       | Psym i ->
          let Proof(_,c) = proof_at i in
          begin
            match c with
            | Prefl _
            | Psym _
            | Ptrans _ -> incr n
            | _ -> ()
          end
       | Pconjunct1 i | Pconjunct2 i ->
          begin match proof_at i with
          | Proof(_,Pconj _) -> incr n
          | _ -> ()
          end
       | Pmkcomb(i,j) ->
          begin match proof_at i with
          | Proof(_,Prefl _) ->
             begin match proof_at j with
             | Proof(_,Prefl _) -> incr n
             | _ -> ()
             end
          | _ -> ()
          end
       | _ -> ()
     in
     iter_proofs_at simp;
     let n = !n and total = nb_proofs() in
     log "%d simplifications (%d%%)\n" n ((100 * n) / total)

  | ["simp";b] ->
     let basename = b ^ "-origin" in
     read_pos basename;
     read_use basename;
     init_proof_reading basename;
     let dump_file = b ^ ".prf" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     let n = ref 0 in
     let map = ref MapInt.empty in
     let add i p = map := MapInt.add i p !map in
     let proof_at j = try MapInt.find j !map with Not_found -> proof_at j in
     let pc_at j = let Proof(_,c) = proof_at j in c in
     let simp k p =
       let default() = output_value oc p in
       let out pc =
         let p = change_proof_content p pc in
         incr n; add k p; output_value oc p
       in
       if Array.get !last_use k < 0 then out Ptruth else
       let Proof(_,c) = p in
       match c with
       | Ptrans(i,j) ->
          let pi = proof_at i and pj = proof_at j in
          let Proof(_,ci) = pi and Proof(_,cj) = pj in
          begin match ci, cj with
          | Prefl _, _ -> (* i:t=t j:t=u ==> k:t=u *) out cj
          | _, Prefl _ -> (* i:t=u j:u=u ==> k:t=u *) out ci
          | _ -> default()
          end
       | Psym i ->
          let pi = proof_at i in
          let Proof(_,ci) = pi in
          begin
            match ci with
            | Prefl _ -> (* i:t=t ==> k:t=t *) out ci
            | Psym j -> (* j:t=u ==> i:u=t ==> k:t=u *) out (pc_at j)
            | _ -> default()
          end
       | Pconjunct1 i ->
          begin match proof_at i with
          | Proof(_,Pconj(j,_)) -> (* j:p ==> i:p/\q ==> k:p *) out (pc_at j)
          | _ -> default()
          end
       | Pconjunct2 i ->
          begin match proof_at i with
          | Proof(_,Pconj(_,j)) -> (* j:q ==> i:p/\q ==> k:q *) out (pc_at j)
          | _ -> default()
          end
       | Pmkcomb(i,j) ->
          begin match proof_at i with
          | Proof(_,Prefl t) ->
             begin match proof_at j with
             | Proof(_,Prefl u) -> (* i:t=t j:u=u ==> k:tu=tu *)
                out (Prefl(mk_comb(t,u)))
             | _ -> default()
             end
          | _ -> default()
          end
       | _ -> default()
     in
     iter_proofs_at simp;
     let n = !n and total = nb_proofs() in
     log "%d simplifications (%d%%)\n" n ((100 * n) / total)

  | ["use";basename] ->
     (* The .use file records an array [last_use] such that
        [last_use.(i) = 0] if [i] is a named theorem, the highest
        theorem index using [i] if there is one, and -1 otherwise. *)
     let nb_proofs = read_nb_proofs basename in
     let last_use = Array.make nb_proofs (-1) in
     read_prf basename
       (fun idx p -> List.iter (fun k -> Array.set last_use k idx) (deps p));
     MapInt.iter (fun k _ -> Array.set last_use k 0) (read_thm basename);
     let dump_file = basename ^ ".use" in
     log "generate %s ...\n" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc last_use;
     let unused = ref 0 in
     Array.iter (fun k -> if k < 0 then incr unused) last_use;
     log "%d useless steps (%d%%)\n" !unused ((100 * !unused) / nb_proofs)

  | ["dg";nb_parts;b] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 2 then wrong_arg();
     let nb_proofs = read_nb_proofs b in
     let part_size = nb_proofs / nb_parts in
     let part idx =
       let k = idx / part_size in
       if k >= nb_parts - 1 then nb_parts - 1 else k in
     let dg = Array.init nb_parts (fun i -> Array.make i 0) in
     let add_dep x =
       let px = part x in
       fun y ->
       let py = part y in
       if px <> py then
         begin
           (*try*) dg.(px).(py) <- dg.(px).(py) + 1
           (*with (Invalid_argument _) as e ->
             log "x = %d, px = %d, y = %d, py = %d\n%!" x px y py;
             raise e*)
         end
     in
     read_prf b (fun idx p -> List.iter (add_dep idx) (deps p));
     for i = 1 to nb_parts - 1 do
       log "%d:" (i+1);
       for j = 0 to i - 1 do
         if dg.(i).(j) > 0 then log " %d (%d)" (j+1) dg.(i).(j)
       done;
       log "\n"
     done;
     let dump_file = b ^ ".dg" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc nb_parts;
     output_value oc dg

  | ["mk";b] -> make b

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
       end

  | ["thm";f] ->
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     let map_thid_name = read_thm basename in
     read_pos basename;
     init_proof_reading basename;
     if dk then Xdk.export_theorems basename map_thid_name
     else let nb_parts = read_val (basename ^ ".dg") in
          Xlp.export_theorems_part nb_parts basename map_thid_name

  | ["axm";f] ->
     let dk = is_dk f in
     let basename = Filename.chop_extension f in
     read_sig basename;
     let map_thid_name = read_thm basename in
     read_pos basename;
     init_proof_reading basename;
     if dk then Xdk.export_theorems_as_axioms basename map_thid_name
     else Xlp.export_theorems_as_axioms basename map_thid_name

  | ["part";k;x;y;f] ->
     let basename = Filename.chop_extension f in

     let dump_file = basename ^ ".dg" in
     log "read %s ...\n%!" dump_file;
     let ic = open_in_bin dump_file in
     let nb_parts = input_value ic in

     let k = integer k and x = integer x and y = integer y
     and nb_proofs = nb_proofs() in
     if k < 1 || k > nb_parts || x < 0 || y < x then wrong_arg();
     read_sig basename;
     read_pos basename;
     init_proof_reading basename;
     cur_part_max := (k * nb_proofs) / nb_parts;
     read_use basename;
     if is_dk f then
       begin
         Xdk.export_proofs_part basename k x y;
         let suffix = "_part_" ^ string_of_int k in
         Xdk.export_term_abbrevs basename suffix;
         Xdk.export_type_abbrevs basename suffix
       end
     else
       begin
         let dg = input_value ic in
         Xlp.export_proofs_part basename dg k x y;
         let suffix = "_part_" ^ string_of_int k in
         Xlp.export_term_abbrevs basename suffix;
         Xlp.export_type_abbrevs basename suffix
       end

  | ["prf";x;y;basename] ->
     let x = integer x and y = integer y and n = nb_proofs() in
     if x < 0 || y < 0 || x > y || x >= n || y >= n then wrong_arg();
     read_sig basename;
     read_pos basename;
     init_proof_reading basename;
     read_use basename;
     Xlp.export_one_file_by_prf basename x y

  | ["mk-lp";nb_parts;basename] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 1 then wrong_arg();
     read_pos basename;
     init_proof_reading basename;
     Xlp.gen_lp_makefile_one_file_by_prf basename (nb_proofs()) nb_parts

  | ["mk-coq";nb_parts;basename] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 1 then wrong_arg();
     read_pos basename;
     init_proof_reading basename;
     Xlp.gen_coq_makefile_one_file_by_prf basename (nb_proofs()) nb_parts

  | f::args ->
     let r = range args in
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
     read_use basename;
     if dk then
       begin
         Xdk.export_proofs basename r;
         if r = All then Xdk.export_theorems basename (read_thm basename);
         Xdk.export_term_abbrevs basename "";
         Xdk.export_type_abbrevs basename "";
         log "generate %s.dk ...\n%!" basename;
         let infiles =
           List.map (fun s -> basename ^ "_" ^ s ^ ".dk")
             (["types";"type_abbrevs";"terms";"term_abbrevs";"axioms"
              ;"proofs"] @ if r = All then ["theorems"] else [])
         in
         exit
           (Sys.command
              ("cat theory_hol.dk " ^ String.concat " " infiles
               ^ " > " ^ basename ^ ".dk"))
       end
     else
       begin
         Xlp.export_proofs basename r;
         if r = All then Xlp.export_theorems basename (read_thm basename);
         Xlp.export_term_abbrevs basename "";
         Xlp.export_type_abbrevs basename ""
       end

let _ = main()
