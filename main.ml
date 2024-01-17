(* Main program for translating HOL-Light proofs to Dedukti or Lambdapi. *)

open Fusion
open Xlib
open Xprelude
open Xproof
open Xfiles
open Xnames

let usage() =
  log
"hol2dk uses
------------

hol2dk [-h|--help]
  print this help

Dumping commands
----------------

hol2dk dump-simp $file.[ml|hl]
  compose the commands dump, pos, use, rewrite and purge
  for $file depending on hol.ml

hol2dk dump-use-simp $file.[ml|hl]
  same as hol2dk dump except that hol.ml is not loaded first

hol2dk dump $file.[ml|hl]
  run OCaml toplevel to check $file.[ml|hl] and generate
  $file.sig (type and term constants), $file.prf (proof steps)
  and $file.thm (named theorems)

hol2dk dump-use $file.[ml|hl]
  same as hol2dk dump except that hol.ml is not loaded first

hol2dk pos $file
  generate $file.pos, the positions of proofs in $file.prf

hol2dk use $file
  generate $file.use, some data to know whether a theorem is used or not

hol2dk rewrite $file
  simplify $file.prf and update $file.pos and $file.use

hol2dk purge $file
  compute theorems that can be discarded in $file.use

hol2dk proof $file $x $y
  print proof steps between theorem indexes $x and $y

hol2dk print use $file $x
  print the contents of $file.use for theorem index $x

Single-threaded dk/lp file generation
-------------------------------------

hol2dk $file.[dk|lp]
  generate $file.[dk|lp]

hol2dk $file.[dk|lp] $thm_id
  generate $file.[dk|lp] but with theorem index $thm_id only (for debug)

Multi-threaded dk/lp file generation by splitting proofs in $n parts
--------------------------------------------------------------------

hol2dk mk $n $file
  generate $file.dg, the dependency graph between parts when $file.prf is
  split in $n parts, and $file.mk for handling parts in parallel

hol2dk part $k $x $y $file.[dk|lp]
  generate dk/lp proof files of part $k from proof index $x to proof index $y

hol2dk sig $file
  generate dk/lp signature files from $file.sig

hol2dk thm $file.[dk|lp]
  generate $file.[dk|lp] from $file.thm

hol2dk axm $file.[dk|lp]
  generate $file_opam.[dk|lp] from $file.thm (same as thm but without proofs)

Multi-threaded lp file generation by having a file for each named theorem
-------------------------------------------------------------------------

hol2dk split $file
  generate $file.thp and the files $t.sti, $t.pos and $t.use
  for each named theorem $t

hol2dk theorem $file $t.lp
  generate the lp proof of the theorem named $t

Experimental (not efficient)
----------------------------

hol2dk prf $x $y $file
  generate a lp file for each proof from index $x to index $y in $file.prf
  without using type and term abbreviations

hol2dk mk-lp $jobs $file
  generate Makefile.lp for generating with the option -j $jobs a lp file
  (without type and term abbreviations) for each proof of $file.prf

hol2dk mk-coq $n $file
  generate a Makefile for translating to Coq each lp file generated
  by Makefile.lp and check them by using $n sequential calls to make

Other commands
--------------

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

let percent k n = (100 * k) / n

let wrong_arg() = Printf.eprintf "wrong argument(s)\n%!"; exit 1

let is_dk filename =
  match Filename.extension filename with
  | ".dk"  -> true
  | ".lp" -> false
  | _ -> wrong_arg()

let read_sig b =
  let dump_file = b ^ ".sig" in
  let ic = open_in_bin dump_file in
  log "read %s ...\n%!" dump_file;
  the_type_constants := List.rev (input_value ic);
  (* we add "el" to use mk_const without failing *)
  the_term_constants := ("el",aty)::List.rev (input_value ic);
  the_axioms := List.rev (input_value ic);
  the_definitions := List.rev (input_value ic);
  close_in ic;
  update_map_const_typ_vars_pos();
  update_reserved()

let integer s = try int_of_string s with Failure _ -> wrong_arg()

(* [make nb_proofs dg b] generates a makefile for translating the
   proofs of [b] in parallel, according to the dependency graph
   between parts [dg]. *)
let make nb_proofs dg b =
  let nb_parts = Array.length dg in
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
        if dg.(i).(j) then out oc " %s_part_%d.%so" b (j+1) e
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
  check "lp" "$(LAMBDAPI) check -v0 -w -c" (fun _ _ -> ());

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
  close_out oc;
  0

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

let dump after_hol f b =
  let ml_file = Printf.sprintf "/tmp/dump%d.ml" (Unix.getpid()) in
  log "generate %s ...\n%!" ml_file;
  let oc = open_out ml_file in
  let use oc after_hol =
    if after_hol then out oc "#use \"hol.ml\";;\nneeds \"%s\";;" f
    else out oc "#use \"%s\";;" f
  in
  let cmd oc after_hol =
    if after_hol then out oc " dump" else out oc " dump-use" in
  out oc
{|(* file generated with: hol2dk%a %s *)
#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
#require "unix";;
%a
close_out oc_dump;;
Sys.command ("mv "^dump_filename^" %s.prf");;
dump_nb_proofs "%s.nbp";;
dump_signature "%s.sig";;
#load "str.cma";;
#use "xnames.ml";;
dump_map_thid_name "%s.thm" %a;;
|} cmd after_hol f use after_hol b b b b
(olist ostring) (trans_file_deps (dep_graph (files())) f);
  close_out oc;
  Sys.command ("ocaml -w -A -I . "^ml_file)

let basename_ml f =
  match Filename.extension f with
  | ".ml" | ".hl" -> Filename.chop_extension f
  | _ -> wrong_arg()

let rec log_command l =
  log "\nhol2dk"; List.iter (log " %s") l; log " ...\n"; command l

and dump_and_simp after_hol f =
  let b = basename_ml f in
  match dump after_hol f b with
  | 0 -> begin match log_command ["pos";b] with
         | 0 -> begin match log_command ["use";b] with
                | 0 -> command ["simp";b]
                | e -> e
                end
         | e -> e
         end
  | e -> e

and command = function
  | [] | ["-"|"--help"|"help"] -> usage(); 0

  | ["dep";f] ->
     let dg = dep_graph (files()) in
     log "%a\n" (list_sep " " string) (trans_file_deps dg f);
     0

  | ["dep"] ->
     out_dep_graph stdout (dep_graph (files()));
     0

  | ["name";f] ->
     log "%a\n" (list_sep "\n" string) (thms_of_file f);
     0

  | ["name";"upto";f] ->
     let dg = dep_graph (files()) in
     List.iter
       (fun d -> List.iter (log "%s %s\n" d) (thms_of_file d))
       (trans_file_deps dg f);
     0

  | ["name"] ->
     List.iter
       (fun f -> List.iter (log "%s %s\n" f) (thms_of_file f))
       (files());
     0

  | ["dump";f] -> dump true f (basename_ml f)
  | ["dump-use";f] -> dump false f (basename_ml f)
  | ["dump-simp";f] -> dump_and_simp true f
  | ["dump-use-simp";f] -> dump_and_simp false f

  | ["pos";b] ->
     let nb_proofs = read_val (b ^ ".nbp") in
     let pos = Array.make nb_proofs 0 in
     let dump_file = b ^ ".prf" in
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
     let dump_file = b ^ ".pos" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc pos;
     close_out oc;
     0

  | ["stat";b] ->
     let nb_proofs = read_val (b ^ ".nbp") in
     let thm_uses = Array.make nb_proofs 0 in
     let rule_uses = Array.make nb_rules 0 in
     let unused = ref 0 in
     read_use b;
     let f k p =
       if Array.get !Xproof.last_use k >= 0 then
         (count_thm_uses thm_uses p; count_rule_uses rule_uses p)
       else incr unused
     in
     read_prf b f;
     log "compute statistics ...\n";
     print_histogram thm_uses;
     print_rule_uses rule_uses (nb_proofs - !unused);
     0

  | ["stat";b;s] ->
     let nb_proofs = read_val (s ^ ".nbp") in
     let thm_uses = Array.make nb_proofs 0 in
     let rule_uses = Array.make nb_rules 0 in
     let unused = ref 0 in
     read_use s;
     let dump_file = b ^ ".prf" in
     log "read %s ...\n%!" dump_file;
     let ic = open_in_bin dump_file in
     the_start_idx := read_val (s ^ ".sti");
     read_pos b;
     seek_in ic (get_pos !the_start_idx);
     let f k p =
       if Array.get !Xproof.last_use k >= 0 then
         (count_thm_uses thm_uses p; count_rule_uses rule_uses p)
       else incr unused
     in
     for k = 0 to nb_proofs - 1 do f k (input_value ic) done;
     close_in ic;
     log "compute statistics ...\n";
     print_histogram thm_uses;
     print_rule_uses rule_uses (nb_proofs - !unused);
     0

  | ["proof";b;x;y] ->
     let x = integer x and y = integer y in
     let nb_proofs = read_val (b ^ ".nbp") in
     if x < 0 || y < x || y >= nb_proofs then wrong_arg();
     read_pos b;
     init_proof_reading b;
     read_use b;
     let map_thid_name = read_val (b ^ ".thm") in
     for k = x to y do
       log "%8d: %a" k proof (proof_at k);
       begin match Array.get !Xproof.last_use k with
       | 0 -> (try log " (named %s)" (MapInt.find k map_thid_name)
               with Not_found -> assert false)
       | n -> if n < 0 then log " (unused)"
       end;
       log "\n"
     done;
     close_in !Xproof.ic_prf;
     0

  | ["proof";b;x] -> command ["proof";b;x;x]

  | ["rewrite";b] ->
     read_pos b;
     init_proof_reading b;
     read_use b;
     let dump_file = b ^ "-simp.prf" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     (* count the number of simplications *)
     let n = ref 0 in
     (* map from theorem indexes to their new proofs *)
     let map = ref MapInt.empty in
     let add i c = map := MapInt.add i c !map in
     let pc_at j =
       match MapInt.find_opt j !map with
       | Some c -> c
       | None -> content_of (proof_at j)
     in
     (* simplification of proof p at index k *)
     let simp k p =
       let default() = output_value oc p in
       let l = Array.get !last_use k in
       if l < 0 then default() else
       let out c = incr n; add k c; output_value oc (change_content p c) in
       begin match content_of p with
       | Ptrans(i,j) ->
          let ci = pc_at i and cj = pc_at j in
          begin match ci, cj with
          | Prefl _, _ -> (* i:t=t j:t=u ==> k:t=u *) out cj
          | _, Prefl _ -> (* i:t=u j:u=u ==> k:t=u *) out ci
          | _ -> default()
          end
       | Psym i ->
          let ci = pc_at i in
          begin match ci with
          | Prefl _ -> (* i:t=t ==> k:t=t *) out ci
          | Psym j -> (* j:t=u ==> i:u=t ==> k:t=u *) out (pc_at j)
          | _ -> default()
          end
       | Pconjunct1 i ->
          begin match pc_at i with
          | Pconj(j,_) -> (* j:p ==> i:p/\q ==> k:p *) out (pc_at j)
          | _ -> default()
          end
       | Pconjunct2 i ->
          begin match pc_at i with
          | Pconj(_,j) -> (* j:q ==> i:p/\q ==> k:q *) out (pc_at j)
          | _ -> default()
          end
       | Pmkcomb(i,j) ->
          begin match pc_at i with
          | Prefl t ->
             begin match pc_at j with
             | Prefl u -> (* i:t=t j:u=u ==> k:tu=tu *)
                out (Prefl(mk_comb(t,u)))
             | _ -> default()
             end
          | _ -> default()
          end
       | Peqmp(i,j) ->
          begin match pc_at i with
          | Prefl _ -> (* i:p=p j:p ==> k:p *) out (pc_at j)
          | _ -> default()
          end
       | _ -> default()
       end;
       (* we can empty the map since the proofs coming after a named
          theorem cannot refer to proofs coming before it *)
       if l = 0 then map := MapInt.empty
     in
     for k = 0 to Array.length !prf_pos - 1 do simp k (proof_at k) done;
     close_in !Xproof.ic_prf;
     close_out oc;
     let nb_proofs = Array.length !prf_pos in
     log "%d simplifications (%d%%)\n" !n (percent !n nb_proofs);
     (* replace file.prf by file-simp.prf, and recompute file.pos and
        file.use *)
     log "replace %s.prf by %s-simp.prf ...\n" b b;
     begin match Sys.command (Printf.sprintf "mv %s-simp.prf %s.prf" b b) with
     | 0 ->
        begin match log_command ["pos";b] with
        | 0 -> log_command ["use";b]
        | e -> e
        end
     | e -> e
     end

  | ["purge";b] ->
     (* compute useful theorems *)
     read_pos b;
     init_proof_reading b;
     let map_thid_name = read_val (b ^ ".thm") in
     let nb_proofs = Array.length !prf_pos in
     let useful = Array.make nb_proofs false in
     let rec mark_as_useful = function
       | [] -> ()
       | k::ks ->
          if useful.(k) then mark_as_useful ks
          else begin
              useful.(k) <- true;
              mark_as_useful (List.rev_append (deps (proof_at k)) ks)
            end
     in
     MapInt.iter (fun k _ -> mark_as_useful [k]) map_thid_name;
     close_in !Xproof.ic_prf;
     (* update file.use *)
     read_use b;
     let nb_useless = ref nb_proofs in
     Array.iteri
       (fun k b ->
         if b then decr nb_useless else Array.set !Xproof.last_use k (-1))
       useful;
     let dump_file = b ^ ".use" in
     log "generate %s ...\n" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc !Xproof.last_use;
     log "%d useless theorems (%d%%)\n"
       !nb_useless (percent !nb_useless nb_proofs);
     0

  | ["simp";b] ->
     begin match log_command ["rewrite";b] with
     | 0 -> log_command ["purge";b]
     | e -> e
     end

  | ["use";b] ->
     (* The .use file records an array [last_use] such that
        [last_use.(i) = 0] if [i] is a named theorem, the highest
        theorem index using [i] if there is one, and -1 otherwise. *)
     let nb_proofs = read_val (b ^ ".nbp") in
     let last_use = Array.make nb_proofs (-1) in
     read_prf b
       (fun i p -> List.iter (fun k -> Array.set last_use k i) (deps p));
     MapInt.iter (fun k _ -> Array.set last_use k 0) (read_val (b ^ ".thm"));
     let dump_file = b ^ ".use" in
     log "generate %s ...\n" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc last_use;
     let unused = ref 0 in
     Array.iter (fun n -> if n < 0 then incr unused) last_use;
     log "%d unused theorems (including named theorems) (%d%%)\n"
       !unused (percent !unused nb_proofs);
     close_out oc;
     let first = ref (-1) in
     let exception Found in
     (try Array.iteri
            (fun i j -> if j < 0 then (first := i; raise Found)) last_use
      with Found -> ());
     log "first unused: %d\n" !first;
     0

  | ["print";"use";b;k] ->
     let k = integer k in
     let nb_proofs = read_val (b ^ ".nbp") in
     if k < 0 || k >= nb_proofs then wrong_arg();
     read_use b;
     log "%d\n" (Array.get !Xproof.last_use k);
     0

  | ["mk";nb_parts;b] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 2 then wrong_arg();
     let nb_proofs = read_val (b ^ ".nbp") in
     let part_size = nb_proofs / nb_parts in
     let part idx =
       let k = idx / part_size in
       if k >= nb_parts - 1 then nb_parts - 1 else k in
     let dg = Array.init nb_parts (fun i -> Array.make i false) in
     let add_dep x =
       let px = part x in
       fun y ->
       let py = part y in
       if px <> py then
         begin
           (*try*) dg.(px).(py) <- true (*dg.(px).(py) + 1*)
           (*with (Invalid_argument _) as e ->
             log "x = %d, px = %d, y = %d, py = %d\n%!" x px y py;
             raise e*)
         end
     in
     read_use b;
     let f k p =
       if Array.get !Xproof.last_use k >= 0 then
         List.iter (add_dep k) (deps p)
     in
     read_prf b f;
     for i = 1 to nb_parts - 1 do
       log "%d:" (i+1);
       for j = 0 to i - 1 do
         (*if dg.(i).(j) > 0 then log " %d (%d)" (j+1) dg.(i).(j)*)
         if dg.(i).(j) then log " %d" (j+1)
       done;
       log "\n"
     done;
     let dump_file = b ^ ".dg" in
     log "generate %s ...\n%!" dump_file;
     let oc = open_out_bin dump_file in
     output_value oc nb_parts;
     output_value oc dg;
     close_out oc;
     make nb_proofs dg b

  | ["sig";f] ->
     let dk = is_dk f in
     let b = Filename.chop_extension f in
     read_sig b;
     if dk then
       begin
         Xdk.export_types b;
         Xdk.export_terms b;
         Xdk.export_axioms b
       end
     else
       begin
         Xlp.export_types b;
         Xlp.export_terms b;
         Xlp.export_axioms b
       end;
     0

  | ["thm";f] ->
     let dk = is_dk f in
     let b = Filename.chop_extension f in
     read_sig b;
     let map_thid_name = read_val (b ^ ".thm") in
     read_pos b;
     init_proof_reading b;
     begin
       if dk then Xdk.export_theorems b map_thid_name
       else let nb_parts = read_val (b ^ ".dg") in
            Xlp.export_theorems_part nb_parts b map_thid_name
     end;
     close_in !Xproof.ic_prf;
     0

  | ["axm";f] ->
     let dk = is_dk f in
     let b = Filename.chop_extension f in
     read_sig b;
     let map_thid_name = read_val (b ^ ".thm") in
     read_pos b;
     init_proof_reading b;
     begin
       if dk then Xdk.export_theorems_as_axioms b map_thid_name
       else Xlp.export_theorems_as_axioms b map_thid_name
     end;
     close_in !Xproof.ic_prf;
     0

  | ["part";k;x;y;f] ->
     let b = Filename.chop_extension f in

     let dump_file = b ^ ".dg" in
     log "read %s ...\n%!" dump_file;
     let ic = open_in_bin dump_file in
     let nb_parts = input_value ic in

     let k = integer k and x = integer x and y = integer y in
     if k < 1 || k > nb_parts || x < 0 || y < x then wrong_arg();
     read_sig b;
     let suffix = "_part_" ^ string_of_int k in
     read_pos b;
     init_proof_reading b;
     read_use b;
     if is_dk f then
       begin
         Xdk.export_proofs_part b k x y;
         Xdk.export_term_abbrevs b suffix;
         Xdk.export_type_abbrevs b suffix
       end
     else
       begin
         (* used in xlp to know whether a theorem can be declared as private *)
         cur_part_max := y;
         let dg = input_value ic in
         Xlp.export_proofs_part b dg k x y;
         Xlp.export_term_abbrevs b b suffix;
         Xlp.export_type_abbrevs b b suffix
       end;
     close_in ic;
     close_in !Xproof.ic_prf;
     0

  | ["split";b] ->
     read_pos b;
     read_use b;
     (*init_proof_reading b;*)
     let map_thid_name = read_val (b ^ ".thm") in
     let map = ref MapInt.empty in
     let create_segment start_index end_index =
       let n = try MapInt.find end_index map_thid_name
               with Not_found -> "thm" ^ string_of_int end_index in
       let len = end_index - start_index + 1 in
       write_val (n ^ ".nbp") len;
       write_val (n ^ ".sti") start_index;
       write_val (n ^ ".pos") (Array.sub !prf_pos start_index len);
       write_val (n ^ ".use") (Array.sub !last_use start_index len);
       let p = Array.get !prf_pos end_index in
       map := MapInt.add end_index (n,p) !map;
       (*let dump_file = n ^ ".prf" in
       log "write %s ...\n%!" dump_file;
       let oc = open_out_bin dump_file in
       seek_in !ic_prf (get_pos start_index);
       for _k = 1 to len do
         let p : proof = input_value !ic_prf in
         output_value oc p
       done;
       close_out oc*)
     in
     let end_idx = ref (Array.length !prf_pos - 1) in
     while Array.get !last_use !end_idx < 0 do decr end_idx done;
     for k = !end_idx - 1 downto 0 do
       let l = Array.get !last_use k in
       if l = 0 || l > !end_idx then
         begin
           create_segment (k+1) !end_idx;
           end_idx := k
         end
     done;
     create_segment 0 !end_idx;
     MapInt.iter (fun i (n,_) -> log "%d %s\n" i n) !map;
     write_val (b ^ ".thp") !map;
     0

  | ["theorem";b;f] ->
     read_sig b;
     map_thid_pos := read_val (b ^ ".thp");
     let n = Filename.chop_extension f in
     read_pos n;
     read_use n;
     the_start_idx := read_val (n ^ ".sti");
     (*log "the_start_idx = %d\n%!" !the_start_idx;*)
     init_proof_reading b;
     if is_dk f then
       begin
         log "dk output not available for this command"; 1
       end
     else
       begin
         cur_part_max := !the_start_idx + Array.length !prf_pos - 1;
         Xlp.export_proofs b n All;
         close_in !Xproof.ic_prf;
         Xlp.export_term_abbrevs b n "";
         Xlp.export_type_abbrevs b n "";
         let dump_file = n ^ "_deps.lp" in
         log "generate %s ...\n%!" dump_file;
         let oc = open_out dump_file in
         SetStr.iter (out oc "require open hol-light.%s;\n") !thdeps;
         close_out oc;
         log "generate %s.lp ...\n%!" n;
         Sys.command (Printf.sprintf "cat %s %s > %s && rm -f %s %s"
                        (n^"_deps.lp") (n^"_proofs.lp") (n^".lp")
                        (n^"_deps.lp") (n^"_proofs.lp"))
       end

  | ["prf";x;y;b] ->
     read_sig b;
     read_pos b;
     let x = integer x and y = integer y
         and nb_proofs = Array.length !prf_pos in
     if x < 0 || y < 0 || x > y || x >= nb_proofs || y >= nb_proofs then
       wrong_arg();
     init_proof_reading b;
     read_use b;
     Xlp.export_one_file_by_prf b x y;
     close_in !Xproof.ic_prf;
     0

  | ["mk-lp";nb_parts;b] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 1 then wrong_arg();
     read_pos b;
     let nb_proofs = Array.length !prf_pos in
     init_proof_reading b;
     Xlp.gen_lp_makefile_one_file_by_prf b nb_proofs nb_parts;
     close_in !Xproof.ic_prf;
     0

  | ["mk-coq";nb_parts;b] ->
     let nb_parts = integer nb_parts in
     if nb_parts < 1 then wrong_arg();
     read_pos b;
     let nb_proofs = Array.length !prf_pos in
     init_proof_reading b;
     Xlp.gen_coq_makefile_one_file_by_prf b nb_proofs nb_parts;
     close_in !Xproof.ic_prf;
     0

  | f::args ->
     let r = range args in
     let dk = is_dk f in
     let b = Filename.chop_extension f in
     (* read and translate sig file *)
     read_sig b;
     if dk then
       begin
         Xdk.export_types b;
         Xdk.export_terms b;
         Xdk.export_axioms b;
       end
     else
       begin
         Xlp.export_types b;
         Xlp.export_terms b;
         Xlp.export_axioms b
       end;
     read_pos b;
     init_proof_reading b;
     read_use b;
     if dk then
       begin
         Xdk.export_proofs b r;
         if r = All then Xdk.export_theorems b (read_val (b ^ ".thm"));
         Xdk.export_term_abbrevs b "";
         Xdk.export_type_abbrevs b "";
         log "generate %s.dk ...\n%!" b;
         let infiles =
           List.map (fun s -> b ^ "_" ^ s ^ ".dk")
             (["types";"type_abbrevs";"terms";"term_abbrevs";"axioms"
              ;"proofs"] @ if r = All then ["theorems"] else [])
         in
         exit
           (Sys.command
              ("cat theory_hol.dk " ^ String.concat " " infiles
               ^ " > " ^ b ^ ".dk"))
       end
     else
       begin
         Xlp.export_proofs b b r;
         if r = All then Xlp.export_theorems b (read_val (b ^ ".thm"));
         Xlp.export_term_abbrevs b b "";
         Xlp.export_type_abbrevs b b ""
       end;
     close_in !Xproof.ic_prf;
     0

let _ =
  (*Memtrace.trace_if_requested ();*)
  exit (command (List.tl (Array.to_list Sys.argv)))
