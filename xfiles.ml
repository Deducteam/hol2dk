open Xprelude;;
open Xlib;;

(* [files()] computes the list of HOL-Light files in the current
   directory and its subdirectories recursively. *)
let files() : string list =
  let rec walk acc = function
  | [] -> acc
  | dir::tail ->
     let contents = Array.to_list (Sys.readdir dir) in
     let dirs, files =
       List.fold_left
         (fun (dirs,files) f ->
           try
             if f <> "" && f.[0] = '.' then (dirs, files) else
             if Filename.check_suffix f ".ml"
                || Filename.check_suffix f ".hl" then
               let f = if dir = "." then f else Filename.concat dir f in
               (dirs, f::files)
             else
               (*FIXME:temporary hack to avoid following links*)
               if f = "_opam" then (dirs, files) else
               let f = if dir = "." then f else Filename.concat dir f in
               (*Unix.(match (stat f).st_kind with
               | S_DIR -> (f::dirs, files)
               | _ -> (dirs, files))*)
               if Sys.is_directory f then (f::dirs, files)
               else (dirs, files)
           with Sys_error _ -> (dirs, files))
         ([],[]) contents
     in
     walk (files @ acc) (dirs @ tail)
  in walk [] ["."]
;;

(* [dep_graph files] computes the dependency graph of [files]. *)
let dep_graph =
  let re =
    Str.regexp "\\(load[st]\\|needs\\|#use\\)[ \t]+\"\\([^.]+.[mh]l\\)\"" in
  let search content =
    let rec search acc start =
      try
        let _ = Str.search_forward re content start in
        search (Str.matched_group 2 content :: acc) (Str.match_end())
      with _ -> acc
    in List.rev (search [] 0)
  in
  fun (files : string list) : string list MapStr.t ->
  List.fold_left
    (fun map filename ->
      MapStr.add filename (search (string_of_file filename)) map)
    MapStr.empty files
;;

(* [out_dep_graph oc dg] prints on [oc] the dependency graph [dg] in
   the Makefile format. *)
let out_dep_graph oc dg =
  MapStr.iter
    (fun name deps -> out oc "%s:%a\n" name (list_prefix " " string) deps)
    dg;
;;

(* [file_deps dg f] returns the immediate dependencies of [f] in [dg]. *)
let file_deps dg filename = try MapStr.find filename dg with Not_found -> [];;

(* [trans_deps dg f] returns all the dependencies of [f] in [dg],
   recursively. *)
let trans_file_deps dg filename =
  let rec trans visited to_visit =
    match to_visit with
    | [] -> List.rev visited
    | f::to_visit ->
       if List.mem f visited then trans visited to_visit
       else (*trans (f::visited) (file_deps dg f @ to_visit)*)
         let fs = file_deps dg f in
         if List.for_all (fun f -> List.mem f visited) fs then
           trans (f :: visited) to_visit
         else trans visited (fs @ f :: to_visit)
  in trans [] [filename]
;;

(* unit test *)
let _ =
  let dg =
    List.fold_left (fun dg (f,deps) -> MapStr.add f deps dg) MapStr.empty
      ["a",["b";"c"]; "b",["d";"e"]; "c",["f";"g"]]
  in
  assert (trans_file_deps dg "a" = ["d";"e";"b";"f";"g";"c";"a"])
