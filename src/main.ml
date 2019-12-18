open Syntax
open Extension.Format

(*
let test_tsort ppf (progdata : Data.progdata) =
  Idmap.iter (fun _ sdef ->
      (pp_list_comma pp_identifier) ppf (Dependency.tsort_statenode sdef);
      pp_print_newline ppf ()
    ) progdata.sdefs
*)

exception FileError of string
exception ParseError of string

let parse filename =
  let () =
    if not (Sys.file_exists filename) then
      let msg = Printf.sprintf "File %s is not found" filename in
      raise (FileError msg)
    else ()
  in
  let ichan = open_in filename in
  let lexbuf = Lexing.from_channel ichan in
  try
    let res = Parser.xfrp Lexer.read lexbuf in
    close_in ichan; res
  with
  | Parser.Error ->
     let pos = lexbuf.lex_curr_p in
     let msg =
       Printf.sprintf "Syntax error in %s : Line %d, Char %d"
         filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
     in
     close_in_noerr ichan;
     raise (ParseError msg)
  | Check.Error(msg) ->
     raise (ParseError msg)
  | Dependency.Cycle ->
     let msg =
       Printf.sprintf "Detect cyclic dependency in %s" filename
     in
     close_in_noerr ichan;
     raise (ParseError msg)
  | e ->
     close_in_noerr ichan;
     raise e

type filestate = Visiting | Visited

let gather_filedata entry_file =
  let rec visit file (visit_state, all_data) =
    match Idmap.find_opt file visit_state with
    | None ->
       let filename = file ^ ".xfrp" in
       let ast = parse filename in
       let (visit_state, all_data) =
         List.fold_right visit ast.xfrp_use (visit_state, all_data)
       in
       let data = Typing.infer all_data file ast in
       let all_data =  Idmap.add file data all_data in
       let visit_state = Idmap.add file Visited visit_state in
       (visit_state, all_data)
    | Some(Visiting) -> raise (FileError "Detect cyclic file dependency")
    | Some(Visited) -> (visit_state, all_data)
  in
  let (_, all_data) = visit entry_file (Idmap.empty, Idmap.empty)  in
  all_data

let codegen entry_file all_data =
  let () =
    printf "%a" (pp_idmap pp_xfrp) all_data;
    print_newline ()
  in
  let metainfo = MetaInfo.get_metainfo entry_file all_data in
  printf "%a" MetaInfo.pp_metainfo metainfo;
  print_newline ()

let compile filename =
  try
    let ext = Filename.extension filename in
    let () =
      if ext = ".xfrp" then () else raise (FileError "Invalid file name")
    in
    let file = Filename.remove_extension filename in
    gather_filedata file |> codegen file
  with
  | ParseError msg | FileError msg
    -> printf "Compile Error : %s" msg;
       print_newline ()

let usage_msg =
  "[Usage] emfrp-switch [file]..."

let () =
  Arg.parse [] compile usage_msg


