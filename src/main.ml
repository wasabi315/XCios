open Syntax
open Extension.Format

(*
let test_tsort ppf (progdata : Data.progdata) =
  Idmap.iter (fun _ sdef ->
      (pp_list_comma pp_identifier) ppf (Dependency.tsort_statenode sdef);
      pp_print_newline ppf ()
    ) progdata.sdefs
*)

exception ParseError of string
exception FileError of string

let parse filename =
  let () = print_string filename; print_newline () in
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
  | Parser.NameConflict(id) ->
     let msg =
       Printf.sprintf "Detect name confliction in %s : %s"
         filename id
     in
     close_in_noerr ichan;
     raise (ParseError msg)
  | e ->
     close_in_noerr ichan;
     raise e

let get_filedata _data_map ast = ast

type filestate = Visiting | Visited

let gather_filedata entry_file =
  let rec visit file (visit_state, data_map) =
    match Idmap.find_opt file visit_state with
    | None ->
       let ast = parse file in
       let use_files = List.map (fun f -> f ^ ".xfrp") ast.xfrp_use in
       let (visit_state, data_map) =
         List.fold_right visit use_files (visit_state, data_map)
       in
       let data = get_filedata data_map ast in
       let data_map =  Idmap.add file data data_map in
       let visit_state = Idmap.add file Visited visit_state in
       (visit_state, data_map)
    | Some(Visiting) -> raise (FileError "Detect cyclic file dependency")
    | Some(Visited) -> (visit_state, data_map)
  in
  let (_, data_map) = visit entry_file (Idmap.empty, Idmap.empty)  in
  data_map

let codegen data_map =
  Idmap.iter (fun id ast ->
      print_string id;
      print_newline ();
      pp_xfrp std_formatter ast;
      print_newline ();
    ) data_map

let compile file =
  try
    gather_filedata file |> codegen
  with
  | ParseError msg | FileError msg
    -> printf "Compile Error : %s" msg;
       print_newline ()

let usage_msg =
  "[Usage] emfrp-switch [file]..."

let () =
  Arg.parse [] compile usage_msg


