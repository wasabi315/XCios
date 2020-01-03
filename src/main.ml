open Syntax
open MetaInfo
open Extension.Format

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
     close_in_noerr ichan;
     raise (ParseError msg)
  | e ->
     close_in_noerr ichan;
     raise e

type filestate = Visiting | Visited

let gather_filedata entry_file =
  let rec visit file acc =
    let (visit_state, _, _) = acc in
    match Idmap.find_opt file visit_state with
    | None ->
       let filename = file ^ ".xfrp" in
       let ast = parse filename in
       let (visit_state, all_data, file_ord_rev) =
         List.fold_right visit ast.xfrp_use acc
       in
       let data = Typing.infer all_data file ast in
       let visit_state = Idmap.add file Visited visit_state in
       let all_data =  Idmap.add file data all_data in
       let file_ord_rev = file :: file_ord_rev in
       (visit_state, all_data, file_ord_rev)
    | Some(Visiting) -> raise (FileError "Detect cyclic file dependency")
    | Some(Visited) -> acc
  in
  let (_, all_data, file_ord_rev) =
    visit entry_file (Idmap.empty, Idmap.empty, [])
  in
  (all_data, List.rev file_ord_rev)

let get_metainfo entry_file (all_data, file_ord) =
  let filedata = Idmap.find entry_file all_data in
  let () =
    match Idmap.find_opt "Main" filedata.xfrp_all with
    | Some (XFRPModule _) | Some (XFRPSModule _) -> ()
    | _ -> raise (FileError "Main module not found")
  in
  let used_materials = GatherUsed.gather all_data entry_file in
  let metainfo =
    metainfo_empty entry_file
    |> AllElements.get_all_elements all_data file_ord used_materials
    |> ModuleData.calc_moduledata
    |> Alloc.calc_alloc_amount all_data
    |> TypeData.calc_typedata all_data file_ord
  in
  metainfo

let generate_main entry_file metainfo =
  printf "@[<v>" ;
  printf "%a" GenDataType.generate metainfo;
  printf "@,%a" GenMemory.generate metainfo;
  printf "@,%a" GenGlobal.generate (entry_file, metainfo);
  printf "@,%a" GenFun.generate metainfo;
  printf "@]"

let codegen entry_file metainfo =
  printf "%a@." pp_metainfo metainfo;
  generate_main entry_file metainfo

let compile path =
  try
    let basename = Filename.basename path in
    let ext = Filename.extension basename in
    let () =
      if ext = ".xfrp" then () else raise (FileError "Invalid file name")
    in
    let dir = Filename.dirname path in
    let () = Sys.chdir dir in
    let file = Filename.remove_extension basename in
    gather_filedata file |> get_metainfo file |> codegen file
  with
  | ParseError msg | FileError msg
    -> printf "Compile Error : %s" msg;
       print_newline ()

let usage_msg =
  "[Usage] emfrp-switch [file]..."

let () =
  Arg.parse [] compile usage_msg
