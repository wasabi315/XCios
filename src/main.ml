open Syntax
open Extension.Format

let test_tsort ppf (progdata : Data.progdata) =
  let tsort_node sdef =
    let id_and_exprs =
      List.fold_left (fun acc ndef ->
          let (id, _) = ndef.node_id in
          (id, ndef.node_body) :: acc
        ) [] sdef.nodes
    in
    Dependency.tsort_dependency id_and_exprs
  in
  Data.Idmap.iter (fun _ sdef ->
      (pp_list_comma pp_identifier) ppf (tsort_node sdef);
      pp_print_newline ppf ()
    ) progdata.sdef

let compile filename =
  let ichan = open_in filename in
  let lexbuf = Lexing.from_channel ichan in
  (try
     let prog = Parser.program Lexer.read lexbuf in
     let pdata = Data.of_progdata prog in
     Data.pp_progdata std_formatter pdata;
     pp_print_newline std_formatter ();
     test_tsort std_formatter pdata
   with
   | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      Printf.printf "Syntax error : Line %d, Char %d.\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1));
  close_in ichan

let usage_msg =
  "[Usage] emfrp-switch [file]..."

let () =
  Arg.parse [] compile usage_msg


