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

let parse filename =
  let ichan = open_in filename in
  let lexbuf = Lexing.from_channel ichan in
  try
    let res = Parser.xfrp Lexer.read lexbuf in
    close_in ichan; res
  with
  | Parser.Error ->
     let pos = lexbuf.lex_curr_p in
     let mes =
       Printf.sprintf "Syntax error in %s : Line %d, Char %d."
         filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
     in
     close_in_noerr ichan;
     raise (ParseError mes)
  | e ->
     close_in_noerr ichan;
     raise e

(*
let compile filename =
  let ichan = open_in filename in
  let lexbuf = Lexing.from_channel ichan in
  (try
     let prog = Parser.program Lexer.read lexbuf in
     let pdata = Data.of_progdata prog in
     let pdata = Typing.infer_progdata pdata in
     Data.pp_progdata std_formatter pdata;
     pp_print_newline std_formatter ();
     test_tsort std_formatter pdata
   with
   | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      Printf.printf "Syntax error : Line %d, Char %d.\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1));
  close_in ichan
 *)

let run filename =
  let ast = parse filename in
  pp_xfrp std_formatter ast

let usage_msg =
  "[Usage] emfrp-switch [file]..."

let () =
  Arg.parse [] run usage_msg


