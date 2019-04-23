let usage_msg =
  "[Usage] emfrp-switch [file]..."

let compile filename =
  let ichan = open_in filename in
  let lexbuf = Lexing.from_channel ichan in
  (try
     let prog = Parser.switchmodule Lexer.read lexbuf in
     Codegen.codegen stdout prog
   with
   | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      Printf.printf "Syntax error : Line %d, Char %d."
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1));
  close_in ichan

let () =
  Arg.parse [] compile usage_msg
