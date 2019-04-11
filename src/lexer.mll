{
  open Parser
  open Lexing

  let lex_context : (string, token) Hashtbl.t =
    let tb_size = 50 in
    Hashtbl.create tb_size
}

