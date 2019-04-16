{
  open Parser

  let lex_context : (string, token) Hashtbl.t =
    let tb_size = 50 in
    Hashtbl.create tb_size

  let () =
    List.iter (fun (id, tok) -> Hashtbl.add id tok)
      [
        "switchmodule", SWITCHMODULE;
        "in",           IN;
        "out",          OUT;
        "use",          USE;
        "init",         INIT;
        "data",         DATA;
        "type",         TYPE;
        "func",         FUNC;
        "state",        STATE;
        "switch",       SWITCH;
        "node",         NODE;
        "Retain",       RETAIN;
        "last",         LAST;
        "if",           IF;
        "then",         THEN;
        "else",         ELSE;
        "of",           OF;
        "True",         TRUE;
        "False",        FALSE;
      ]
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
let digits = ['0'-'9']+
let fdigits = (['0'-'9']+ '.' ['0'-'9']* | '.' ['0'-'9']+)
              (['e' 'E'] ['+' '-']? ['0'-'9']+)?

(* longest match -> earlier rule *)
rule read = parse
  | space   { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | '#'     { read_comment lexbuf; read lexbuf }
  | '['     { LBRACKET }
  | ']'     { RBRACKET }
  | '{'     { LBRACE }
  | '}'     { RBRACE }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | ','     { COMMA }
  | ':'     { COLON }
  | '@'     { AT }
  | "->"    { ARROW }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '*'     { ASTERISK }
  | '/'     { SLASH }
  | "+."    { PLUSDOT }
  | "-."    { MINUSDOT }
  | "*."    { ASTERISKDOT }
  | "/."    { SLASHDOT }
  | '~'     { TILDE }
  | '%'     { PERCENT }
  | '^'     { XOR }
  | "||"    { OR2 }
  | "&&"    { AND2 }
  | '|'     { OR }
  | '&'     { AND }
  | "=="    { EQUAL2 }
  | "!="    { NEQ }
  | "<="    { LEQ }
  | '<'     { LT }
  | ">="    { GEQ }
  | '>'     { GT }
  | "<=."   { LEQDOT }
  | "<."    { LTDOT }
  | ">=."   { GEQDOT }
  | ">."    { GTDOT }
  | "<<"    { LSHIFT }
  | ">>"    { RSHIFT }
  | '!'     { BANG }
  | '='     { EQUAL }
  | id {
      let s = Lexing.lexeme lexbuf in
        try
          Hashtbl.find lex_context s
        with Not_found ->
          Id s
    }
  | digits  { INT (int_of_string (Lexing.lexeme lexbuf))}
  | fdigits { FLOAT (float_of_string (Lexing.lexeme lexbuf))}
  | eof     { EOF }
  | _       { assert false }
and read_comment = parse
  | '\n'    { Lexing.new_line lexbuf } (* comment end *)
  | eof     { () }                     (* comment end *)
  | _       { read_comment lexbuf }
