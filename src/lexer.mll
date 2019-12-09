{
  open Parser

  let lex_context : (string, token) Hashtbl.t =
    let tb_size = 50 in
    Hashtbl.create tb_size

  let () =
    List.iter (fun (id, tok) -> Hashtbl.add lex_context id tok)
      [
        "module",       MODULE;
        "switchmodule", SWITCHMODULE;
        "in",           IN;
        "out",          OUT;
        "use",          USE;
        "init",         INIT;
        "public",       PUBLIC;
        "shared",       SHARED;
        "const",        CONST;
        "type",         TYPE;
        "fun",          FUN;
        "newnode",      NEWNODE;
        "node",         NODE;
        "state",        STATE;
        "switch",       SWITCH;
        "Retain",       RETAIN;
        "last",         LAST;
        "if",           IF;
        "then",         THEN;
        "else",         ELSE;
        "let",          LET;
        "case",         CASE;
        "of",           OF;
        "True",         TRUE;
        "False",        FALSE;
      ]
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
let digits = ['0'-'9']+
let fliteral = ['0'-'9']+ '.' ['0'-'9']* | '.' ['0'-'9']+

(* longest match -> earlier rule *)
rule read = parse
  | space   { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | '#'     { read_comment lexbuf; read lexbuf }
  | '{'     { LBRACE }
  | '}'     { RBRACE }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | ','     { COMMA }
  | ':'     { COLON }
  | ';'     { SEMICOLON }
  | '@'     { AT }
  | "->"    { RARROW }
  | "<-"    { LARROW }
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
  | id
    {
      let s = Lexing.lexeme lexbuf in
        try
          Hashtbl.find lex_context s
        with Not_found ->
          if 'A' <= s.[0] && s.[0] <= 'Z' then UID s else ID s
    }
  | "()"     { UNIT }
  | digits   { INT (Lexing.lexeme lexbuf)}
  | fliteral { FLOAT (Lexing.lexeme lexbuf)}
  | eof      { EOF }
  | _        { assert false }
and read_comment = parse
  | '\n'    { Lexing.new_line lexbuf } (* comment end *)
  | eof     { () }                     (* comment end *)
  | _       { read_comment lexbuf }
