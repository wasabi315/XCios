%{
open Syntax
%}

%token
SWITCHMODULE IN OUT USE INIT
DATA TYPE FUNC STATE SWITCH NODE
RETAIN LAST IF THEN ELSE OF
TRUE FALSE

%token
LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN 
COMMA COLON AT ARROW 
PLUS MINUS ASTERISK SLASH
PLUSDOT MINUSDOT ASTERISKDOT SLASHDOT
TILDE PERCENT XOR OR2 AND2 OR AND
EQUAL2 NEQ LSHIFT LEQ LT
RSHIFT GEQ GT BANG EQUAL 

%token <string> ID
%token <int> INT
%token <float> FLOAT

%token EOF

%start <Syntax.switchmodule> switchmodule

%right prec_if
%left OR2
%left AND2
%left OR
%left XOR
%left AND
%left EQUAL2 NEQ
%left LT LEQ GT GEQ
%left LSHIFT RSHIFT
%left PLUS PLUSDOT MINUS MINUSDOT
%left ASTERISKDOT ASTERISK SLASH SLASHDOT PERCENT
%right prec_uni

%%

(* whole module *)
switchmodule:
  | SWITCHMODULE id = ID
    in_nodes = loption(in_node_decl)
    out_nodes = loption(out_node_decl)
    use = loption(use_decl)
    init = init_state_decl
    definitions = nonempty_list(definition)
    EOF
    {
      {
	in_nodes = in_nodes;
	out_nodes = out_nodes;
	use = use;
	init = init;
	definitions = definitions;
      }
    }

in_node_decl: 
  | IN inodes = separated_list(COMMA, in_node) { inodes }

in_node: 
  | id = ID init = delimited(LPAREN, literal, RPAREN)? COLON t = typespec
    { (id, init, t) }

out_node_decl: 
  | OUT out_nodes = separated_list(COMMA, id_and_type) 
    { out_nodes }

use_decl: 
  | USE use = separated_list(COMMA, ID) 
    { use }

init_state_decl: 
  | INIT id = ID LPAREN params = separated_list(COMMA, literal) RPAREN
    { (id, params) }


(* toplevel definitions *)
definition:
  | DATA signature = id_and_type_opt EQUAL body = expression
    { 
      let (id, topt) = signature in
      let def = { data_id = i; data_type = topt; data_body = expr } in
      DataDef def
    }
  | TYPE id = ID EQUAL constructors = separated_nonempty_list(OR, cons_definition)
    {
      let def = { type_id = id; constructors = constructors } in
      TypeDef def
    }
  | FUNC id = ID params = fparams
    t = preceded(COLON, typespec)? EQUAL body = expression
    {
      let def = 
	{ func_id = id; func_type = t; func_params = params; func_body = body } in
      FuncDef def
    }
  | STATE id = ID params = sparams LBRACE
    nodes = node_definition+ 
    SWITCH COLON switch = expression
    RBRACE
    {
      let def =
	{ state_id = id; state_params = params; nodes = nodes; switch = switch } in
      StateDef state
    }

cons_definition:
  | id = ID ts = delimited(LPAREN, separated_nonempty_list(COMMA, typespec), RPAREN)?
    { (id, ts) }

fparams: 
  | params = delimited(LPAREN, separated_list(COMMA, id_and_type_opt), RPAREN)
    { params }
sparams:
  | params = delimited(LPAREN, separated_list(COMMA, id_and_type), RPAREN)
    { params }

node_definition: 
  | NODE init = node_init? signature = id_and_type_opt EQUAL body = expression
    { 
      let (id, topt) = signature in
      { init = init; node_id = id; node_type = topt; node_body = body }
    }

node_init:
  | INIT init = delimited(LBRACKET, expression, RBRACKET)
    { init }


(* expressions *)
expression:
  | op = uni_op expr = expression 
    %prec prec_uni
    { EUniOp op expr }
  | expr1 = expression op = bin_op expr2 = expression
    { EBinOP op expr1 expr2 }
  | expr = delimited(LPAREN, separated_nonempty_list(COMMA, expression), RPAREN)
    { 
      match expr with
      | [] -> assert false
      | [x] -> x
      | _ -> ETuple expr
    }
  | expr = literal
    { EConst expr }
  | RETAIN
    { ERetain }
  | expr = ID
    { EID expr }
  | id = ID AT annot = annotation
    { EAnnot id annot }
  | id = ID args = delimited(LPAREN, separated_list(COMMA, expression), RPAREN)
    { EFuncall id args }
  | IF etest = expression THEN ethen = expression ELSE eelse = expression
    %prec prec_if
    { EIf etest ethen eelse}
  | LBRACE binds = binder+ body = expression RBRACE
    { ELet binds body }
  | expr = expression OF branchs = separated_nonempty_list(COMMA, match_branch)
    { EPat expr branchs }

binder:
  | signature = id_and_type_opt EQUAL body = expression
    { 
      let (id, topt) = signature in 
      { bind_id = id; bind_type = topt; bind_body = body }
    }

match_branch:
  | pat = pattern ARROW expr = expression
    { {branch_pat = pat; branch_expr = expr } }

pattern:
  | id = ID
    {
      match id with
      | "_" -> PWild
      | _ -> PId id
    }
  | c = literal
    { PConst c }
  | ps = delimited(LPAREN, separated_nonempty_list(COMMA, pattern), RPAREN)
    { PTuple ps }
  | id = ID ps = delimited(LPAREN, separated_nonempty_list(COMMA, pattern), RPAREN)
    { PADT id ps }

%inline
uni_op:
  | PLUS { UPos } | MINUS { UNeg } | BANG { UNot } | TILDE { UInv }

%inline
bin_op:
  | ASTERISK { BMul } | SLASH { BDiv }
  | PLUS { BAdd } | MINUS { BSub }
  | ASTERISKDOT { BFMul } | SLASHDOT { BFDiv }
  | PLUSDOT { BFAdd } | MINUSDOT { BFSub }
  | PERCENT { BMod } | LSHIFT { BShl } | RSHIFT { BShr }
  | LT { BLt } | LEQ { BLeq } | GT { BGt } | GEQ { BGeq }
  | EQUAL2 { BEq } | NEQ { BNeq }
  | AND2 { BLand } | OR2 { BLor }
  | AND { BAnd } | OR { Bor } | XOR { BXor }

annotation:
  | LAST { ALast }


(* primitives *)
id_and_type:
  | p = separated_pair(ID, COLON, typespec) { p }

id_and_type_opt:
  | id = ID topt = preceded(COLON, typespec)? { (id, topt) }

literal:
  | TRUE { LTrue }
  | FALSE { LFalse }
  | n = INT { LInt n }
  | n = FLOAT { LFloat n }

typespec:
  | id = ID
    {
      match id with 
      | "Bool" -> TBool
      | "Int" -> TInt
      | "Float" -> TFloat
      | _ -> TID id
    }
  | ts = delimited(LPAREN, separated_nonempty_list(COMMA, typespec), RPAREN)
    { TTuple ts }
