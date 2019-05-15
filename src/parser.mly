%{
open Syntax
open Type
%}

%token
MODULE SWITCHMODULE IN OUT USE INIT
CONST TYPE FUN NODE STATE SWITCH
RETAIN LAST IF THEN ELSE LET CASE OF
TRUE FALSE

%token
LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
COMMA COLON SEMICOLON AT ARROW
PLUS MINUS ASTERISK SLASH
PLUSDOT MINUSDOT ASTERISKDOT SLASHDOT
TILDE PERCENT XOR OR2 AND2 OR AND
EQUAL2 NEQ LSHIFT RSHIFT
LEQ LT GEQ GT
LEQDOT LTDOT GEQDOT GTDOT
BANG EQUAL

%token <string> ID
%token <string> UID

%token <string> INT
%token <string> FLOAT
%token UNIT

%token EOF

%start <Syntax.program> program

%right prec_if
%left OR2
%left AND2
%left OR
%left XOR
%left AND
%left EQUAL2 NEQ
%left LT LEQ GT GEQ LEQDOT LTDOT GEQDOT GTDOT
%left LSHIFT RSHIFT
%left PLUS PLUSDOT MINUS MINUSDOT
%left ASTERISKDOT ASTERISK SLASH SLASHDOT PERCENT
%right prec_uni

%%
paren(rule):
  | ret = delimited(LPAREN, rule, RPAREN) { ret }


program:
  | m = xfrp_module { XfrpModule(m) }
  | m = xfrp_smodule { XfrpSModule(m) }

(* whole module *)
xfrp_module:
  | MODULE id = UID
    in_nodes = loption(in_node_decl)
    out_nodes = loption(out_node_decl)
    use = loption(use_decl)
    definitions = nonempty_list(definitionM)
    EOF
    {
      {
        module_id = id;
	module_in = in_nodes;
	module_out = out_nodes;
	module_use = use;
	module_defs = definitions;
      }
    }

xfrp_smodule:
  | SWITCHMODULE id = UID
    in_nodes = loption(in_node_decl)
    out_nodes = loption(out_node_decl)
    use = loption(use_decl)
    init = init_decl
    definitions = nonempty_list(definitionSM)
    EOF
    {
      {
        smodule_id = id;
	smodule_in = in_nodes;
	smodule_out = out_nodes;
	smodule_use = use;
	smodule_init = init;
	smodule_defs = definitions;
      }
    }

in_node_decl:
  | IN inodes = separated_list(COMMA, node_decl) { inodes }

out_node_decl:
  | OUT onodes = separated_list(COMMA, node_decl) { onodes }

node_decl:
  | id = ID init = paren(literal)? COLON t = typespec
    { (id, init, t) }

use_decl:
  | USE use = separated_list(COMMA, UID)
    { use }

init_decl:
  | INIT id = UID param = literal?
    {
      match param with
      | Some x -> (id, x)
      | None -> (id, LUnit)
    }

(* toplevel definitions *)
definitionM:
  | d = const_definition { MConstDef(d) }
  | d = type_definition { MTypeDef(d) }
  | d = fun_definition { MFunDef(d) }
  | d = node_definition { MNodeDef(d) }

definitionSM:
  | d = const_definition { SMConstDef(d) }
  | d = type_definition { SMTypeDef(d) }
  | d = fun_definition { SMFunDef(d) }
  | d = state_definition { SMStateDef(d) }

const_definition:
  | CONST id = id_and_type_opt EQUAL body = expression
    {
      { const_id = id; const_body = body }
    }

type_definition:
  | TYPE id = UID EQUAL defs = separated_nonempty_list(OR, variant_definition)
    {
      { type_id = id; variant_defs = defs }
    }
variant_definition:
  | c = ID v = preceded(OF, typespec)?
    {
      match v with
      | Some x -> (c, x)
      | None -> (c, TUnit)
    }

fun_definition:
  | FUN id = ID params = paren(separated_list(COMMA, id_and_type_opt))
    topt = preceded(COLON, typespec)? EQUAL body = expression
    {
      let t_params = List.map (fun (_, tvar) -> tvar) params in
      let t_ret =
        match topt with
        | Some(x) -> x
        | None -> gen_tvar_dummy ()
      in
      let fun_type = TFun(t_params, t_ret) in
      { fun_id = (id, fun_type); fun_params = params; fun_body = body }
    }

node_definition:
  | NODE init = node_init? id = id_and_type_opt EQUAL body = expression
    {
      { init = init; node_id = id; node_body = body }
    }
node_init:
  | INIT init = delimited(LBRACKET, literal, RBRACKET)
    { init }

state_definition:
  | STATE id = UID
    params = loption(paren(separated_nonempty_list(COMMA, id_and_type)))
    LBRACE
    nodes = node_definition+
    SWITCH COLON switch = expression
    RBRACE
    {
      { state_id = id; state_params = params; nodes = nodes; switch = switch }
    }

(* expressions *)
expression:
  | op = uni_op expr = expression
    %prec prec_uni
    { EUniOp(op, expr) }
  | expr1 = expression op = bin_op expr2 = expression
    { EBinOp(op, expr1, expr2) }
  | c = UID v = expression?
    {
      match v with
      | Some x -> EVariant(c, x)
      | None -> EVariant(c, EConst(LUnit))
    }
  | expr = paren(separated_nonempty_list(COMMA, expression))
    {
      match expr with
      | [] -> assert false
      | [x] -> x
      | _ -> ETuple(expr)
    }
  | expr = prim_literal
    { EConst(expr) }
  | RETAIN
    { ERetain }
  | expr = ID
    { EId(expr) }
  | id = ID AT annot = annotation
    { EAnnot(id, annot) }
  | id = ID args = paren(separated_list(COMMA, expression))
    { EFuncall(id, args) }
  | IF etest = expression THEN ethen = expression ELSE eelse = expression
    %prec prec_if
    { EIf(etest, ethen, eelse) }
  | LET binders = separated_nonempty_list(SEMICOLON, binder) IN
    body = expression
    { ELet(binders, body) }
  | CASE expr = expression OF branchs = branch+
    { ECase(expr, branchs) }

binder:
  | id = id_and_type_opt EQUAL body = expression
    { { binder_id = id; binder_body = body } }

branch:
  | pat = pattern ARROW body = expression SEMICOLON
    { { branch_pat = pat; branch_body = body } }

pattern:
  | id = ID
    {
      match id with
      | "_" -> PWild
      | _ -> PId(id)
    }
  | c = prim_literal
    { PConst(c) }
  | ps = paren(separated_nonempty_list(COMMA, pattern))
    {
      match ps with
      | [] -> assert false
      | [x] -> x
      | _ -> PTuple(ps)
    }
  | c = UID v = pattern?
    {
      match v with
      | Some(x) -> PADT(c,x)
      | _ -> PADT(c, PConst(LUnit))
    }

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
  | LTDOT { BFLt } | LEQDOT { BFLeq } | GTDOT { BFGt } | GEQDOT { BFGeq }
  | EQUAL2 { BEq } | NEQ { BNeq }
  | AND2 { BLand } | OR2 { BLor }
  | AND { BAnd } | OR { BOr } | XOR { BXor }

annotation:
  | LAST { ALast }

(* primitives *)
id_and_type:
  | p = separated_pair(ID, COLON, typespec) { p }

id_and_type_opt:
  | id = ID topt = preceded(COLON, typespec)?
    {
      let t =
        match topt with
        | Some(x) -> x
        | None -> gen_tvar_dummy ()
      in
      (id, t)
    }

literal:
  | l = prim_literal { l }
  | l = paren(separated_nonempty_list(COMMA, literal))
    {
      match l with
      | [] -> assert false
      | [x] -> x
      | _ -> LTuple(l) }
  | c = UID v = literal?
    {
      match v with
      | Some x -> LVariant(c, x)
      | None -> LVariant(c, LUnit)
    }

prim_literal:
  | TRUE { LTrue }
  | FALSE { LFalse }
  | UNIT { LUnit }
  | n = INT { LInt(n) }
  | n = FLOAT { LFloat(n) }

typespec:
  | id = UID
    {
      match id with
      | "Bool" -> TBool
      | "Int" -> TInt
      | "Float" -> TFloat
      | _ -> TId(id)
    }
  | ts = paren(separated_nonempty_list(COMMA, typespec))
    { TTuple(ts) }
