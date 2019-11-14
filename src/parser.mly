%{
open Syntax
open Type

(* convert list to Idmap.t *)
let list_to_idmap (id_f : 'a -> identifier) (lst : 'a list) =
  List.fold_left (fun m x -> Idmap.add (id_f x) x m) Idmap.empty lst

(* split mixed definitions *)
let split_module_elems elems =
  List.fold_right (fun elem (cs, ns, subms) ->
    match elem with
    | MConst(d) -> (d::cs, ns, subms)
    | MNode(d) -> (cs, d::ns, subms)
    | MSubmodule(d) -> (cs, ns, d::subms)
  ) elems ([],[],[])

let split_state_elems elems =
  List.fold_right (fun elem (cs, ns, subms) ->
    match elem with
    | SConst(d) -> (d::cs, ns, subms)
    | SNode(d) -> (cs, d::ns, subms)
    | SSubmodule(d) -> (cs, ns, d::subms)
  ) elems ([],[],[])

let split_smodule_elems elems =
  List.fold_right (fun elem (cs, sts) ->
    match elem with
    | SMConst(d) -> (d::cs, sts)
    | SMState(d) -> (cs, d::sts)
  ) elems ([], [])

let split_file_elems elems =
  List.fold_right (fun elem (ts, cs, fs, ms, sms) ->
    match elem with
    | XFRPType(d) -> (d::ts, cs, fs, ms, sms)
    | XFRPConst(d) -> (ts, d::cs, fs, ms, sms)
    | XFRPFun(d) -> (ts, cs, d::fs, ms, sms)
    | XFRPModule(d) -> (ts, cs, fs, d::ms, sms)
    | XFRPSModule(d) -> (ts, cs, fs, ms, d::sms)
  ) elems ([],[],[],[],[])
%}

%token
MODULE SWITCHMODULE IN OUT USE INIT PUBLIC SHARED
CONST TYPE FUN STATE NODE NEW SWITCH
RETAIN LAST IF THEN ELSE LET CASE OF
TRUE FALSE

%token
LBRACE RBRACE LPAREN RPAREN
COMMA COLON SEMICOLON AT LARROW RARROW DOT
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

%start <Syntax.xfrp> xfrp

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

(* whole program *)
xfrp:
  | use = loption(use_clause)
    elems = nonempty_list(xfrp_elem)
    EOF
    {
      let (ts, cs, fs, ms, sms) = split_file_elems elems in
      let types = list_to_idmap (fun d -> d.type_id) ts in
      let consts = list_to_idmap (fun d -> d.const_id) cs in
      let funs = list_to_idmap (fun d -> d.fun_id) fs in
      let modules = list_to_idmap (fun d -> d.module_id) ms in
      let smodules = list_to_idmap (fun d -> d.smodule_id) sms in
      {
        xfrp_use = use;
        xfrp_types = types;
        xfrp_consts = consts;
        xfrp_funs = funs;
        xfrp_modules = modules;
        xfrp_smodules = smodules;
      }
    }

use_clause:
  | USE use = separated_nonempty_list(COMMA, UID)
    { use }

xfrp_elem:
  | pub = boption(PUBLIC) def = typedef
    {
      XFRPType({ def with type_pub = pub})
    }
  | pub = boption(PUBLIC) def = constdef
    {
      XFRPConst({ def with const_pub = pub})
    }
  | pub = boption(PUBLIC) def = fundef
    {
      XFRPFun({def with fun_pub = pub})
    }
  | pub = boption(PUBLIC) def = xfrp_module
    {
      XFRPModule({def with module_pub = pub})
    }
  | pub = boption(PUBLIC) def = xfrp_smodule
    {
      XFRPSModule({def with smodule_pub = pub})
    }

(* const *)
constdef:
  | CONST decl = id_and_type_opt EQUAL body = expression
    {
      let (id, t) = decl in
      {
        const_pub = false;
        const_id = id;
        const_type = t;
        const_body = body;
      }
    }

(* type *)
typedef:
  | TYPE id = UID EQUAL defs = separated_nonempty_list(OR, variant_def)
    {
      let conses =
        List.fold_right (fun (c, v) m -> Idmap.add c v m) defs Idmap.empty
      in
      { type_pub = false; type_id = id; type_conses = conses }
    }
variant_def:
  | c = UID v = preceded(OF, typespec)?
    {
      match v with
      | Some x -> (c, x)
      | None -> (c, TUnit)
    }

(* function *)
fundef:
  | FUN id = ID params = paren(separated_list(COMMA, id_and_type_opt))
    topt = preceded(COLON, typespec)? EQUAL body = expression
    {
      let t_params = List.map (fun (_, tvar) -> tvar) params in
      let t_ret =
        match topt with
        | Some(x) -> x
        | None -> TEmpty
      in
      let t_fun = TFun(t_params, t_ret) in
      {
        fun_pub = false;
        fun_id = id;
        fun_params = params;
        fun_type = t_fun;
        fun_body = body;
      }
    }

(* module header *)
in_node_decl:
  | IN in_nodes = separated_nonempty_list(COMMA, node_decl) { in_nodes }

out_node_decl:
  | OUT out_nodes = separated_nonempty_list(COMMA, node_decl) { out_nodes }

shared_node_decl:
  | SHARED shared_nodes = separated_list(COMMA, node_decl) { shared_nodes }


(* module *)
xfrp_module:
  | MODULE id = UID
    params = loption(paren(separated_list(COMMA, id_and_type)))
    LBRACE
    in_nodes = loption(in_node_decl)
    out_nodes = out_node_decl
    elems = nonempty_list(module_elem)
    RBRACE
    {
      let (cs, ns, subms) = split_module_elems elems in
      let consts = list_to_idmap (fun d -> d.const_id) cs in
      let nodes = list_to_idmap (fun d -> d.node_id) ns in
      let submodules = list_to_idmap (fun d -> d.submodule_id) subms in
      {
        module_pub = false;
        module_id = id;
        module_params = params;
        module_in = in_nodes;
        module_out = out_nodes;
        module_consts = consts;
        module_nodes = nodes;
        module_submodules = submodules;
        module_consts_ord = [];
        module_update_ord = [];
      }
    }

module_elem:
  | attr = nattr_normal? def = node
    {
      let def =
        match attr with
        | Some(x) -> { def with node_attr = x }
        | None -> def
      in
      MNode(def)
    }
  | def = submodule { MSubmodule(def) }
  | def = constdef { MConst(def) }

nattr_normal:
  | OUT { OutputNode }

(* switch module *)
xfrp_smodule:
  | SWITCHMODULE id = UID
    params = loption(paren(separated_list(COMMA, id_and_type)))
    LBRACE
    in_nodes = loption(in_node_decl)
    out_nodes = out_node_decl
    shared_nodes = loption(shared_node_decl)
    INIT init = expression
    elems = nonempty_list(smodule_elem)
    RBRACE
    {
      let (cs, sts) = split_smodule_elems elems in
      let consts = list_to_idmap (fun d -> d.const_id) cs in
      let states = list_to_idmap (fun d -> d.state_id) sts in
      {
        smodule_pub = false;
        smodule_id = id;
        smodule_params = params;
	smodule_in = in_nodes;
	smodule_out = out_nodes;
        smodule_shared = shared_nodes;
        smodule_init = init;
        smodule_consts = consts;
        smodule_states = states;
        smodule_consts_ord = [];
      }
    }

smodule_elem:
  | def = state { SMState(def) }
  | def = constdef { SMConst(def) }

state:
  | STATE id = UID
    params = loption(paren(separated_nonempty_list(COMMA, id_and_type)))
    LBRACE
    elems = nonempty_list(state_elem)
    SWITCH COLON switch = expression
    RBRACE
    {
      let (cs, ns, subms) = split_state_elems elems in
      let consts = list_to_idmap (fun d -> d.const_id) cs in
      let nodes = list_to_idmap (fun d -> d.node_id) ns in
      let submodules = list_to_idmap (fun d -> d.submodule_id) subms in
      {
        state_id = id;
        state_params = params;
        state_consts = consts;
        state_nodes = nodes;
        state_submodules = submodules;
        state_switch = switch;
        state_consts_ord = [];
        state_update_ord = [];
      }
    }

state_elem:
  | attr = nattr_switch? def = node
    {
      let def =
        match attr with
        | Some(x) -> { def with node_attr = x }
        | None -> def
      in
      SNode(def)
    }
  | def = submodule { SSubmodule(def) }
  | def = constdef { SConst(def) }

nattr_switch:
  | SHARED { SharedNode } | OUT { OutputNode }

(* node *)
node:
  | NODE id = ID
    init = paren(expression)?
    topt = preceded(COLON, typespec)?
    EQUAL body = expression
    {
      let t =
        match topt with
        | Some(x) -> x
        | None -> TEmpty
      in
      {
        node_attr = NormalNode;
        node_id = id;
        node_init = init;
        node_type = t;
        node_body = body;
      }
    }

submodule:
  | NEW bind_id = ID EQUAL
    module_id = UID margs = loption(paren(separated_list(COMMA, expression)))
    LARROW inputs = separated_nonempty_list(COMMA, expression)
    {
      {
        submodule_id = bind_id;
        submodule_module = module_id;
        submodule_margs = margs;
        submodule_inputs = inputs;
      }
    }

(* expressions *)
expression:
  | op = uni_op expr = expression
    %prec prec_uni
    { (EUniOp(op, expr), TEmpty) }
  | expr1 = expression op = bin_op expr2 = expression
    { (EBinOp(op, expr1, expr2), TEmpty) }
  | c = UID v = expression?
    {
      match v with
      | Some x -> (EVariant(c, x), TEmpty)
      | None ->
        let expr_unit = (EConst(LUnit), TEmpty) in
        (EVariant(c, expr_unit), TEmpty)
    }
  | expr = paren(separated_nonempty_list(COMMA, expression))
    {
      match expr with
      | [] -> assert false
      | [x] -> x
      | _ -> (ETuple(expr), TEmpty)
    }
  | expr = literal
    { (EConst(expr), TEmpty) }
  | RETAIN
    { (ERetain, TEmpty) }
  | expr = ID
    { (EId(expr), TEmpty) }
  | id = ID AT annot = annotation
    { (EAnnot(id, annot), TEmpty) }
  | id = ID DOT out = ID
    { (EDot(id, out), TEmpty) }
  | id = ID args = paren(separated_list(COMMA, expression))
    { (EFuncall(id, args), TEmpty) }
  | IF etest = expression THEN ethen = expression ELSE eelse = expression
    %prec prec_if
    { (EIf(etest, ethen, eelse), TEmpty) }
  | LET binders = separated_nonempty_list(SEMICOLON, binder) IN
    body = expression
    { (ELet(binders, body), TEmpty) }
  | CASE expr = expression OF branchs = branch+
    { (ECase(expr, branchs), TEmpty) }

binder:
  | id = id_and_type_opt EQUAL body = expression
    { { binder_id = id; binder_body = body } }

branch:
  | pat = pattern RARROW body = expression SEMICOLON
    { { branch_pat = pat; branch_body = body } }

pattern:
  | id = ID
    {
      match id with
      | "_" -> (PWild, TEmpty)
      | _ -> (PId(id), TEmpty)
    }
  | c = literal
    { (PConst(c), TEmpty) }
  | ps = paren(separated_nonempty_list(COMMA, pattern))
    {
      match ps with
      | [] -> assert false
      | [x] -> x
      | _ -> (PTuple(ps), TEmpty)
    }
  | c = UID v = pattern?
    {
      match v with
      | Some(x) -> (PVariant(c,x), TEmpty)
      | _ ->
        let pat_unit = (PConst(LUnit), TEmpty) in
        (PVariant(c, pat_unit), TEmpty)
    }

%inline
uni_op:
  | BANG { UNot } | TILDE { UInv }
  | PLUS { UPlus } | MINUS { UMinus }
  | PLUSDOT { UFPlus } | MINUSDOT { UFMinus }

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
        | None -> TEmpty
      in
      (id, t)
    }

node_decl:
  | id = ID init = paren(expression)? COLON t = typespec
    { (id, init, t) }

literal:
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
