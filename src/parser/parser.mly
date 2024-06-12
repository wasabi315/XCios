%{
open Syntax
open Type
open Dependency
open Check

(* Generate fresh identifier *)
let id_counter = ref 0

let gensym () =
  id_counter := !id_counter + 1;
  "#" ^ (string_of_int !id_counter)

(* Convert list to Idmap.t. *)
let list_to_idmap (id_f : 'a -> identifier) (lst : 'a list) =
  List.fold_left (fun m x -> Idmap.add (id_f x) x m) Idmap.empty lst

(* Split mixed definitions. *)
let split_module_elems elems =
  List.fold_right (fun elem (cs, ns, newns) ->
    match elem with
    | MConst(d) -> (d::cs, ns, newns)
    | MNode(d) -> (cs, d::ns, newns)
    | MNewnode(d) -> (cs, ns, d::newns)
  ) elems ([],[],[])

let split_state_elems elems =
  List.fold_right (fun elem (cs, ns, newns) ->
    match elem with
    | SConst(d) -> (d::cs, ns, newns)
    | SNode(d) -> (cs, d::ns, newns)
    | SNewnode(d) -> (cs, ns, d::newns)
  ) elems ([],[],[])

let split_smodule_elems elems =
  List.fold_right (fun elem (cs, sts) ->
    match elem with
    | SMConst(d) -> (d::cs, sts)
    | SMState(d) -> (cs, d::sts)
  ) elems ([], [])

let split_file_elems elems =
  List.fold_right (fun elem (ts, mds, cs, fs, ms, sms) ->
    match elem with
    | XFRPType(d) -> (d::ts, mds, cs, fs, ms, sms)
    | XFRPMode(d) -> (ts, d::mds, cs, fs, ms, sms)
    | XFRPConst(d) -> (ts, mds, d::cs, fs, ms, sms)
    | XFRPFun(d) -> (ts, mds, cs, d::fs, ms, sms)
    | XFRPModule(d) -> (ts, mds, cs, fs, d::ms, sms)
    | XFRPSModule(d) -> (ts, mds, cs, fs, ms, d::sms)
  ) elems ([],[],[],[],[],[])
%}

%token
MODULE SWITCHMODULE IN OUT USE INIT PUBLIC SHARED
CONST TYPE FUN ORDERED MODE ACC STATE NODE NEWNODE WITH SWITCH
RETAIN LAST IF THEN ELSE LET CASE OF
TRUE FALSE

%token
LBRACE RBRACE LPAREN RPAREN
COMMA COLON SEMICOLON AT QUOTE LARROW RARROW
PLUS MINUS ASTERISK SLASH
PLUSDOT MINUSDOT ASTERISKDOT SLASHDOT
TILDE PERCENT XOR OR2 AND2 OR AND
EQUAL2 NEQ LSHIFT RSHIFT
LEQ LT GEQ GT
LEQDOT LTDOT GEQDOT GTDOT
BANG EQUAL

%token <string> ID
%token <string> UID

%token <int> INT
%token <float> FLOAT
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
      let () = check_name_conflict_file elems in
      let (ts, mds, cs, fs, ms, sms) = split_file_elems elems in
      let types = list_to_idmap (fun d -> d.type_id) ts in
      let modes = list_to_idmap (fun d -> d.mode_id) mds in
      let consts = list_to_idmap (fun d -> d.const_id) cs in
      let funs = list_to_idmap (fun d -> d.fun_id) fs in
      let modules = list_to_idmap (fun d -> d.module_id) ms in
      let smodules = list_to_idmap (fun d -> d.smodule_id) sms in
      let all = list_to_idmap xfrp_elem_id elems in
      {
        xfrp_use = use;
        xfrp_types = types;
        xfrp_modes = modes;
        xfrp_consts = consts;
        xfrp_funs = funs;
        xfrp_modules = modules;
        xfrp_smodules = smodules;
        xfrp_all = all;
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
  | pub = boption(PUBLIC) def = modedef
    {
      XFRPMode({ def with mode_pub = pub})
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

(* mode *)
accessibility:
  | (* empty *) { Inacc }
  | ACC { Acc }

modedef:
  | MODE id = UID EQUAL modevs = separated_nonempty_list(OR, pair(accessibility, UID))
  {
    { mode_pub = false
    ; mode_id = id
    ; mode_vals = List.to_seq modevs |> Seq.map (fun (acc, modev) -> (modev, acc)) |> Idmap.of_seq
    ; mode_val_ord = None
    }
  }
  | ORDERED MODE id = UID EQUAL modevs = omode_value_defs
  {
    let inacc_modevs , acc_modevs = modevs in
    let mode_val_ord = inacc_modevs @ acc_modevs in
    let inacc_modevs =
      inacc_modevs
      |> List.to_seq
      |> Seq.map (fun modev -> (modev, Inacc))
    in
    let acc_modevs =
      acc_modevs
      |> List.to_seq
      |> Seq.map (fun modev -> (modev, Acc))
    in
    { mode_pub = false
    ; mode_id = id
    ; mode_vals = Idmap.of_seq (Seq.append inacc_modevs acc_modevs)
    ; mode_val_ord = Some(mode_val_ord)
    }
  }

omode_value_defs:
  | (* empty *)
    { [], [] }
  | mode = UID
    { [mode], [] }
  | ACC acc_modes = separated_list(pair(LT, ACC), UID)
    { [], acc_modes }
  | mode = UID LT modes = omode_value_defs
    {
      let modes , acc_modes = modes in
      mode :: modes, acc_modes
    }

(* function *)
fundef:
  | FUN id = ID params = paren(separated_list(COMMA, id_and_type_opt))
    topt = preceded(COLON, typespec)? EQUAL body = expression
    {
      let tret =
        match topt with
        | Some(x) -> x
        | None -> TEmpty
      in
      {
        fun_pub = false;
        fun_id = id;
        fun_params = params;
        fun_rettype = tret;
        fun_body = body;
      }
    }

(* module header *)
in_node_decl:
  | IN in_nodes = separated_nonempty_list(COMMA, io_node_decl) { in_nodes }

out_node_decl:
  | OUT out_nodes = separated_nonempty_list(COMMA, io_node_decl) { out_nodes }

shared_node_decl:
  | SHARED shared_nodes = separated_list(COMMA, node_decl) { shared_nodes }

mode_annot:
  | id = ID EQUAL mode = UID { id, ModeAnnotEq (mode, UnknownId) }
  | id = ID GEQ mode = UID { id, ModeAnnotGeq (mode, UnknownId) }

mode_annots:
  | WITH annots = separated_nonempty_list(COMMA, mode_annot) { annots }

(* module *)
xfrp_module:
  | MODULE id = UID
    params = loption(paren(separated_list(COMMA, id_and_type)))
    LBRACE
    in_nodes = loption(in_node_decl)
    out_nodes = out_node_decl
    mode_annot = loption(mode_annots)
    elems = list(module_elem)
    RBRACE
    {
      try
        let () = check_name_conflict_module elems in
        let (cs, ns, newns) = split_module_elems elems in
        let consts = list_to_idmap (fun d -> d.const_id) cs in
        let nodes = list_to_idmap (fun d -> d.node_id) ns in
        let newnodes = list_to_idmap (fun d -> d.newnode_id) newns in
        let all = list_to_idmap module_elem_id elems in
        let consts_ord = tsort_consts consts in
        let update_ord = get_update_ord nodes newnodes in
        let () = check_nodes in_nodes out_nodes [] nodes newnodes mode_annot in
        {
          module_pub = false;
          module_id = id;
          module_params = params;
          module_in = in_nodes;
          module_out = out_nodes;
          module_mode_annots = mode_annot;
          module_consts = consts;
          module_nodes = nodes;
          module_newnodes = newnodes;
          module_all = all;
          module_consts_ord = consts_ord;
          module_update_ord = update_ord;
        }
      with
      | Dependency.Cycle ->
          let msg =
            Printf.sprintf "Detect cyclic dependency"
          in
          raise (Check.Error msg)
    }

module_elem:
  | def = node
    {
      let () = check_module_attr_node def in
      MNode(def)
    }
  | def = newnode
    {
      let () = check_module_attr_newnode def in
      MNewnode(def)
    }
  | def = constdef { MConst(def) }

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
      try
        let () = check_name_conflict_smodule elems in
        let (cs, sts) = split_smodule_elems elems in
        let consts = list_to_idmap (fun d -> d.const_id) cs in
        let states = list_to_idmap (fun d -> d.state_id) sts in
        let all = list_to_idmap smodule_elem_id elems in
        let consts_ord = tsort_consts consts in
        let () =
          List.iter (fun st ->
            check_nodes in_nodes out_nodes shared_nodes st.state_nodes st.state_newnodes st.state_mode_annots
          ) sts
        in
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
          smodule_all = all;
          smodule_consts_ord = consts_ord;
        }
      with
      | Dependency.Cycle ->
          let msg =
            Printf.sprintf "Detect cyclic dependency"
          in
          raise (Check.Error msg)
    }

smodule_elem:
  | def = state { SMState(def) }
  | def = constdef { SMConst(def) }

state:
  | STATE id = UID
    params = loption(paren(separated_nonempty_list(COMMA, id_and_type)))
    mode_annot = loption(mode_annots)
    LBRACE
    elems = list(state_elem)
    SWITCH COLON switch = expression
    RBRACE
    {
      try
        let (cs, ns, newns) = split_state_elems elems in
        let () = check_name_conflict_state elems in
        let consts = list_to_idmap (fun d -> d.const_id) cs in
        let nodes = list_to_idmap (fun d -> d.node_id) ns in
        let newnodes = list_to_idmap (fun d -> d.newnode_id) newns in
        let all = list_to_idmap state_elem_id elems in
        let consts_ord = tsort_consts consts in
        let update_ord = get_update_ord nodes newnodes in
        {
          state_id = id;
          state_params = params;
          state_mode_annots = mode_annot;
          state_consts = consts;
          state_nodes = nodes;
          state_newnodes = newnodes;
          state_all = all;
          state_switch = switch;
          state_consts_ord = consts_ord;
          state_update_ord = update_ord;
        }
      with
      | Dependency.Cycle ->
          let msg =
            Printf.sprintf "Detect cyclic dependency"
          in
          raise (Check.Error msg)
    }

state_elem:
  | def = node { SNode(def) }
  | def = newnode { SNewnode(def) }
  | def = constdef { SConst(def) }

(* node *)
node_attr:
  | SHARED { SharedNode } | OUT { OutputNode }

node:
  | attr = node_attr? NODE id = ID
    init = paren(expression)?
    topt = preceded(COLON, typespec)?
    EQUAL body = expression
    {
      let attr =
        match attr with
        | Some(x) -> x
        | None -> NormalNode
      in
      let t =
        match topt with
        | Some(x) -> x
        | None -> TEmpty
      in
      {
        node_attr = attr;
        node_id = id;
        node_init = init;
        node_type = t;
        node_body = body;
      }
    }

newnode:
  | NEWNODE binds = separated_nonempty_list(COMMA, newnode_bind) EQUAL
    module_id = UID margs = loption(paren(separated_list(COMMA, expression)))
    LARROW inputs = separated_nonempty_list(COMMA, newnode_input)
    {
      let id = gensym () in
      {
        newnode_id = id;
        newnode_binds = binds;
        newnode_module = (module_id, UnknownId);
        newnode_margs = margs;
        newnode_inputs = inputs;
      }
    }

newnode_bind:
  | attr = node_attr? id = ID
    {
      let attr =
        match attr with
        | Some(x) -> x
        | None -> NormalNode
      in
      (attr, NBDef id, TEmpty)
    }
  | attr = node_attr? AND id = ID
    {
      let attr =
        match attr with
        | Some(x) -> x
        | None -> NormalNode
      in
      (attr, NBPass id, TEmpty)
    }

newnode_input:
  | expr = expression { expr }
  | AND id = ID { EPass(id, UnknownId), TEmpty }

(* expressions *)
expression:
  | op = uni_op expr = expression
    %prec prec_uni
    {
      let (sub, _) = expr in
      let ast =
        match op, sub with
        | UPlus, EConst (LInt _) | UPlus, EConst (LFloat _) -> sub
        | UMinus, EConst (LInt n) -> EConst (LInt (- n))
        | UMinus, EConst (LFloat n) -> EConst (LFloat (-. n))
        | _, _ -> EUniOp(op, expr)
      in
      (ast, TEmpty)
    }
  | expr1 = expression op = bin_op expr2 = expression
    { (EBinOp(op, expr1, expr2), TEmpty) }
  | c = UID v = expression?
    {
      let cons = (c, UnknownId) in
      match v with
      | Some x -> (EVariant(cons, x), TEmpty)
      | None ->
        let expr_unit = (EConst(LUnit), TEmpty) in
        (EVariant(cons, expr_unit), TEmpty)
    }
  | expr = paren(separated_nonempty_list(COMMA, expression))
    {
      match expr with
      | [] -> assert false
      | [x] -> x
      | _ -> (ETuple(expr), TEmpty)
    }
  | expr = single_literal
    { (EConst(expr), TEmpty) }
  | RETAIN
    { (ERetain, TEmpty) }
  | id = ID
    { let idref = (id, UnknownId) in (EId idref, TEmpty) }
  | id = ID AT annot = annotation
    { let idref = (id, UnknownId) in (EAnnot(idref, annot), TEmpty) }
  | id = ID args = paren(separated_list(COMMA, expression))
    { let idref = (id, UnknownId) in (EFuncall(idref, args), TEmpty) }
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
      let cons = (c, UnknownId) in
      match v with
      | Some(x) -> (PVariant(cons,x), TEmpty)
      | _ ->
        let pat_unit = (PConst(LUnit), TEmpty) in
        (PVariant(cons, pat_unit), TEmpty)
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

io_node_decl:
  | id = ID init = paren(expression)? COLON mode = preceded(QUOTE, UID)? t = typespec
    { match mode with
      | None -> id, init, t
      | Some(mode_id) -> id, init, TMode("", mode_id, t)
    }

node_decl:
  | id = ID init = paren(expression)? COLON t = typespec
    { (id, init, t) }

single_literal:
  | TRUE { LTrue }
  | FALSE { LFalse }
  | UNIT { LUnit }
  | n = INT { LInt(n) }
  | n = FLOAT { LFloat(n) }

literal:
  | TRUE { LTrue }
  | FALSE { LFalse }
  | UNIT { LUnit }
  | n = int_literal { LInt(n) }
  | n = float_literal { LFloat(n) }

int_literal:
  | n = INT { n }
  | PLUS n = int_literal { n }
  | MINUS n = int_literal { - n }

float_literal:
  | n = FLOAT { n }
  | PLUS n = float_literal { n }
  | MINUS n = float_literal { -. n }

typespec:
  | id = UID
    {
      match id with
      | "Unit" -> TUnit
      | "Bool" -> TBool
      | "Int" -> TInt
      | "Float" -> TFloat
      | _ -> TId("", id)
    }
  | ts = paren(separated_nonempty_list(COMMA, typespec))
    { TTuple(ts) }
