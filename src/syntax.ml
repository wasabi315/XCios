(* AST type definitions *)
open Extension.Format

(* identifier *)
type identifier = string

let pp_identifier = pp_print_string

let pp_id_and_args pp_args =
  pp_funcall pp_identifier pp_args

let pp_id_and_type ppf (id, t) =
  fprintf ppf "%a : %a"
    pp_identifier id Type.pp_t t

module Identifier =
  struct
    type t = identifier
    let compare = String.compare
  end

module Idmap = Map.Make(Identifier)
module Idset = Set.Make(Identifier)

(* literal *)
type literal =
  | LTrue
  | LFalse
  | LInt of string
  | LFloat of string
  | LUnit

let pp_literal ppf = function
  | LTrue -> fprintf ppf "<literal True>"
  | LFalse -> fprintf ppf "<literal False>"
  | LInt(n) -> fprintf ppf "<literal int %a>" pp_print_string n
  | LFloat(n) -> fprintf ppf "<literal float %a>" pp_print_string n
  | LUnit -> fprintf ppf "<literal Unit>"

(* operators *)
type uni_op = UNot | UInv

let pp_uni_op ppf op =
  pp_print_string ppf
    (match op with
     | UNot -> "!" | UInv -> "~")

type bin_op =
  | BMul | BDiv | BAdd | BSub
  | BFMul | BFDiv | BFAdd | BFSub
  | BMod | BShl | BShr
  | BLt | BLeq | BGt | BGeq
  | BFLt | BFLeq | BFGt | BFGeq
  | BEq | BNeq
  | BLand | BLor
  | BAnd | BOr | BXor

let pp_bin_op ppf op =
  pp_print_string ppf
    (match op with
     | BMul -> "*" | BDiv -> "/" | BAdd -> "+" | BSub -> "-"
     | BFMul -> "*." | BFDiv -> "/." | BFAdd -> "+." | BFSub -> "-."
     | BMod -> "%" | BShl -> "<<" | BShr -> ">>"
     | BLt -> "<" | BLeq -> "<=" | BGt -> ">" | BGeq -> ">="
     | BFLt -> "<." | BFLeq -> "<=." | BFGt -> ">." | BFGeq -> ">=."
     | BEq -> "==" | BNeq -> "!="
     | BLand -> "&&" | BLor -> "||"
     | BAnd -> "&" | BOr -> "|" | BXor -> "^")

(* node annotation *)
type annotation = ALast

let pp_annotation ppf annot =
  pp_print_string ppf
    (match annot with
     | ALast -> "last")

(* pattern *)
type pattern_ast =
  | PWild
  | PId of identifier
  | PConst of literal
  | PTuple of (pattern list)
  | PVariant of identifier * pattern
and pattern = pattern_ast * Type.t

let rec pp_pattern_ast ppf =
  begin
    function
    | PWild -> pp_print_string ppf "_"
    | PId(id) -> pp_identifier ppf id
    | PConst(c) -> pp_literal ppf c
    | PTuple(ps) -> fprintf ppf "(@[%a@])" (pp_list_comma pp_pattern) ps
    | PVariant(c, p) -> fprintf ppf "%a@ %a" pp_identifier c pp_pattern p
  end
and pp_pattern ppf (ast, t) =
  fprintf ppf "%a : %a" pp_pattern_ast ast Type.pp_t t

(* expression *)
type expression_ast =
  | EUniOp of uni_op * expression
  | EBinOp of bin_op * expression * expression
  | EVariant of identifier * expression
  | ETuple of expression list
  | EConst of literal
  | ERetain
  | EId of identifier
  | EAnnot of identifier * annotation
  | EFuncall of identifier * (expression list)
  | EIf of expression * expression * expression
  | ELet of (binder list) * expression
  | ECase of expression * (branch list)

and binder =
  {
    binder_id : (identifier * Type.t);
    binder_body : expression;
  }

and branch =
  {
    branch_pat : pattern;
    branch_body : expression;
  }
and expression = expression_ast * Type.t

let rec pp_expression_ast ppf = function
  | EUniOp(op, e) -> fprintf ppf "<uniop @[%a@ %a@]>"
                     pp_uni_op op pp_expression e
  | EBinOp(op, e1, e2) -> fprintf ppf "<binop @[%a@ @[%a@ %a@]@]>"
                            pp_bin_op op pp_expression e1 pp_expression e2
  | EVariant(c,v) -> fprintf ppf "<variant %a %a>"
                       pp_identifier c pp_expression v
  | ETuple(es) -> fprintf ppf "<tuple (@[%a@])>" (pp_list_comma pp_expression) es
  | EConst(l) -> fprintf ppf "<const %a>" pp_literal l
  | ERetain -> fprintf ppf "<Retain>"
  | EId(id) -> fprintf ppf "<id %a>" pp_identifier id
  | EAnnot(id, annot) -> fprintf ppf "<annot @[%a@ %@@ %a@]>"
                         pp_identifier id pp_annotation annot
  | EFuncall(id, es) -> fprintf ppf "<funcall %a>"
                        (pp_id_and_args pp_expression) (id, es)
  | EIf(etest, ethen, eelse) -> fprintf ppf "<if @[<v>%a@ %a@ %a@]>"
                                  pp_expression etest
                                  pp_expression ethen
                                  pp_expression eelse
  | ELet(binders, body) -> fprintf ppf "<@[<v 2>let (@[<v>%a@])@;%a@]>"
                        (pp_list_comma pp_binder) binders pp_expression body
  | ECase(e, branchs) -> fprintf ppf "<@[<v 2>case %a@;@[<v>%a@]>"
                           pp_expression e (pp_list_comma pp_branch) branchs

and pp_binder ppf {binder_id; binder_body} =
  fprintf ppf "@[<2>%a =@ %a@]"
    pp_id_and_type binder_id pp_expression binder_body

and pp_branch ppf {branch_pat; branch_body} =
  fprintf ppf "@[<2>%a ->@ %a@]"
    pp_pattern branch_pat pp_expression branch_body

and pp_expression ppf (ast, t) =
  fprintf ppf "%a : %a" pp_expression_ast ast Type.pp_t t

(* const *)
type constdef =
  {
    const_pub : bool;
    const_id : identifier;
    const_type : Type.t;
    const_body : expression;
  }

let pp_constdef ppf {const_pub;const_id;const_type;const_body} =
  fprintf ppf "<@[<v 1>ConstDef:@;";
  fprintf ppf "id: %a@;" pp_id_and_type (const_id, const_type);
  fprintf ppf "public: %a@;" pp_print_bool const_pub;
  fprintf ppf "body: %a@]>" pp_expression const_body

(* type *)
type typedef =
  {
    type_pub : bool;
    type_id : identifier;
    variant_defs : (identifier * Type.t) list;
  }

let pp_typedef ppf {type_pub;type_id;variant_defs} =
  let pp_variant_def ppf (id, t) =
    fprintf ppf "%a of %a" pp_identifier id Type.pp_t t
  in
  fprintf ppf "<@[<v 1>TypeDef:@;";
  fprintf ppf "id: %a@;" pp_identifier type_id;
  fprintf ppf "public: %a@;" pp_print_bool type_pub;
  fprintf ppf "variants: (@[%a@])@]>"
    (pp_list_comma pp_variant_def) variant_defs

(* function *)
type fundef =
  {
    fun_pub : bool;
    fun_id : identifier;
    fun_params : (identifier * Type.t) list;
    fun_type : Type.t;
    fun_body : expression;
  }

let pp_fundef ppf {fun_pub;fun_id;fun_type;fun_params;fun_body} =
  fprintf ppf "<@[<v 1>FunDef:@;";
  fprintf ppf "id: %a@;" pp_id_and_type (fun_id, fun_type);
  fprintf ppf "public: %a@;" pp_print_bool fun_pub;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_type) fun_params;
  fprintf ppf "body: %a@]>" pp_expression fun_body

(* internal node *)
let pp_node_decl ppf (id, init, t) =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "%a(%a) : %a"
    pp_identifier id
    (pp_opt pp_expression pp_init_none) init
    Type.pp_t t

type node =
  {
    node_id : identifier;
    node_init : expression option;
    node_type : Type.t;
    node_body : expression;
  }

let pp_node ppf {node_id;node_init;node_type;node_body} =
  fprintf ppf "<@[<v 1>node:@;";
  fprintf ppf "id: %a@;" pp_node_decl (node_id, node_init, node_type);
  fprintf ppf "body: %a@]>" pp_expression node_body

(* output node *)
type outnode =
  {
    outnode_id : identifier;
    outnode_type : Type.t;
    outnode_body : expression;
  }
let pp_outnode ppf {outnode_id;outnode_type;outnode_body} =
  fprintf ppf "<@[<v 1>outnode:@;";
  fprintf ppf "id: %a@;" pp_id_and_type (outnode_id, outnode_type);
  fprintf ppf "body: %a@]>" pp_expression outnode_body

(* newnode *)
type newnode =
  {
    newnode_binds : (identifier * Type.t) list;
    newnode_module : identifier;
    newnode_margs : expression list;
    newnode_inputs : expression list;
  }
let pp_newnode ppf def =
  fprintf ppf "<@[<v 1>newnode:@;";
  fprintf ppf "bind: %a@;" (pp_list_comma pp_id_and_type) def.newnode_binds;
  fprintf ppf "module: %a@;" pp_identifier def.newnode_module;
  fprintf ppf "args: %a@]>" (pp_list_comma pp_expression) def.newnode_margs;
  fprintf ppf "input: %a@]>" (pp_list_comma pp_expression) def.newnode_inputs

(* module *)
type module_elem =
  | MNode of node
  | MOutNode of outnode
  | MNewNode of newnode
  | MConst of constdef
let pp_module_elem ppf = function
  | MNode(d) -> pp_node ppf d
  | MOutNode(d) -> pp_outnode ppf d
  | MNewNode(d) -> pp_newnode ppf d
  | MConst(d) -> pp_constdef ppf d

type xfrp_module =
  {
    module_pub : bool;
    module_id : identifier;
    module_params : (identifier * Type.t) list;
    module_in : (identifier * (expression option) * Type.t) list;
    module_out : (identifier * (expression option) * Type.t) list;
    module_elems : module_elem list;
  }
let pp_xfrp_module ppf def =
  fprintf ppf "<@[<v 1>module:@;";
  fprintf ppf "id: %a@;" pp_identifier def.module_id;
  fprintf ppf "public : %a@;" pp_print_bool def.module_pub;
  fprintf ppf "in: (@[%a@])@;"
    (pp_list_comma pp_node_decl) def.module_in;
  fprintf ppf "out: (@[%a@])@;"
    (pp_list_comma pp_node_decl) def.module_out;
  fprintf ppf "elems: (@[%a@])@]>"
    (pp_list_comma pp_module_elem) def.module_elems;

(* state *)
type state_elem =
  | SNode of node
  | SOutNode of outnode
  | SNewNode of newnode
  | SConst of constdef
let pp_state_elem ppf = function
  | SNode(d) -> pp_node ppf d
  | SOutNode(d) -> pp_outnode ppf d
  | SNewNode(d) -> pp_newnode ppf d
  | SConst(d) -> pp_constdef ppf d

type state =
  {
    state_id : identifier;
    state_params : (identifier * Type.t) list;
    state_elems : state_elem list;
    state_switch : expression;
  }
let pp_state ppf {state_id; state_params; state_elems; state_switch} =
  fprintf ppf "<@[<v 1>StateDef:@;";
  fprintf ppf "id: %a@;" pp_identifier state_id;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_type) state_params;
  fprintf ppf "elems: (@[%a@])@;"
    (pp_list_comma pp_state_elem) state_elems;
  fprintf ppf "switch: %a@]>" pp_expression state_switch;

(* switch module *)
type smodule_elem =
  | SMState of state
  | SMConst of constdef
let pp_smodule_elem ppf = function
  | SMState(d) -> pp_state ppf d
  | SMConst(d) -> pp_constdef ppf d

type xfrp_smodule =
  {
    smodule_pub : bool;
    smodule_id : identifier;
    smodule_params : (identifier * Type.t) list;
    smodule_in : (identifier * (expression option) * Type.t) list;
    smodule_out : (identifier * (expression option) * Type.t) list;
    smodule_init : expression;
    smodule_elems : smodule_elem list;
  }
let pp_xfrp_smodule ppf def =
  fprintf ppf "<@[<v 1>module:@;";
  fprintf ppf "id: %a@;" pp_identifier def.smodule_id;
  fprintf ppf "public : %a@;" pp_print_bool def.smodule_pub;
  fprintf ppf "params: %a@;"
    (pp_list_comma pp_id_and_type) def.smodule_params;
  fprintf ppf "in: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.smodule_in;
  fprintf ppf "out: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.smodule_out;
  fprintf ppf "elems: @[%a@]@]>"
    (pp_list_comma pp_smodule_elem) def.smodule_elems;

(* whole program *)
type xfrp_elem =
  | XFRPType of typedef
  | XFRPConst of constdef
  | XFRPFun of fundef
  | XFRPModule of xfrp_module
  | XFRPSModule of xfrp_smodule
let pp_xfrp_elem ppf = function
  | XFRPType(d) -> pp_typedef ppf d
  | XFRPConst(d) -> pp_constdef ppf d
  | XFRPFun(d) -> pp_fundef ppf d
  | XFRPModule(d) -> pp_xfrp_module ppf d
  | XFRPSModule(d) -> pp_xfrp_smodule ppf d

type xfrp =
  {
    xfrp_use : identifier list;
    xfrp_elems : xfrp_elem list;
  }
let pp_xfrp ppf def =
  fprintf ppf "<@[<v 1>xfrp:@;";
  fprintf ppf "use: %a@;"
    (pp_list_comma pp_identifier) def.xfrp_use;
  fprintf ppf "elems: @[%a@]@]>"
    (pp_list_comma pp_xfrp_elem) def.xfrp_elems

