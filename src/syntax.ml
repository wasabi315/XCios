(* AST type definitions *)
open Extension.Format
open Type

(* Identifier *)
type identifier = string

let pp_identifier = pp_print_string

let pp_id_and_args pp_args =
  pp_funcall pp_identifier pp_args

type id_and_type = identifier * typespec
let pp_id_and_type ppf (id, t) =
  fprintf ppf "%a : %a"
    pp_identifier id pp_typespec t

module Identifier =
  struct
    type t = identifier
    let compare = String.compare
  end

module Idmap = Map.Make(Identifier)
module Idset = Set.Make(Identifier)

(* Literal *)
type literal =
  | LTrue
  | LFalse
  | LInt of string
  | LFloat of string
  | LUnit
  | LTuple of literal list
  | LVariant of identifier * literal

let rec pp_literal ppf = function
  | LTrue -> fprintf ppf "<literal True>"
  | LFalse -> fprintf ppf "<literal False>"
  | LInt(n) -> fprintf ppf "<literal int %a>" pp_print_string n
  | LFloat(n) -> fprintf ppf "<literal float %a>" pp_print_string n
  | LUnit -> fprintf ppf "<literal Unit>"
  | LTuple(ls)-> fprintf ppf "(@[%a])" (pp_list_comma pp_literal) ls
  | LVariant(c,v) -> fprintf ppf "%a@ %a" pp_identifier c pp_literal v

(* Operators *)
type uni_op = UPos| UNeg | UNot | UInv

let pp_uni_op ppf op =
  pp_print_string ppf
    (match op with
     | UPos -> "+" | UNeg -> "-" | UNot -> "!" | UInv -> "~")

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

(* Annotation for node *)
type annotation = ALast

let pp_annotation ppf annot =
  pp_print_string ppf
    (match annot with
     | ALast -> "last")

(* Pattern match *)
type pattern =
  | PWild
  | PId of identifier
  | PConst of literal
  | PTuple of (pattern list)
  | PADT of identifier * pattern

let rec pp_pattern ppf = function
  | PWild -> pp_print_string ppf "_"
  | PId(id) -> pp_identifier ppf id
  | PConst(c) -> pp_literal ppf c
  | PTuple(ps) -> fprintf ppf "(@[%a@])" (pp_list_comma pp_pattern) ps
  | PADT(c, p) -> fprintf ppf "%a@ %a" pp_identifier c pp_pattern p

(* Expression *)
type expression =
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
    binder_id : id_and_type;
    binder_body : expression;
  }

and branch =
  {
    branch_pat : pattern;
    branch_body : expression;
  }

let rec pp_expression ppf = function
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

(* Const definition *)
type constdef =
  {
    const_id : id_and_type;
    const_body : expression;
  }

let pp_constdef ppf {const_id; const_body} =
  fprintf ppf "<@[<v 1>ConstDef:@;";
  fprintf ppf "id: %a@;" pp_id_and_type const_id;
  fprintf ppf "body: %a@]>" pp_expression const_body

(* Type defitnition *)
type typedef =
  {
    type_id : identifier;
    variant_defs : (identifier * typespec) list;
  }

let pp_typedef ppf {type_id;variant_defs} =
  let pp_variant_def ppf (id, t) =
    fprintf ppf "%a of %a" pp_identifier id pp_typespec t
  in
  fprintf ppf "<@[<v 1>TypeDef:@;";
  fprintf ppf "id: %a@;" pp_identifier type_id;
  fprintf ppf "variants: (@[%a@])@]>"
    (pp_list_comma pp_variant_def) variant_defs

(* Function defitnition *)
type fundef =
  {
    fun_id : id_and_type;
    fun_params : id_and_type list;
    fun_body : expression;
  }
let pp_fundef ppf {fun_id;fun_params;fun_body} =
  fprintf ppf "<@[<v 1>FunDef:@;";
  fprintf ppf "id: %a@;" pp_id_and_type fun_id;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_type) fun_params;
  fprintf ppf "body: %a@]>" pp_expression fun_body

(* Node definitions *)
type nodedef =
  {
    init : literal option;
    node_id : id_and_type;
    node_body : expression;
  }

let pp_nodedef ppf {init; node_id; node_body} =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "<@[<v 1>NodeDef:@;";
  fprintf ppf "init: %a@;"
    (pp_opt pp_literal pp_init_none) init;
  fprintf ppf "id: %a@;" pp_id_and_type node_id;
  fprintf ppf "body: %a@]>" pp_expression node_body

(* State definition *)
type statedef =
  {
    state_id : identifier;
    state_params : id_and_type list;
    nodes : nodedef list;
    switch : expression;
  }

let pp_statedef ppf {state_id; state_params; nodes; switch} =
  fprintf ppf "<@[<v 1>StateDef:@;";
  fprintf ppf "id: %a@;" pp_identifier state_id;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_type) state_params;
  fprintf ppf "nodes: (@[%a@])@;"
    (pp_list_comma pp_nodedef) nodes;
  fprintf ppf "switch: %a@]>" pp_expression switch;

(* toplevel definitions *)
(* for module *)
type definitionM =
  | MConstDef of constdef
  | MTypeDef of typedef
  | MFunDef of fundef
  | MNodeDef of nodedef

(* for switch module *)
type definitionSM =
  | SMConstDef of constdef
  | SMTypeDef of typedef
  | SMFunDef of fundef
  | SMStateDef of statedef

let pp_definitionM ppf = function
  | MConstDef(d) -> pp_constdef ppf d
  | MTypeDef(d) -> pp_typedef ppf d
  | MFunDef(d) -> pp_fundef ppf d
  | MNodeDef(d) -> pp_nodedef ppf d

let pp_definitionSM ppf = function
  | SMConstDef(d) -> pp_constdef ppf d
  | SMTypeDef(d) -> pp_typedef ppf d
  | SMFunDef(d) -> pp_fundef ppf d
  | SMStateDef(d) -> pp_statedef ppf d

(* module *)
type xfrp_module =
  {
    module_id   : identifier;
    module_in   : (identifier * (literal option) * typespec) list;
    module_out  : (identifier * (literal option) * typespec) list;
    module_use  : identifier list;
    module_defs : definitionM list;
  }

type xfrp_smodule =
  {
    smodule_id   : identifier;
    smodule_in   : (identifier * (literal option) * typespec) list;
    smodule_out  : (identifier * (literal option) * typespec) list;
    smodule_use  : identifier list;
    smodule_init : identifier * literal;
    smodule_defs : definitionSM list;
  }

let pp_nodedecl ppf (id, init, t) =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "%a(%a) : %a"
    pp_identifier id
    (pp_opt pp_literal pp_init_none) init
    pp_typespec t

let pp_xfrp_module ppf def =
  fprintf ppf "<@[<v 1>module:@;";
  fprintf ppf "id: %a@;" pp_identifier def.module_id;
  fprintf ppf "in: (@[%a@])@;"
    (pp_list_comma pp_nodedecl) def.module_in;
  fprintf ppf "out: (@[%a@])@;"
    (pp_list_comma pp_nodedecl) def.module_out;
  fprintf ppf "use: (@[%a@])@;"
    (pp_list_comma pp_identifier) def.module_use;
  fprintf ppf "definitions: (@[%a@])@]>"
    (pp_list_comma pp_definitionM) def.module_defs

let pp_xfrp_smodule ppf def =
  let pp_init ppf (c, v) =
    fprintf ppf "%a %a" pp_identifier c pp_literal v
  in
  fprintf ppf "<@[<v 1>switchmodule:@;";
  fprintf ppf "id: %a@;" pp_identifier def.smodule_id;
  fprintf ppf "in: (@[%a@])@;"
    (pp_list_comma pp_nodedecl) def.smodule_in;
  fprintf ppf "out: (@[%a@])@;"
    (pp_list_comma pp_nodedecl) def.smodule_out;
  fprintf ppf "use: (@[%a@])@;"
    (pp_list_comma pp_identifier) def.smodule_use;
  fprintf ppf "init: %a@;" pp_init def.smodule_init;
  fprintf ppf "definitions: (@[%a@])@]>"
    (pp_list_comma pp_definitionSM) def.smodule_defs

(* whole program *)
type program = XfrpModule of xfrp_module | XfrpSModule of xfrp_smodule

let pp_program ppf = function
  | XfrpModule(d) -> pp_xfrp_module ppf d
  | XfrpSModule(d) -> pp_xfrp_smodule ppf d
