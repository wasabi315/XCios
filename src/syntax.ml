(* AST type definitions *)
open Extension.Format

(* Identifier *)
type identifier = string
let pp_identifier = pp_print_string

let pp_id_and_args pp_args =
  pp_funcall pp_identifier pp_args

(* Type specification *)
type typespec =
  | TBool | TInt | TDouble
  | TID of identifier
  | TTuple of typespec list
let rec pp_typespec ppf = function
  | TBool -> pp_print_string ppf "<type Bool>"
  | TInt -> pp_print_string ppf "<type Int>"
  | TDouble -> pp_print_string ppf "<type Double>"
  | TID(t) -> fprintf ppf "<type %a>" pp_identifier t
  | TTuple(ts) -> fprintf ppf "<type (@[%a@])>"
                    (pp_list_comma pp_typespec) ts

let pp_typespec_opt =
  pp_opt pp_typespec (fun ppf () -> pp_print_string ppf "_")

let pp_id_and_type ppf (id, t) =
  fprintf ppf "%a : %a"
    pp_identifier id pp_typespec t

let pp_id_and_typeopt ppf (id, topt)=
  fprintf ppf "%a : %a"
    pp_identifier id pp_typespec_opt topt

(* Literal *)
type literal =
  | LTrue
  | LFalse
  | LInt of string
  | LDouble of string
let pp_literal ppf = function
  | LTrue -> fprintf ppf "<literal True>"
  | LFalse -> fprintf ppf "<literal False>"
  | LInt(n) -> fprintf ppf "<literal int %a>" pp_print_string n
  | LDouble(n) -> fprintf ppf "<literal float %a>" pp_print_string n

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
  | PADT of identifier * (pattern list)
let rec pp_pattern ppf = function
  | PWild -> pp_print_string ppf "_"
  | PId(id) -> pp_identifier ppf id
  | PConst(c) -> pp_literal ppf c
  | PTuple(ps) -> fprintf ppf "(@[%a@])" (pp_list_comma pp_pattern) ps
  | PADT(c, ps) -> (pp_id_and_args pp_pattern) ppf (c, ps)

(* Expression *)
type expression =
  | EUniOp of uni_op * expression
  | EBinOp of bin_op * expression * expression
  | ETuple of expression list
  | EConst of literal
  | ERetain
  | EId of identifier
  | EAnnot of identifier * annotation
  | EFuncall of identifier * (expression list)
  | EIf of expression * expression * expression
  | EPat of expression * (branch list)
and branch =
  {
    branch_pat : pattern;
    branch_expr : expression;
  }
let rec pp_expression ppf = function
  | EUniOp(op, e) -> fprintf ppf "<uniop @[%a@ %a@]>"
                     pp_uni_op op pp_expression e
  | EBinOp(op, e1, e2) -> fprintf ppf "<binop @[%a@ @[%a@ %a@]@]>"
                         pp_bin_op op pp_expression e1 pp_expression e2
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
  | EPat(e, branchs) -> fprintf ppf "<match @[%a@;(@[%a@])@]>"
                        pp_expression e (pp_list_comma pp_branch) branchs
and pp_branch ppf {branch_pat; branch_expr} =
  fprintf ppf "@[<2>%a ->@ %a@]"
    pp_pattern branch_pat pp_expression branch_expr

(* Data definition *)
type datadef =
  {
    data_id : identifier;
    data_type : typespec option;
    data_body : expression;
  }
let pp_datadef ppf {data_id; data_type; data_body} =
  fprintf ppf "<@[<v 1>DataDef:@;";
  fprintf ppf "id: %a@;" pp_identifier data_id;
  fprintf ppf "type: %a@;" pp_typespec_opt data_type;
  fprintf ppf "body: %a@]>" pp_expression data_body

(* Type defitnition *)
type typedef =
  {
    type_id : identifier;
    constructors : (identifier * (typespec list)) list;
  }
let pp_typedef ppf {type_id;constructors} =
  let pp_constructor = (pp_id_and_args pp_typespec) in
  fprintf ppf "<@[<v 1>TypeDef:@;";
  fprintf ppf "id: %a@;" pp_identifier type_id;
  fprintf ppf "constructors: (@[%a@])@]>"
    (pp_list_comma pp_constructor) constructors

(* Function defitnition *)
type funcdef =
  {
    func_id : identifier;
    func_type : typespec option;
    func_params : (identifier * (typespec option)) list;
    func_body : expression;
  }
let pp_funcdef ppf {func_id;func_type;func_params;func_body} =
  fprintf ppf "<@[<v 1>FuncDef:@;";
  fprintf ppf "id: %a@;" pp_identifier func_id;
  fprintf ppf "type: %a@;" pp_typespec_opt func_type;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_typeopt) func_params;
  fprintf ppf "body: %a@]>" pp_expression func_body

(* State definition *)
type statedef =
  {
    state_id : identifier;
    state_params : (identifier * typespec) list;
    nodes : nodedef list;
    switch : expression;
  }
and nodedef =
  {
    init : expression option;
    node_id : identifier;
    node_type : typespec option;
    node_body : expression;
  }
let rec pp_statedef ppf {state_id; state_params; nodes; switch} =
  fprintf ppf "<@[<v 1>StateDef:@;";
  fprintf ppf "id: %a@;" pp_identifier state_id;
  fprintf ppf "params: (@[%a@])@;"
    (pp_list_comma pp_id_and_type) state_params;
  fprintf ppf "nodes: (@[%a@])@;"
    (pp_list_comma pp_nodedef) nodes;
  fprintf ppf "switch: %a@]>" pp_expression switch;
and pp_nodedef ppf {init; node_id; node_type; node_body} =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "<@[<v 1>NodeDef:@;";
  fprintf ppf "init: %a@;"
    (pp_opt pp_expression pp_init_none) init;
  fprintf ppf "id: %a@;" pp_identifier node_id;
  fprintf ppf "type: %a@;" pp_typespec_opt node_type;
  fprintf ppf "body: %a@]>" pp_expression node_body

(* toplevel definitions *)
type definition =
  | DataDef of datadef
  | TypeDef of typedef
  | FuncDef of funcdef
  | StateDef of statedef
let pp_definition ppf = function
  | DataDef(d) -> pp_datadef ppf d
  | TypeDef(d) -> pp_typedef ppf d
  | FuncDef(d) -> pp_funcdef ppf d
  | StateDef(d) -> pp_statedef ppf d

(* whole module *)
type switchmodule =
  {
    module_id   : identifier;
    (* (identifier / init value) list *)
    in_nodes    : (identifier * (literal option) * typespec) list;
    out_nodes   : (identifier * literal * typespec) list;
    use         : identifier list;
    (* state id / state parameters *)
    init        : identifier * (literal list);
    definitions : definition list;
  }
let pp_switchmodule ppf {module_id; in_nodes; out_nodes; use; init; definitions} =
  let pp_in_node ppf (id, init, t) =
    let pp_init_none ppf () = pp_print_string ppf "_" in
    fprintf ppf "%a(%a) : %a"
      pp_identifier id
      (pp_opt pp_literal pp_init_none) init
      pp_typespec t
  in
  let pp_out_node ppf (id, init, t) =
    fprintf ppf "%a(%a) : %a"
      pp_identifier id pp_literal init pp_typespec t
  in
  fprintf ppf "<@[<v 1>SwitchModule:@;";
  fprintf ppf "id: %a@;" pp_identifier module_id;
  fprintf ppf "in_nodes: (@[%a@])@;"
    (pp_list_comma pp_in_node) in_nodes;
  fprintf ppf "out_nodes: (@[%a@])@;"
    (pp_list_comma pp_out_node) out_nodes;
  fprintf ppf "use: (@[%a@])@;"
    (pp_list_comma pp_identifier) use;
  fprintf ppf "init: %a@;"
    (pp_id_and_args pp_literal) init;
  fprintf ppf "definitions: (@[%a@])@]"
    (pp_list_comma pp_definition) definitions
