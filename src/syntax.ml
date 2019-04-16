(* AST type definitions *)
open Format

(* A pretty printer for list. Separator is comma + space (break hint) *)
let pp_list_comma pp_element =
  let separetor ppf () = fprintf ppf ",@ " in
  pp_print_list pp_element ~pp_sep:separetor

(* A pretty printer for option. *)
let pp_opt pp_some pp_none ppf = function
  | Some(x) -> pp_some ppf x
  | None -> pp_none ppf ()

(* Identifier *)
type identifier = string
let pp_identifier = pp_print_string

(* Type specification *)
type typespec =
  | TBool | TInt | TFloat
  | TID of identifier
  | TTuple of typespec list
let rec pp_typespec ppf = function
  | TBool -> pp_print_string ppf "<type Bool>"
  | TInt -> pp_print_string ppf "<type Int>"
  | TFloat -> pp_print_string ppf "<type Float>"
  | TID(t) -> fprintf ppf "<type %a>" pp_identifier t
  | TTuple(ts) -> let lst_printer = pp_list_comma pp_typespec in
                 fprintf ppf "<type @[<1>(%a)@]>" lst_printer ts

let pp_typespec_opt =
  pp_opt pp_typespec (fun ppf () -> pp_print_string ppf "_")

let pp_id_and_type ppf (id, t) =
  fprintf ppf "%a:%a"
    pp_identifier id pp_typespec t

let pp_id_and_typeopt ppf (id, topt)=
  fprintf ppf "%a:%a"
    pp_identifier id pp_typespec_opt topt

let pp_id_and_args pp_args ppf (id, args) =
  fprintf ppf "%a@[<1>(%a)@]"
    pp_identifier id
    (pp_list_comma pp_args) args

(* Literal *)
type literal =
  | LTrue
  | LFalse
  | LInt of int
  | LFloat of float
let pp_literal ppf = function
  | LTrue -> fprintf ppf "<literal True>"
  | LFalse -> fprintf ppf "<literal False>"
  | LInt(n) -> fprintf ppf "<literal int %a>" pp_print_int n
  | LFloat(n) -> fprintf ppf "<literal float %a>" pp_print_float n

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
let rec pp_pattern ppf  = function
  | PWild -> pp_print_string ppf "_"
  | PId(id) -> pp_identifier ppf id
  | PConst(c) -> pp_literal ppf c
  | PTuple(ps) -> fprintf ppf "@[<1>(%a)@]" (pp_list_comma pp_pattern) ps
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
  | ELet of (binder list) * expression
  | EPat of expression * (branch list)
and branch =
  {
    branch_pat : pattern;
    branch_expr : expression;
  }
and binder =
  {
    bind_id : identifier;
    bind_type : typespec option;
    bind_body : expression;
  }
let rec pp_expression ppf = function
  | EUniOp(op, e) -> fprintf ppf "<uniop @[%a@ %a@]>"
                     pp_uni_op op pp_expression e
  | EBinOp(op, e1, e2) -> fprintf ppf "<binop @[%a@ %a@ %a@]>"
                         pp_bin_op op pp_expression e1 pp_expression e2
  | ETuple(es) -> fprintf ppf "<tuple @[<1>(%a)@]>" (pp_list_comma pp_expression) es
  | EConst(l) -> fprintf ppf "<const %a>" pp_literal l
  | ERetain -> fprintf ppf "<Retain>"
  | EId(id) -> fprintf ppf "<id %a>" pp_identifier id
  | EAnnot(id, annot) -> fprintf ppf "<annot @[%a@ %@@ %a@]>"
                         pp_identifier id pp_annotation annot
  | EFuncall(id, es) -> fprintf ppf "<funcall %a>"
                        (pp_id_and_args pp_expression) (id, es)
  | EIf(etest, ethen, eelse) -> fprintf ppf "<if @[%a@ %a@ %a@]>"
                                  pp_expression etest
                                  pp_expression ethen
                                  pp_expression eelse
  | ELet(binds, body) -> fprintf ppf "<let @[@[<1>(%a)@]@;%a@]>"
                         (pp_list_comma pp_binder) binds pp_expression body
  | EPat(e, branchs) -> fprintf ppf "<match @[%a@;@[<1>(%a)@]@]>"
                        pp_expression e (pp_list_comma pp_branch) branchs
and pp_binder ppf {bind_id; bind_type; bind_body} =
  fprintf ppf "@[<2>%a =@ %a@]"
    pp_id_and_typeopt (bind_id, bind_type)
    pp_expression bind_body
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
  fprintf ppf "<@[<2>DataDef:@;";
  fprintf ppf "id:@ %a@;" pp_identifier data_id;
  fprintf ppf "type:@ %a@;" pp_typespec_opt data_type;
  fprintf ppf "body:@ %a@]>" pp_expression data_body

(* Type defitnition *)
type typedef =
  {
    type_id : identifier;
    constructors : (identifier * (typespec list)) list;
  }
let pp_typedef ppf {type_id;constructors} =
  let pp_constructor = (pp_id_and_args pp_typespec) in
  fprintf ppf "<@[<2>TypeDef:@;";
  fprintf ppf "id:@ %a@;" pp_identifier type_id;
  fprintf ppf "constructors:@ @[<1>(%a)@]@]>"
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
  fprintf ppf "<@[<2>FuncDef:@;";
  fprintf ppf "id:@ %a@;" pp_identifier func_id;
  fprintf ppf "type:@ %a@;" pp_typespec_opt func_type;
  fprintf ppf "params:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_id_and_typeopt) func_params;
  fprintf ppf "body:@ %a@]>" pp_expression func_body

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
  fprintf ppf "<@[<2>StateDef:@;";
  fprintf ppf "id:@ %a@;" pp_identifier state_id;
  fprintf ppf "params:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_id_and_type) state_params;
  fprintf ppf "nodes:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_nodedef) nodes;
  fprintf ppf "switch:@ %a@;@]>" pp_expression switch;
and pp_nodedef ppf {init; node_id; node_type; node_body} =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "<@[<2>NodeDef:@;";
  fprintf ppf "init:@ %a@;"
    (pp_opt pp_expression pp_init_none) init;
  fprintf ppf "id:@ %a@;" pp_identifier node_id;
  fprintf ppf "type:@ %a@;" pp_typespec_opt node_type;
  fprintf ppf "body:@ %a]>" pp_expression node_body

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
    (* (identifier / init value) list *)
    in_nodes    : (identifier * typespec * (literal option)) list;
    out_nodes   : (identifier * typespec) list;
    use         : identifier list;
    (* state id / state parameters *)
    init        : identifier * (literal list);
    definitions : definition list;
  }
let pp_switchmodule ppf {in_nodes; out_nodes; use; init; definitions} =
  let pp_in_node ppf (id, t, init) =
    let pp_init_none ppf () = pp_print_string ppf "_" in
    fprintf ppf "%a(%a)"
      pp_id_and_type (id, t)
      (pp_opt pp_literal pp_init_none) init
  in
  fprintf ppf "<@[<2>SwitchModule:@;";
  fprintf ppf "in_nodes:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_in_node) in_nodes;
  fprintf ppf "out_nodes:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_id_and_type) out_nodes;
  fprintf ppf "use:@ @[<1>(%a)@]@;"
    (pp_list_comma pp_identifier) use;
  fprintf ppf "init:@ %a@;"
    (pp_id_and_args pp_literal) init;
  fprintf ppf "definitions:@ @[<1>(%a)@]@]"
    (pp_list_comma pp_definition) definitions
