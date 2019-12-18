(* AST type definitions *)
open Extension.Format

(* identifier *)
type identifier = string

let pp_identifier = pp_print_string

let pp_id_and_type ppf (id, t) =
  fprintf ppf "%a : %a"
    pp_identifier id Type.pp_t t

let conc_id idlist =
  let idlist = List.rev idlist in
  match idlist with
  | [] -> ""
  | x :: xs ->
     List.fold_left (fun acc id -> id ^ "_" ^ acc) x xs

module Identifier =
  struct
    type t = identifier
    let compare = String.compare
  end

module Idmap = Map.Make(Identifier)
module Idset = Set.Make(Identifier)

let pp_idmap pp_contents ppf idmap =
  let pp_binds ppf (id, x) =
    fprintf ppf "%a -> %a" pp_identifier id pp_contents x
  in
  fprintf ppf "@[<v>%a@]" (pp_list_break pp_binds) (Idmap.bindings idmap)

let pp_idset ppf idset =
  let idlist = Idset.to_seq idset |> List.of_seq in
  pp_list_comma pp_identifier ppf idlist

(* node attribute *)
type nattr = NormalNode | InputNode | OutputNode | SharedNode
let pp_nattr ppf = function
  | NormalNode -> fprintf ppf "normal"
  | InputNode -> fprintf ppf "input"
  | OutputNode -> fprintf ppf "output"
  | SharedNode -> fprintf ppf "shared"

(* identifier reference *)
type idinfo =
  | UnknownId
  | LocalId of Type.t
  | ConstId of string * Type.t
  | FunId of string * Type.t list * Type.t
  | ValueCons of string * Type.t * Type.t
  | ModuleCons of string * Type.t list * Type.t list * Type.t list
  | StateCons of string * identifier * Type.t
  | ModuleParam of Type.t
  | ModuleConst of Type.t
  | StateParam of Type.t
  | StateConst of Type.t
  | NodeId of nattr * Type.t
let pp_idinfo ppf = function
  | UnknownId -> fprintf ppf "unknown"
  | LocalId _ -> fprintf ppf "local"
  | ConstId (file, _) -> fprintf ppf "const:%a" pp_print_string file
  | FunId (file, _, _) -> fprintf ppf "fun:%a" pp_print_string file
  | ValueCons (file, _, _) -> fprintf ppf "value cons:%a" pp_print_string file
  | ModuleCons (file, _, _, _) -> fprintf ppf "module cons:%a" pp_print_string file
  | StateCons(_, _, _) -> fprintf ppf "state cons"
  | ModuleParam _ -> fprintf ppf "module param"
  | ModuleConst _ -> fprintf ppf "module const"
  | StateParam _ -> fprintf ppf "state param"
  | StateConst _ -> fprintf ppf "state const"
  | NodeId (_,_) -> fprintf ppf "node"

let map_idinfo_type (f : Type.t -> Type.t) (idinfo : idinfo) : idinfo =
  match idinfo with
  | UnknownId -> idinfo
  | LocalId(t) -> LocalId (f t)
  | ConstId(file, t) -> ConstId (file, f t)
  | FunId(file, tparams, tret) ->
     let tparams = List.map f tparams in
     let tret = f tret in
     FunId(file, tparams, tret)
  | ValueCons(file, tvalue, tret) ->
     let tvalue = f tvalue in
     let tret = f tret in
     ValueCons(file, tvalue, tret)
  | ModuleCons(file, tps, tis, tos) ->
     let tps = List.map f tps in
     let tis = List.map f tis in
     let tos = List.map f tos in
     ModuleCons(file, tps, tis, tos)
  | StateCons(file, mname, t) -> StateCons (file, mname, f t)
  | ModuleParam t -> ModuleParam (f t)
  | ModuleConst t -> ModuleConst (f t)
  | StateParam t -> StateParam (f t)
  | StateConst t -> StateConst (f t)
  | NodeId(attr, t) -> NodeId (attr, f t)

type idref = identifier * idinfo
let pp_idref ppf (id, idinfo) =
  fprintf ppf "%a(%a)" pp_identifier id pp_idinfo idinfo

(* literal *)
type literal =
  | LTrue
  | LFalse
  | LInt of int
  | LFloat of float
  | LUnit

let pp_literal ppf = function
  | LTrue -> fprintf ppf "<literal True>"
  | LFalse -> fprintf ppf "<literal False>"
  | LInt(n) -> fprintf ppf "<literal int %a>" pp_print_int n
  | LFloat(n) -> fprintf ppf "<literal float %a>" pp_print_float n
  | LUnit -> fprintf ppf "<literal Unit>"

(* operators *)
type uni_op =
  | UNot | UInv
  | UPlus | UMinus
  | UFPlus | UFMinus

let pp_uni_op ppf op =
  pp_print_string ppf
    (match op with
     | UNot -> "!" | UInv -> "~"
     | UPlus -> "+" | UMinus -> "-"
     | UFPlus -> "+." | UFMinus -> "-.")

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
  | PVariant of idref * pattern
and pattern = pattern_ast * Type.t

let rec pp_pattern_ast ppf =
  begin
    function
    | PWild -> pp_print_string ppf "_"
    | PId(id) -> pp_identifier ppf id
    | PConst(c) -> pp_literal ppf c
    | PTuple(ps) -> fprintf ppf "(@[%a@])" (pp_list_comma pp_pattern) ps
    | PVariant(c, p) -> fprintf ppf "%a@ %a" pp_idref c pp_pattern p
  end
and pp_pattern ppf (ast, t) =
  fprintf ppf "%a : %a" pp_pattern_ast ast Type.pp_t t

(* expression *)
type expression_ast =
  | EUniOp of uni_op * expression
  | EBinOp of bin_op * expression * expression
  | EVariant of idref * expression
  | ETuple of expression list
  | EConst of literal
  | ERetain
  | EId of idref
  | EAnnot of idref * annotation
  | EFuncall of idref * (expression list)
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
  | EUniOp(op, e) -> fprintf ppf "@[<2><uniop %a@ %a>@]"
                     pp_uni_op op pp_expression e
  | EBinOp(op, e1, e2) -> fprintf ppf "@[<2><binop %a@ @[%a@ %a@]>@]"
                            pp_bin_op op pp_expression e1 pp_expression e2
  | EVariant(c,v) -> fprintf ppf "@[<2><variant %a %a>@]"
                       pp_idref c pp_expression v
  | ETuple(es) -> fprintf ppf "@[<2><tuple (@[%a@])>@]"
                    (pp_list_comma pp_expression) es
  | EConst(l) -> fprintf ppf "<const %a>" pp_literal l
  | ERetain -> fprintf ppf "<Retain>"
  | EId(idref) -> fprintf ppf "<id %a>" pp_idref idref
  | EAnnot(idref, annot) -> fprintf ppf "@[<2><annot @[%a %@@ %a@]>@]"
                           pp_idref idref pp_annotation annot
  | EFuncall(idref, es) -> fprintf ppf "<@[<v 2>funcall %a@;@[<v>%a@]@]>"
                          pp_idref idref (pp_list_comma pp_expression) es
  | EIf(etest, ethen, eelse) -> fprintf ppf "<if @[<v>%a@ %a@ %a@]>"
                                  pp_expression etest
                                  pp_expression ethen
                                  pp_expression eelse
  | ELet(binders, body) -> fprintf ppf "<let @[(%a)@;%a@]>"
                        (pp_list_comma pp_binder) binders pp_expression body
  | ECase(e, branchs) -> fprintf ppf "<@[<v 2>case %a@;@[<v>%a@]@]>"
                           pp_expression e (pp_list_comma pp_branch) branchs

and pp_binder ppf {binder_id; binder_body} =
  fprintf ppf "%a = @[%a@]"
    pp_id_and_type binder_id pp_expression binder_body

and pp_branch ppf {branch_pat; branch_body} =
  fprintf ppf "%a -> @[%a@]"
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
  fprintf ppf "@[<v>ConstDef: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_id_and_type (const_id, const_type);
  fprintf ppf "public: %a@;" pp_print_bool const_pub;
  fprintf ppf "body: %a@]@;" pp_expression const_body;
  fprintf ppf "}@]"

(* type *)
type typedef =
  {
    type_pub : bool;
    type_id : identifier;
    type_conses : Type.t Idmap.t;
  }

let pp_typedef ppf {type_pub;type_id;type_conses} =
  fprintf ppf "@[<v>TypeDef: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_identifier type_id;
  fprintf ppf "public: %a@;" pp_print_bool type_pub;
  fprintf ppf "constructors: @[%a@]@]@;"
    (pp_idmap Type.pp_t) type_conses;
  fprintf ppf "}@]"

(* function *)
type fundef =
  {
    fun_pub : bool;
    fun_id : identifier;
    fun_params : (identifier * Type.t) list;
    fun_rettype : Type.t;
    fun_body : expression;
  }

let pp_fundef ppf {fun_pub;fun_id;fun_rettype;fun_params;fun_body} =
  fprintf ppf "@[<v>FunDef: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_identifier fun_id;
  fprintf ppf "public: %a@;" pp_print_bool fun_pub;
  fprintf ppf "params: @[%a@]@;"
    (pp_list_comma pp_id_and_type) fun_params;
  fprintf ppf "return: %a" Type.pp_t fun_rettype;
  fprintf ppf "body: %a@]@;" pp_expression fun_body;
  fprintf ppf "}@]"

(* node *)
let pp_node_decl ppf (id, init, t) =
  let pp_init_none ppf () = pp_print_string ppf "_" in
  fprintf ppf "%a(%a) : %a"
    pp_identifier id
    (pp_opt pp_expression pp_init_none) init
    Type.pp_t t

type node =
  {
    node_attr : nattr;
    node_id   : identifier;
    node_init : expression option;
    node_type : Type.t;
    node_body : expression;
  }
let pp_node ppf {node_attr;node_id;node_init;node_type;node_body} =
  fprintf ppf "@[<v>node(%a): {@;<0 2>" pp_nattr node_attr;
  fprintf ppf "@[<v>id: %a@;" pp_node_decl (node_id, node_init, node_type);
  fprintf ppf "body: %a@]@;" pp_expression node_body;
  fprintf ppf "}@]"

(* newnode *)
type newnode =
  {
    newnode_id : identifier; (* generated by compiler *)
    newnode_binds : (nattr * identifier * Type.t) list;
    newnode_module : idref;
    newnode_margs : expression list;
    newnode_inputs : expression list;
  }
let pp_newnode ppf def =
  let pp_newnode_bind ppf (attr, id, t) =
    fprintf ppf "%a(%a): %a" pp_identifier id pp_nattr attr Type.pp_t t
  in
  fprintf ppf "@[<v>newnode: {@;<0 2>";
  fprintf ppf "@[<v>bind: @[%a@]@;"
    (pp_list_comma pp_newnode_bind) def.newnode_binds;
  fprintf ppf "module: %a@;" pp_idref def.newnode_module;
  fprintf ppf "args: %a@;" (pp_list_comma pp_expression) def.newnode_margs;
  fprintf ppf "input: @[%a@]@]@;" (pp_list_comma pp_expression) def.newnode_inputs;
  fprintf ppf "}@]"

(* module *)
type module_elem =
  | MNode of node
  | MNewnode of newnode
  | MConst of constdef
let pp_module_elem ppf = function
  | MNode(d) -> pp_node ppf d
  | MNewnode(d) -> pp_newnode ppf d
  | MConst(d) -> pp_constdef ppf d

let module_elem_id = function
  | MNode(d) -> d.node_id
  | MNewnode(d) -> d.newnode_id
  | MConst(d) -> d.const_id

type xfrp_module =
  {
    module_pub        : bool;
    module_id         : identifier;
    module_params     : (identifier * Type.t) list;
    module_in         : (identifier * (expression option) * Type.t) list;
    module_out        : (identifier * (expression option) * Type.t) list;
    module_consts     : constdef Idmap.t;
    module_nodes      : node Idmap.t;
    module_newnodes   : newnode Idmap.t;
    module_all        : module_elem Idmap.t;
    module_consts_ord : identifier list;
    module_update_ord : identifier list;
  }
let pp_xfrp_module ppf def =
  fprintf ppf "@[<v>module: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_identifier def.module_id;
  fprintf ppf "public : %a@;" pp_print_bool def.module_pub;
  fprintf ppf "in: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.module_in;
  fprintf ppf "out: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.module_out;
  fprintf ppf "consts: @[%a@]@;"
    (pp_idmap pp_constdef) def.module_consts;
  fprintf ppf "nodes: @[%a@]@;"
    (pp_idmap pp_node) def.module_nodes;
  fprintf ppf "newnodes: @[%a@]@;"
      (pp_idmap pp_newnode) def.module_newnodes;
  fprintf ppf "consts_ord: @[%a@]@;"
    (pp_list_comma pp_identifier) def.module_consts_ord;
  fprintf ppf "update_ord: @[%a@]@]@;"
    (pp_list_comma pp_identifier) def.module_update_ord;
  fprintf ppf "}@]"

(* state *)
type state_elem =
  | SNode of node
  | SNewnode of newnode
  | SConst of constdef
let pp_state_elem ppf = function
  | SNode(d) -> pp_node ppf d
  | SNewnode(d) -> pp_newnode ppf d
  | SConst(d) -> pp_constdef ppf d

let state_elem_id = function
  | SNode(d) -> d.node_id
  | SNewnode(d) -> d.newnode_id
  | SConst(d) -> d.const_id

type state =
  {
    state_id         : identifier;
    state_params     : (identifier * Type.t) list;
    state_consts     : constdef Idmap.t;
    state_nodes      : node Idmap.t;
    state_newnodes   : newnode Idmap.t;
    state_all        : state_elem Idmap.t;
    state_switch     : expression;
    state_consts_ord : identifier list;
    state_update_ord : identifier list;
  }
let pp_state ppf def =
  fprintf ppf "@[<v>StateDef: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_identifier def.state_id;
  fprintf ppf "params: @[%a@]@;"
    (pp_list_comma pp_id_and_type) def.state_params;
  fprintf ppf "consts: @[%a@]@;"
    (pp_idmap pp_constdef) def.state_consts;
  fprintf ppf "nodes: @[%a@]@;"
    (pp_idmap pp_node) def.state_nodes;
  fprintf ppf "newnodes: @[%a@]@;"
    (pp_idmap pp_newnode) def.state_newnodes;
  fprintf ppf "switch: %a@;" pp_expression def.state_switch;
  fprintf ppf "consts_ord: @[%a@]@;"
    (pp_list_comma pp_identifier) def.state_consts_ord;
  fprintf ppf "update_ord: @[%a@]@]@;"
    (pp_list_comma pp_identifier) def.state_update_ord;
  fprintf ppf "}@]"

(* switch module *)
type smodule_elem =
  | SMState of state
  | SMConst of constdef
let pp_smodule_elem ppf = function
  | SMState(d) -> pp_state ppf d
  | SMConst(d) -> pp_constdef ppf d

let smodule_elem_id = function
  | SMState(d) -> d.state_id
  | SMConst(d) -> d.const_id

type xfrp_smodule =
  {
    smodule_pub        : bool;
    smodule_id         : identifier;
    smodule_params     : (identifier * Type.t) list;
    smodule_in         : (identifier * (expression option) * Type.t) list;
    smodule_out        : (identifier * (expression option) * Type.t) list;
    smodule_shared     : (identifier * (expression option) * Type.t) list;
    smodule_init       : expression;
    smodule_consts     : constdef Idmap.t;
    smodule_states     : state Idmap.t;
    smodule_all        : smodule_elem Idmap.t;
    smodule_consts_ord : identifier list;
  }
let pp_xfrp_smodule ppf def =
  fprintf ppf "@[<v>smodule: {@;<0 2>";
  fprintf ppf "@[<v>id: %a@;" pp_identifier def.smodule_id;
  fprintf ppf "public : %a@;" pp_print_bool def.smodule_pub;
  fprintf ppf "params: %a@;"
    (pp_list_comma pp_id_and_type) def.smodule_params;
  fprintf ppf "in: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.smodule_in;
  fprintf ppf "out: @[%a@]@;"
    (pp_list_comma pp_node_decl) def.smodule_out;
  fprintf ppf "consts: @[%a@]@;"
    (pp_idmap pp_constdef) def.smodule_consts;
  fprintf ppf "states: @[%a@]@;"
    (pp_idmap pp_state) def.smodule_states;
  fprintf ppf "consts_ord: @[%a@]@]@;"
    (pp_list_comma pp_identifier) def.smodule_consts_ord;
  fprintf ppf "}@]"

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

let xfrp_elem_id = function
  | XFRPType(d) -> d.type_id
  | XFRPConst(d) -> d.const_id
  | XFRPFun(d) -> d.fun_id
  | XFRPModule(d) -> d.module_id
  | XFRPSModule(d) -> d.smodule_id

type xfrp =
  {
    xfrp_use : identifier list;
    xfrp_types : typedef Idmap.t;
    xfrp_consts : constdef Idmap.t;
    xfrp_funs : fundef Idmap.t;
    xfrp_modules : xfrp_module Idmap.t;
    xfrp_smodules : xfrp_smodule Idmap.t;
    xfrp_all      : xfrp_elem Idmap.t;
  }
let pp_xfrp ppf def =
  fprintf ppf "@[<v>xfrp: {@;<0 2>";
  fprintf ppf "@[<v>use: %a@;"
    (pp_list_comma pp_identifier) def.xfrp_use;
  fprintf ppf "types: @[%a@]@;"
    (pp_idmap pp_typedef) def.xfrp_types;
  fprintf ppf "consts: @[%a@]@;"
    (pp_idmap pp_constdef) def.xfrp_consts;
  fprintf ppf "funs: @[%a@]@;"
    (pp_idmap pp_fundef) def.xfrp_funs;
  fprintf ppf "modules: @[%a@]@;"
    (pp_idmap pp_xfrp_module) def.xfrp_modules;
  fprintf ppf "smodules: @[%a@]@]@;"
    (pp_idmap pp_xfrp_smodule) def.xfrp_smodules;
  fprintf ppf "}@]"
