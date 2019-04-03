(* AST type definitions *)

type identifier = string

type typespec =
  | TBool | TInt | TFloat
  | TID of identifier
  | TTuple of typespec list

type literal =
  | LTrue
  | LFalse
  | LNum of string

(* expression *)          
type expression =
  | EUniOp of uni_op * expression
  | EBinOP of bin_op * expression * expression
  | ETuple of expression list
  | EConst of literal
  | ERetain
  | EId of identifier
  | EAnnot of identifier * annotation
  | EFuncall of identifier * (expression list)
  | EIf of expression * expression * expression
  | ELet of (binder list) * expression
  | EPat of expression * (branch list)
and uni_op = UPos| UNeg | UNot | UInv
and bin_op =
  | BMul | BDiv | BMod 
  | BAdd | BSub
  | BShl | BShr
  | BLt | BLeq | BGt | BGeq
  | BEq | BNeq
  | BLand | BLor
  | BAnd | BOr | BXor
and annotation = ALast
and binder =
  {
    bind_id = identifier;
    bind_type = typespec option;
    bind_body = expression;
  }
and branch =
  {
    branch_pat = pattern;
    branch_expr = expression;
  }
and pattern = 
  | PWild
  | PId of identifier
  | PConst of literal
  | PTuple of (pattern list)
  | PADT of identifier * (pattern list)
            
(* toplevel definitions *)          
type definition =
  | DefData of datadef
  | DefType of typedef
  | DefFunc of funcdef
  | DefState of statedef
and datadef =
  {
    data_id : identifier;
    data_type : typespec option;
    data_body : expression;
  }
and typedef =
  {
    type_id : identifier;
    constructors : identifier * (typespec list);
  }
and funcdef =
  {
    func_id : identifier;
    func_type : typespec option;
    func_params : (identifier * (typespec option)) list;
    func_body : expression;
  }
and statedef =
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
