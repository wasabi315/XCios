(* Emfrp code generation *)
open Extension.Format
open Syntax

module S = Set.Make(struct
               type t = identifier
               let compare = String.compare
             end)

exception RetainError

(* Identifier *)
let gen_identifier = pp_print_string

let gen_id_and_args gen_args =
  pp_funcall gen_identifier gen_args

(* Type specification *)
let rec gen_typespec ppf = function
  | TBool -> pp_print_string ppf "Bool"
  | TInt -> pp_print_string ppf "Int"
  | TFloat -> pp_print_string ppf "Float"
  | TID(t) -> fprintf ppf "%a" gen_identifier t
  | TTuple(ts) -> fprintf ppf "(@[%a@])" (pp_list_comma gen_typespec) ts

let gen_id_and_type ppf (id, t) =
  fprintf ppf "%a : %a" gen_identifier id gen_typespec t

let gen_id_and_typeopt ppf (id, topt) =
  match topt with
  | Some t -> gen_id_and_type ppf (id, t)
  | None -> gen_identifier ppf id

(* Literal *)
let gen_literal ppf = function
  | LTrue -> pp_print_string ppf "True"
  | LFalse -> pp_print_string ppf "False"
  | LInt(n) -> pp_print_string ppf n
  | LFloat(n) -> pp_print_string ppf n

(* Operators *)
let gen_uni_op ppf op =
  pp_print_string ppf
    (match op with
     | UPos -> "+" | UNeg -> "-" | UNot -> "!" | UInv -> "~")
let gen_bin_op ppf op =
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
let gen_annotation ppf annot =
  pp_print_string ppf
    (match annot with
     | ALast -> "last")

(* Pattern match *)
let rec gen_pattern ppf = function
  | PWild -> pp_print_string ppf "_"
  | PId(id) -> pp_identifier ppf id
  | PConst(c) -> pp_literal ppf c
  | PTuple(ps) -> fprintf ppf "(@[%a@])" (pp_list_comma gen_pattern) ps
  | PADT(c, ps) -> (gen_id_and_args gen_pattern) ppf (c, ps)

(* A code generation context *)
type genscope =
  | SNode of identifier * identifier (* state_id, node_id *)
  | SSwitch of identifier (* state_id *)
  | SOther

type genctx = {
    names_in : S.t;
    names_out : S.t;
    names_local : S.t;
    names_param : S.t;
    names_var : S.t;
    state_node : identifier;
    switch_node : identifier;
    scope : genscope;
  }

(* Expression *)
let rec gen_expression ctx ppf = function
  | EUniOp(op, e) ->
     fprintf ppf "%a(%a)"
       gen_uni_op op (gen_expression ctx) e
  | EBinOp(op, e1, e2) ->
     fprintf ppf "@[<1>(%a@ %a %a)@]"
       (gen_expression ctx) e1
       gen_bin_op op
       (gen_expression ctx) e2
  | ETuple(es) ->
     fprintf ppf "(@[%a@])"
       (pp_list_comma (gen_expression ctx)) es
  | EConst(l) -> gen_literal ppf l
  | ERetain ->
     begin
       match ctx.scope with
       | SNode(_, nd) -> (gen_expression ctx) ppf (EAnnot(nd, ALast))
       | SSwitch(_) -> fprintf ppf "%a%@last" gen_identifier ctx.state_node
       | _ -> raise RetainError
     end
  | EId(id) -> (gen_id_expr ctx) ppf id
  | EAnnot(id, annot) ->
     begin
       match annot with
       | ALast -> gen_atlast ctx ppf id
     end
  | EFuncall(id, es) -> gen_id_and_args (gen_expression ctx) ppf (id, es)
  | EIf(etest, ethen, eelse) ->
     fprintf ppf "@[if %a@ then %a@ else %a@]"
       (gen_expression ctx) etest
       (gen_expression ctx) ethen
       (gen_expression ctx)  eelse
  | EPat(e, branchs) ->
     fprintf ppf "@[<v 2>%a of:@;%a@]"
       (gen_expression ctx) e
       (pp_print_list (gen_branch ctx)) branchs
and gen_id_expr ctx ppf id =
  if (S.mem id ctx.names_out
      || S.mem id ctx.names_local
      || S.mem id ctx.names_param)
  then
    let state_id =
           match ctx.scope with
           | SNode(sid, _) -> sid
           | SSwitch(sid) -> sid
           | SOther -> assert(false) (* never happened *)
    in
    fprintf ppf "%a_%a" gen_identifier state_id gen_identifier id
  else
    gen_identifier ppf id
and gen_atlast ctx ppf id =
  let state_id =
    match ctx.scope with
    | SNode(sid, _) -> sid
    | SSwitch(sid) -> sid
    | SOther -> assert(false) (* scope error *)
    in
    match id with
    | x when (S.mem x ctx.names_in || S.mem x ctx.names_out)
      -> fprintf ppf "%a%@last" gen_identifier id
    | x when S.mem x ctx.names_local
      -> fprintf ppf "%a_%a_atlast"
           gen_identifier state_id gen_identifier id
    | _ -> assert(false) (* unbound node *)
and gen_branch ctx ppf {branch_pat; branch_expr} =
  fprintf ppf "%a -> %a"
    gen_pattern branch_pat (gen_expression ctx) branch_expr

(* data definition *)
let gen_datadef ctx ppf {data_id; data_type; data_body} =
  fprintf ppf "@[<2>data %a@ = %a@]"
    gen_id_and_typeopt (data_id, data_type)
    (gen_expression ctx) data_body

(* type definition *)
let gen_typedef _ctx ppf {type_id; constructors} =
  let gen_constructor = gen_id_and_args gen_typespec in
  let separator ppf () = fprintf ppf "@ | "  in
  fprintf ppf "@[<2>type %a =@ @[%a@]@]"
    gen_identifier type_id
    (pp_print_list gen_constructor ~pp_sep:separator) constructors

(* function definition *)
let gen_funcdef ctx ppf {func_id;func_type;func_params;func_body} =
  let param_ids = List.map (fun (id, _) -> id) func_params in
  let func_ctx = { ctx with names_var = S.of_list param_ids } in
  let gen_ftype_some ppf t = fprintf ppf " : %a" gen_typespec t in
  fprintf ppf "@[<2>func (@[%a@])%a =@ %a@]"
    (gen_id_and_args gen_id_and_typeopt) (func_id, func_params)
    (pp_opt gen_ftype_some pp_none) func_type
    (gen_expression func_ctx) func_body

(* state definition *)
let gen_statedef ctx ppf {state_id; state_params; nodes; switch} =

  let uc_state_id = String.uncapitalize_ascii state_id in

  (* base context *)
  let state_ctx =
    let node_ids = List.map (fun n -> n.node_id) nodes in
    let names_local = S.diff (S.of_list node_ids) ctx.names_out in
    let names_param =
      List.map (fun (id, _) -> id) state_params
      |> S.of_list
    in
    { ctx with names_local = names_local; names_param = names_param }
  in

  (* parameter *)
  let param_len = List.length state_params in
  let gen_state_param pos ppf (param_id, t) =
    let nid = uc_state_id ^ "_" ^ param_id in
    let pat = List.init param_len (fun i -> if i == pos then "x" else "_") in
    fprintf ppf "@[<2>node %a =@ " gen_id_and_type (nid, t);
    fprintf ppf "@[<v 2>%a%@last of:@;" gen_identifier state_ctx.state_node;
    fprintf ppf "%a -> x@;" (gen_id_and_args pp_print_string) (state_id, pat);
    fprintf ppf "_ -> %s@last@]@]" nid
  in

  (* node *)
  let gen_state_node ppf {init; node_id; node_type; node_body} =
    let nid = uc_state_id ^ "_" ^ node_id in
    let node_ctx = { state_ctx with scope = SNode(uc_state_id, nid) } in
    let gen_init_some ppf e =
      fprintf ppf " init[%a]" (gen_expression state_ctx) e
    in
    fprintf ppf "@[<2>node%a %a =@ "
      (pp_opt gen_init_some pp_none) init
      gen_id_and_typeopt (nid, node_type);
    (gen_expression node_ctx) ppf node_body;
    fprintf ppf "@]";
    if S.mem node_id node_ctx.names_out then ()
    else
      begin
        match init with
        | None -> ()
        | Some(l) ->
           fprintf ppf "@;@;";
           fprintf ppf "@[<2>node %a_atlast =@ " gen_identifier nid;
           fprintf ppf "@[if %a%@last@ " gen_identifier node_ctx.switch_node;
           fprintf ppf "then %a@ " (gen_expression node_ctx) l;
           fprintf ppf "else %s%@last@]@]" nid
      end
  in

  (* switch *)
  let gen_state_swich ppf body =
    let nid = uc_state_id ^ "_state" in
    let switch_ctx = { state_ctx with scope = SSwitch(uc_state_id) } in
    fprintf ppf "@[<2>node %s = @ " nid;
    (gen_expression switch_ctx) ppf body;
    fprintf ppf "@]"
  in

  (* body for state definition *)
  fprintf ppf "@[<v>##### begin state %s #####@;" state_id;
  List.iteri
    (fun i param -> gen_state_param i ppf param; fprintf ppf "@;@;")
    state_params;
  (pp_list_break2 gen_state_node) ppf nodes;
  fprintf ppf "@;@;";
  gen_state_swich ppf switch;
  fprintf ppf "@;";
  fprintf ppf "##### end state %s #####@]" state_id

(* toplevel definition *)
let gen_definition ctx ppf = function
  | DataDef(d) -> gen_datadef ctx ppf d
  | TypeDef(d) -> gen_typedef ctx ppf d
  | FuncDef(d) -> gen_funcdef ctx ppf d
  | StateDef(d) -> gen_statedef ctx ppf d

(* switch module *)
let gen_switchmodule ppf {module_id; in_nodes; out_nodes; use; init; definitions} =

  (* base context *)
  let ctx =
    {
      names_in = S.of_list (List.map (fun (id, _, _) -> id) in_nodes);
      names_out = S.of_list (List.map (fun (id, _) -> id) out_nodes);
      names_local = S.empty;
      names_param = S.empty;
      names_var = S.empty;
      state_node = "state";
      switch_node = "switch";
      scope = SOther
    }
  in

  (* list of all state definition *)
  let states =
    List.fold_left (fun lst def ->
        match def with
        | StateDef d -> d :: lst
        | _ -> lst
      ) [] definitions
  |> List.rev
  in

  (* print in node *)
  let gen_in_node ppf (id, init, t) =
    let gen_init_some ppf l = fprintf ppf "(%a)" gen_literal l in
    fprintf ppf "%a%a : %a"
      gen_identifier id
      (pp_opt gen_init_some pp_none) init
      gen_typespec t
  in

  (* generate state type definition *)
  let gen_statetype ppf () =
    let get_constructor state_def =
      (state_def.state_id, List.map (fun (_, t) -> t) state_def.state_params)
    in
    let constructors = List.map get_constructor states in
    let gen_constructor ppf (c, params) =
      match params with
      | [] -> gen_identifier ppf c
      | _ -> (gen_id_and_args gen_typespec) ppf (c,params)
    in
    let separator ppf () = fprintf ppf "@ | "  in
    fprintf ppf "@[<2>type State =@ @[%a@]@]"
      (pp_print_list gen_constructor ~pp_sep:separator) constructors
  in

  (* generate header *)
  let gen_header ppf () =
    fprintf ppf "@[<v>module %a" gen_identifier module_id;
    begin
      match in_nodes with
      | [] -> ()
      | _ -> fprintf ppf "@;in @[<v>%a@]"
               (pp_list_comma gen_in_node) in_nodes
    end;
    begin
      match out_nodes with
      | [] -> ()
      | _ -> fprintf ppf "@;out @[<v>%a@]"
               (pp_list_comma gen_id_and_type) out_nodes
    end;
    begin
      match use with
      | [] -> ()
      | _ -> fprintf ppf "@;use @[%a@]"
               (pp_list_comma gen_identifier) use
    end;
    fprintf ppf "@]"
  in

  (* print branch's pattern for matching state ADT constructor *)
  let gen_state_cons_pattern ppf st =
    let param_len = List.length st.state_params  in
    let pat = List.init param_len (fun _ -> "_") in
    match pat with
    | [] -> gen_identifier ppf st.state_id
    | _ -> (gen_id_and_args pp_print_string) ppf (st.state_id, pat)
  in

  (* print actual onode *)
  let gen_onode_def ppf (onode_id, t) =
    let gen_state_branch ppf st =
      let nid = (String.uncapitalize_ascii st.state_id) ^ "_" ^ onode_id in
        fprintf ppf "%a -> %a"
          gen_state_cons_pattern st gen_identifier nid
    in
    fprintf ppf "@[<2>node %a =@ " gen_id_and_type (onode_id, t);
    fprintf ppf "@[<v 2>%a%@last of:@;" gen_identifier ctx.state_node;
    (pp_print_list gen_state_branch) ppf states;
    fprintf ppf "@]@]"
  in

  (* print state node *)
  let gen_statenode ppf () =
    let gen_init_state ppf (cons, param) =
      match param with
      | [] -> gen_identifier ppf cons
      | _ -> gen_id_and_args gen_literal ppf (cons, param)
    in
    let gen_state_branch ppf st =
      let nid = (String.uncapitalize_ascii st.state_id) ^ "_state" in
      fprintf ppf "%a -> %a"
        gen_state_cons_pattern st gen_identifier nid
    in
    fprintf ppf "@[<2>node init[%a] %a =@ "
      gen_init_state init gen_identifier ctx.state_node;
    fprintf ppf "@[<v 2>%a%@last of:@;" gen_identifier ctx.state_node;
    (pp_print_list gen_state_branch) ppf states;
    fprintf ppf "@]@]";
  in

  (* print switch node *)
  let gen_switchnode ppf () =
    let gen_state_branch ppf st =
      fprintf ppf "%a -> " gen_state_cons_pattern st;
      fprintf ppf "@[<v 2>%a of:@;" gen_identifier ctx.state_node;
      fprintf ppf "%a -> False@;" gen_state_cons_pattern st;
      fprintf ppf "_ -> True@]"
    in
    fprintf ppf "@[<2>node init[True] %a =@ " gen_identifier ctx.switch_node;
    fprintf ppf "@[<v 2>%a%@last of:@;" gen_identifier ctx.state_node;
    (pp_print_list gen_state_branch) ppf states;
    fprintf ppf "@]@]"
  in

  (* body for switch module definition *)
  pp_open_vbox ppf 0;
  gen_header ppf ();
  fprintf ppf "@;@;";
  gen_statetype ppf ();
  fprintf ppf "@;@;";
  (pp_list_break2 (gen_definition ctx)) ppf definitions;
  fprintf ppf "@;@;";
  (pp_list_break2 gen_onode_def) ppf out_nodes;
  fprintf ppf "@;@;";
  gen_statenode ppf ();
  fprintf ppf "@;@;";
  gen_switchnode ppf ();
  pp_close_box ppf ()

let codegen ochan prog =
  let ppf = (formatter_of_out_channel ochan) in
  gen_switchmodule ppf prog;
  pp_print_newline ppf ()
