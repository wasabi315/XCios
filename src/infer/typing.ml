(* Type inference *)
open Syntax
open Type
open Env
open Extension
open Extension.Format

exception TypeError of string

(* Raise type error with given message `msg`. *)
let raise_err msg = raise (TypeError msg)

(* Raise type error with message. *)
let raise_err_pp fmt = kasprintf (fun msg -> raise (TypeError msg)) fmt

(* Raise type imcompatible error with `t1` and `t2`. *)
let raise_imcompatible t1 t2 = raise_err_pp "%a and %a is not compatible" pp_t t1 pp_t t2

(* Adjusting level of unification target pointed by another free variable
   with `id` and `level`. *)
let rec adjust_level id level = function
  | TVar ({ contents } as r) ->
    (match contents with
     | TVGeneric _ -> assert false
     | TVBound t -> adjust_level id level t
     | TVFree (id', level') ->
       if id = id' then raise_err "recursive type" else r := TVFree (id', min level level'))
  | TTuple ts -> List.iter (adjust_level id level) ts
  | _ -> ()
;;

(* Unify type `t1` and `t2`. *)
let rec unify t1 t2 =
  match t1, t2 with
  | TBool, TBool | TInt, TInt | TFloat, TFloat | TUnit, TUnit -> t1
  | TEmpty, _
  | _, TEmpty
  | TId ("", _), _
  | _, TId ("", _)
  | TState ("", _), _
  | _, TState ("", _) -> assert false
  | TState (file1, mname1), TState (file2, mname2) ->
    if file1 = file2 && mname1 = mname2 then t1 else raise_imcompatible t1 t2
  | TId (file1, tname1), TId (file2, tname2) ->
    if file1 = file2 && tname1 = tname2 then t1 else raise_imcompatible t1 t2
  | TTuple xs, TTuple ys ->
    let ts = unify_list xs ys in
    TTuple ts
  | TVar ({ contents = TVBound t1 } as r), t2 | t1, TVar ({ contents = TVBound t2 } as r)
    ->
    let t = unify t1 t2 in
    r := TVBound t;
    t
  | TVar ({ contents = TVFree (id, level) } as r), t
  | t, TVar ({ contents = TVFree (id, level) } as r) ->
    adjust_level id level t;
    r := TVBound t;
    t
  | TMode ("", _, _), _ | _, TMode ("", _, _) -> assert false
  | TMode (file1, mname1, t1), TMode (file2, mname2, t2) ->
    if file1 = file2 && mname1 = mname2
    then (
      let t = unify t1 t2 in
      TMode (file1, mname1, t))
    else raise_imcompatible t1 t2
  | TMode (_, _, t1), t2 | t1, TMode (_, _, t2) -> unify t1 t2
  | _, _ -> raise_imcompatible t1 t2

(* Unify type list `ts1` and `ts2`. *)
and unify_list ts1 ts2 =
  let len1 = List.length ts1 in
  let len2 = List.length ts2 in
  if len1 != len2
  then raise_imcompatible (TTuple ts1) (TTuple ts2)
  else List.map2 unify ts1 ts2
;;

(* Generalize free variables. *)
let rec generalize level = function
  | TTuple ts -> List.iter (generalize level) ts
  | TVar ({ contents = TVFree (id, level') } as r) ->
    if level' > level then r := TVGeneric id else ()
  | TVar { contents = TVBound t } -> generalize level t
  | _ -> ()
;;

(* Instantiate generic variables. *)
let instantiate level t =
  let general_to_free = Hashtbl.create 10 in
  let rec visit = function
    | TTuple ts -> TTuple (List.map visit ts)
    | TVar { contents = TVGeneric id } ->
      (match Hashtbl.find_opt general_to_free id with
       | Some var -> var
       | None ->
         let newvar = gen_tvar_free level in
         Hashtbl.add general_to_free id newvar;
         newvar)
    | TVar { contents = TVBound t' } -> visit t'
    | _ as t -> t
  in
  visit t
;;

let rec read_typespec tenv level = function
  | TEmpty -> gen_tvar_free level
  | TMode ("", mode, t) ->
    (match Idmap.find_opt mode tenv.ms with
     | Some file ->
       let t' = read_typespec tenv level t in
       TMode (file, mode, t')
     | None -> raise_err_pp "Unknown : %a" pp_print_string mode)
  | TMode (_, _, _) -> assert false
  | TId ("", name) ->
    (match Idmap.find_opt name tenv.ts with
     | Some file -> TId (file, name)
     | None -> raise_err_pp "Unknown : %a" pp_print_string name)
  | TId (_, _) -> assert false
  | TTuple ts ->
    let ts' = List.map (read_typespec tenv level) ts in
    TTuple ts'
  | TVar { contents = TVBound t } -> read_typespec tenv level t
  | _ as t -> t
;;

(* Return if given type is not polymorphic type. *)
let rec is_concrete = function
  | TBool | TInt | TFloat | TUnit | TId (_, _) | TState (_, _) -> true
  | TTuple ts -> List.for_all is_concrete ts
  | TVar { contents = TVBound t } -> is_concrete t
  | TVar _ -> false
  | TMode (_, _, t) -> is_concrete t
  | TEmpty -> assert false
;;

let rec flatten_type = function
  | TTuple ts ->
    let ts = List.map flatten_type ts in
    TTuple ts
  | TVar { contents = TVBound t } -> flatten_type t
  | t -> t
;;

let deref_idinfo_type (id, idinfo) =
  let idinfo = map_idinfo_type flatten_type idinfo in
  id, idinfo
;;

let rec deref_pattern_type (ast, t) =
  let t = flatten_type t in
  match ast with
  | PWild | PId _ | PConst _ -> ast, t
  | PTuple ps ->
    let ps = List.map deref_pattern_type ps in
    PTuple ps, t
  | PVariant (c, p) ->
    let c = deref_idinfo_type c in
    let p = deref_pattern_type p in
    PVariant (c, p), t
;;

let rec deref_expr_type (ast, t) =
  let t = flatten_type t in
  match ast with
  | EUniOp (op, e) ->
    let e = deref_expr_type e in
    EUniOp (op, e), t
  | EBinOp (op, e1, e2) ->
    let e1 = deref_expr_type e1 in
    let e2 = deref_expr_type e2 in
    EBinOp (op, e1, e2), t
  | EVariant (c, e) ->
    let c = deref_idinfo_type c in
    let e = deref_expr_type e in
    EVariant (c, e), t
  | ETuple es ->
    let es = List.map deref_expr_type es in
    ETuple es, t
  | EConst _ | ERetain -> ast, t
  | EId idref -> EId (deref_idinfo_type idref), t
  | EAnnot (idref, annot) -> EAnnot (deref_idinfo_type idref, annot), t
  | EFuncall (f, args) ->
    let f = deref_idinfo_type f in
    let args = List.map deref_expr_type args in
    EFuncall (f, args), t
  | EIf (etest, ethen, eelse) ->
    let etest = deref_expr_type etest in
    let ethen = deref_expr_type ethen in
    let eelse = deref_expr_type eelse in
    EIf (etest, ethen, eelse), t
  | ELet (bs, body) ->
    let bs = List.map deref_binder_type bs in
    let body = deref_expr_type body in
    ELet (bs, body), t
  | ECase (e, bs) ->
    let e = deref_expr_type e in
    let bs = List.map deref_branch_type bs in
    ECase (e, bs), t

and deref_binder_type { binder_id; binder_body } =
  let id, t = binder_id in
  let t = flatten_type t in
  let body = deref_expr_type binder_body in
  { binder_id = id, t; binder_body = body }

and deref_branch_type { branch_pat; branch_body } =
  let pat = deref_pattern_type branch_pat in
  let body = deref_expr_type branch_body in
  { branch_pat = pat; branch_body = body }
;;

(*----- inference functions -----*)
let infer_idref env _tenv level (id, _) =
  let idinfo =
    match Idmap.find_opt id env with
    | Some UnknownId -> assert false
    | Some idinfo -> map_idinfo_type (instantiate level) idinfo
    | None -> raise_err_pp "Unknown %a" pp_identifier id
  in
  id, idinfo
;;

let infer_literal _env _tenv _level ast =
  match ast with
  | LTrue | LFalse -> TBool
  | LInt _ -> TInt
  | LFloat _ -> TFloat
  | LUnit -> TUnit
;;

let rec infer_pattern env _tenv level (ast, _) =
  (* return result + id-type bind *)
  match ast with
  | PWild ->
    let var = gen_tvar_free level in
    let res = ast, var in
    res, []
  | PId id ->
    let var = gen_tvar_free level in
    let res = ast, var in
    res, [ id, var ]
  | PConst l ->
    let tl = infer_literal env _tenv level l in
    let res = PConst l, tl in
    res, []
  | PTuple ps ->
    let ps', binds = List.map (infer_pattern env _tenv level) ps |> List.split in
    let _, tps = List.split ps' in
    let res = PTuple ps', TTuple tps in
    res, List.concat binds
  | PVariant (c, p) ->
    let ((cid, consinfo) as c) = infer_idref env _tenv level c in
    let ((_, tp) as p'), binds = infer_pattern env _tenv level p in
    (match consinfo with
     | ValueCons (_, tp2, tret) ->
       let _ = unify tp tp2 in
       let res = PVariant (c, p'), tret in
       res, binds
     | _ -> raise_err_pp "expected value constructor : %a" pp_identifier cid)
;;

let rec infer_expression env tenv level (ast, _) =
  let infer_uniop op e1 =
    let ((_, te1) as e1') = infer_expression_acc env tenv level e1 in
    let ast' = EUniOp (op, e1') in
    match op with
    | UInv | UPlus | UMinus ->
      let _ = unify TInt te1 in
      ast', TInt
    | UFPlus | UFMinus ->
      let _ = unify TFloat te1 in
      ast', TFloat
    | UNot ->
      let _ = unify TBool te1 in
      ast', TBool
  in
  let infer_binop op e1 e2 =
    let ((_, te1) as e1') = infer_expression_acc env tenv level e1 in
    let ((_, te2) as e2') = infer_expression_acc env tenv level e2 in
    let ast' = EBinOp (op, e1', e2') in
    match op with
    | BMul | BDiv | BAdd | BSub | BMod | BShl | BShr | BAnd | BOr | BXor ->
      let _ = unify TInt te1 in
      let _ = unify TInt te2 in
      ast', TInt
    | BLt | BLeq | BGt | BGeq ->
      let _ = unify TInt te1 in
      let _ = unify TInt te2 in
      ast', TBool
    | BFMul | BFDiv | BFAdd | BFSub ->
      let _ = unify TFloat te1 in
      let _ = unify TFloat te2 in
      ast', TFloat
    | BFLt | BFLeq | BFGt | BFGeq ->
      let _ = unify TFloat te1 in
      let _ = unify TFloat te2 in
      ast', TBool
    | BLand | BLor ->
      let _ = unify TBool te1 in
      let _ = unify TBool te2 in
      ast', TBool
    | BEq | BNeq ->
      let tvar = gen_tvar_free level in
      let _ = unify tvar te1 in
      let _ = unify tvar te2 in
      ast', TBool
  in
  let infer_retain () =
    match Idmap.find "Retain" env with
    | LocalId t -> ast, t
    | _ -> assert false (* fail in register "Retain" *)
  in
  let infer_idexpr idref =
    let ((id, idinfo) as idref) = infer_idref env tenv level idref in
    match idinfo with
    | LocalId t
    | ConstId (_, t)
    | ModuleParam t
    | ModuleConst t
    | StateParam t
    | StateConst t
    | NodeId (_, _, t)
    | InaccNodeId (_, _, t) -> EId idref, t
    | _ -> raise_err_pp "invalid identifier reference : %a" pp_identifier id
  in
  let infer_annot idref annot =
    let ((id, idinfo) as idref) = infer_idref env tenv level idref in
    match idinfo, annot with
    | InaccNodeId (_, _, TMode (_, _, _)), _ | NodeId (_, _, TMode (_, _, _)), _ ->
      raise_err_pp
        "past values of I/O node with mode cannot be accessed: %a"
        pp_identifier
        id
    | NodeId (_, false, _), ALast ->
      raise_err_pp "node %a is not initialized" pp_identifier id
    | NodeId (_, _, t), ALast -> EAnnot (idref, ALast), t
    | _ -> raise_err_pp "expected node : %a" pp_identifier id
  in
  let infer_variant c v =
    let ((cid, cinfo) as c) = infer_idref env tenv level c in
    let ((_, tv) as v) = infer_expression_acc env tenv level v in
    let ast = EVariant (c, v) in
    match cinfo with
    | ValueCons (_, tv2, tret) ->
      let _ = unify tv tv2 in
      ast, tret
    | StateCons (file, mname, tv2) ->
      let _ = unify tv tv2 in
      ast, TState (file, mname)
    | _ -> raise_err_pp "expected constructor : %a" pp_identifier cid
  in
  let infer_tuple es =
    let es' = List.map (infer_expression_acc env tenv level) es in
    let _, tes = List.split es' in
    let ast' = ETuple es' in
    ast', TTuple tes
  in
  let infer_funcall f args =
    let ((fid, finfo) as f) = infer_idref env tenv level f in
    let args = List.map (infer_expression_acc env tenv level) args in
    let _, targs = List.split args in
    let ast = EFuncall (f, args) in
    match finfo with
    | FunId (_, targs2, tret) ->
      let _ = unify_list targs targs2 in
      ast, tret
    | _ -> raise_err_pp "expected a function : %a" pp_identifier fid
  in
  let infer_let binds body =
    let infer_binder (acc, nowenv) { binder_id = id, tid; binder_body = body } =
      let tid = read_typespec tenv level tid in
      let ((_, tbody) as body') = infer_expression_acc nowenv tenv (level + 1) body in
      let () = generalize level tbody in
      let _ = unify tid tbody in
      let env = add_env_shadowing id (LocalId tbody) nowenv in
      let res = { binder_id = id, tbody; binder_body = body' } in
      res :: acc, env
    in
    let binds', newenv = List.fold_left infer_binder ([], env) binds in
    let ((_, tbody) as body') = infer_expression_acc newenv tenv level body in
    let ast' = ELet (List.rev binds', body') in
    ast', tbody
  in
  let infer_if etest ethen eelse =
    let ((_, ttest) as etest') = infer_expression_acc env tenv level etest in
    let ((_, tthen) as ethen') = infer_expression_acc env tenv level ethen in
    let ((_, telse) as eelse') = infer_expression_acc env tenv level eelse in
    let ast' = EIf (etest', ethen', eelse') in
    let _ = unify ttest TBool in
    let _ = unify tthen telse in
    ast', tthen
  in
  let infer_case expr branchs =
    let infer_branch texpr { branch_pat; branch_body } =
      let ((_, tpat) as pat'), newbinds = infer_pattern env tenv level branch_pat in
      let newenv =
        List.fold_right
          (fun (id, t) env -> add_env_shadowing id (LocalId t) env)
          newbinds
          env
      in
      let ((_, tbody) as body') = infer_expression_acc newenv tenv level branch_body in
      let res = { branch_pat = pat'; branch_body = body' } in
      let _ = unify texpr tpat in
      res, tbody
    in
    let ((_, texpr) as expr') = infer_expression_acc env tenv (level + 1) expr in
    let () = generalize level texpr in
    let branchs', tbranchs = List.map (infer_branch texpr) branchs |> List.split in
    let ast' = ECase (expr', branchs') in
    let tvar = gen_tvar_free level in
    let _ = List.map (unify tvar) tbranchs in
    ast', tvar
  in
  match ast with
  | EUniOp (op, e1) -> infer_uniop op e1
  | EBinOp (op, e1, e2) -> infer_binop op e1 e2
  | EVariant (c, v) -> infer_variant c v
  | ETuple es -> infer_tuple es
  | EConst l ->
    let tl = infer_literal env tenv level l in
    EConst l, tl
  | ERetain -> infer_retain ()
  | EId id -> infer_idexpr id
  | EAnnot (id, annot) -> infer_annot id annot
  | EFuncall (f, args) -> infer_funcall f args
  | EIf (etest, ethen, eelse) -> infer_if etest ethen eelse
  | ELet (binders, body) -> infer_let binders body
  | ECase (e, branchs) -> infer_case e branchs

(* check accessiblity in addition *)
and infer_expression_acc env tenv level ast =
  match infer_expression env tenv level ast with
  | EId (id, InaccNodeId (modev, _, _)), _ ->
    raise_err_pp
      "%a is inaccessible when its mode is %a"
      pp_identifier
      id
      pp_identifier
      modev
  | e -> e
;;

let infer_typedef _env tenv def =
  let conses = Idmap.map (read_typespec tenv 1) def.type_conses in
  { def with type_conses = conses }
;;

let infer_constdef env tenv def =
  let t = read_typespec tenv 1 def.const_type in
  let ((_, tbody) as body) =
    infer_expression env tenv 1 def.const_body |> deref_expr_type
  in
  let t = unify t tbody in
  if not (is_concrete t)
  then raise_err_pp "type of constant is not concrete : %a" pp_identifier def.const_id
  else { def with const_body = body; const_type = t }
;;

let infer_fundef env tenv def =
  let env =
    List.fold_right
      (fun (id, t) e -> add_env_shadowing id (LocalId (read_typespec tenv 1 t)) e)
      def.fun_params
      env
  in
  let ((_, tbody) as body) =
    infer_expression env tenv 1 def.fun_body |> deref_expr_type
  in
  let params =
    List.map
      (fun (id, _) ->
        match Idmap.find id env with
        | LocalId t -> id, flatten_type t
        | _ -> assert false)
      def.fun_params
  in
  let tret = read_typespec tenv 1 def.fun_rettype |> unify tbody |> flatten_type in
  let () = generalize 0 tret in
  { def with fun_params = params; fun_rettype = tret; fun_body = body }
;;

let infer_node env tenv undefined_out_nodes def =
  let t =
    match Idmap.find def.node_id env with
    | NodeId (_, _, t) -> t
    | InaccNodeId (modev, _, _) ->
      raise_err_pp
        "%a is inaccessible when its mode is %a"
        pp_identifier
        def.node_id
        pp_identifier
        modev
    | _ -> assert false
  in
  let env = add_env "Retain" (LocalId t) env in
  let init =
    match def.node_init with
    | Some expr ->
      let ((_, texpr) as expr) = infer_expression env tenv 1 expr in
      let _ = unify t texpr in
      Some expr
    | None -> None
  in
  let ((_, tbody) as body) = infer_expression_acc env tenv 1 def.node_body in
  let t =
    (* Keep mode information *)
    match t, unify t tbody with
    | TMode (_, _, _), (TMode (_, _, _) as t) -> t
    | TMode (file, mode, _), t -> TMode (file, mode, t)
    | _, t -> t
  in
  (match def.node_attr with
   | OutputNode -> Hashset.remove undefined_out_nodes def.node_id
   | _ -> ());
  { def with node_init = init; node_body = body; node_type = t }
;;

let infer_newnode env tenv undefined_out_nodes def =
  let ((_, midinfo) as mid) = infer_idref env tenv 1 def.newnode_module in
  match midinfo with
  | ModuleCons (_, pts, its, ots) ->
    let margs = List.map (fun e -> infer_expression env tenv 1 e) def.newnode_margs in
    let _, tmargs = List.split margs in
    let _ = unify_list pts tmargs in
    let inputs = List.map (fun e -> infer_expression env tenv 1 e) def.newnode_inputs in
    let _, its2 = List.split inputs in
    let _ = unify_list its its2 in
    (* If an input node of the instance expects type TMode(...), the actual input should also have type TMode(...) *)
    List.iter2
      (fun t1 t2 ->
        match t1, t2 with
        | TMode (_, _, _), TMode (_, _, _) -> ()
        | (TMode (_, _, _) as t1), t2 -> raise_imcompatible t1 t2
        | _ -> ())
      its
      its2;
    let ots2 =
      def.newnode_binds
      |> List.fold_left (fun acc (_, _, t) -> read_typespec tenv 1 t :: acc) []
      |> List.rev
    in
    let ots = unify_list ots ots2 in
    let margs = List.map deref_expr_type margs in
    let inputs = List.map deref_expr_type inputs in
    let binds =
      List.map2 (fun (attr, id, _) t -> attr, id, flatten_type t) def.newnode_binds ots
    in
    List.iter
      (function
       | OutputNode, id, _ -> Hashset.remove undefined_out_nodes id
       | (NormalNode | SharedNode), id, TMode _ ->
         raise_err_pp
           "output nodes with mode cannot be bound to normal/shared nodes: %a"
           pp_identifier
           id
       | _ -> ())
      binds;
    { def with
      newnode_binds = binds
    ; newnode_module = mid
    ; newnode_margs = margs
    ; newnode_inputs = inputs
    }
  | _ -> raise_err_pp "expected module : %a" pp_identifier def.newnode_id
;;

let infer_param _env tenv (id, t) = id, read_typespec tenv 1 t

let infer_header_node env tenv (id, init, t) =
  let t = read_typespec tenv 1 t in
  match init with
  | None -> id, None, t
  | Some expr ->
    let ((_, texpr) as expr) = infer_expression env tenv 1 expr |> deref_expr_type in
    let _ = unify t texpr in
    id, Some expr, t
;;

let infer_mode_annot env tenv annot =
  let undefined_out_nodes = Hashset.create 10 in
  let annot =
    List.map
      (fun (id, mode) ->
        let mode = infer_idref env tenv 1 mode in
        (match infer_idref env tenv 1 (id, UnknownId), mode with
         | (node_id, NodeId (OutputNode, _, _)), (_, ModeValue (_, _, _, Acc)) ->
           Hashset.add undefined_out_nodes node_id
         | _ -> ());
        id, mode)
      annot
  in
  let env =
    List.fold_left
      (fun env -> function
        | _, (_, ModeValue (_, _, _, Acc)) -> env
        | id, (modev, ModeValue (_, _, _, Inacc)) ->
          let attr, t =
            match Idmap.find id env with
            | NodeId (attr, _, t) -> attr, t
            | _ -> assert false
          in
          add_env_shadowing id (InaccNodeId (modev, attr, t)) env
        | _ -> assert false)
      env
      annot
  in
  env, annot, undefined_out_nodes
;;

let infer_whole_nodes env tenv undefined_out_nodes nodes newnodes =
  let add_env_node def env =
    match def.node_attr with
    | NormalNode ->
      let t = read_typespec tenv 1 def.node_type in
      add_env def.node_id (NodeId (NormalNode, Option.is_some def.node_init, t)) env
    | _ -> env
  in
  let add_env_newnode def env =
    List.fold_left
      (fun env (attr, id, t) ->
        match attr with
        | NormalNode ->
          let t = read_typespec tenv 1 t in
          add_env id (NodeId (NormalNode, false, t)) env
        | _ -> env)
      env
      def.newnode_binds
  in
  let make_env env =
    env
    |> Idmap.fold (fun _ def env -> add_env_node def env) nodes
    |> Idmap.fold (fun _ def env -> add_env_newnode def env) newnodes
  in
  let deref_nodedef_type def =
    let t = flatten_type def.node_type in
    let init =
      match def.node_init with
      | None -> None
      | Some expr -> Some (deref_expr_type expr)
    in
    let body = deref_expr_type def.node_body in
    let () =
      if not (is_concrete t)
      then raise_err_pp "type of node is not concrete : %a" pp_identifier def.node_id
      else ()
    in
    { def with node_type = t; node_init = init; node_body = body }
  in
  (*
     Types of newnode elements must be determined by module signature.
     You need not dereference types of them.
  *)
  let env = make_env env in
  let nodes = Idmap.map (infer_node env tenv undefined_out_nodes) nodes in
  let newnodes = Idmap.map (infer_newnode env tenv undefined_out_nodes) newnodes in
  let nodes = Idmap.map deref_nodedef_type nodes in
  if not (Hashset.is_empty undefined_out_nodes)
  then
    raise_err_pp
      "undefined output node(s) : %a"
      (pp_list_comma pp_identifier)
      (Hashset.to_list undefined_out_nodes);
  nodes, newnodes, env
;;

let infer_module env tenv def =
  let infer_module_params env tenv def =
    let params = List.map (infer_param env tenv) def.module_params in
    let def = { def with module_params = params } in
    let env =
      List.fold_right (fun (id, t) env -> add_env id (ModuleParam t) env) params env
    in
    def, env
  in
  let infer_module_header_nodes env tenv def =
    let in_nodes = List.map (infer_header_node env tenv) def.module_in in
    let out_nodes = List.map (infer_header_node env tenv) def.module_out in
    let def = { def with module_in = in_nodes; module_out = out_nodes } in
    let env =
      env
      |> List.fold_right
           (fun (id, init, t) env ->
             add_env id (NodeId (InputNode, Option.is_some init, t)) env)
           in_nodes
      |> List.fold_right
           (fun (id, init, t) env ->
             add_env id (NodeId (OutputNode, Option.is_some init, t)) env)
           out_nodes
    in
    def, env
  in
  let infer_module_mode_annot env tenv def =
    let env, annot, undef_out_nodes = infer_mode_annot env tenv def.module_mode_annot in
    let def = { def with module_mode_annot = annot } in
    def, env, undef_out_nodes
  in
  let infer_module_consts env tenv def =
    let cs, all, env =
      List.fold_left
        (fun (cs, all, env) id ->
          let def = Idmap.find id cs in
          let def = infer_constdef env tenv def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (MConst def) all in
          let env = add_env def.const_id (ModuleConst def.const_type) env in
          cs, all, env)
        (def.module_consts, def.module_all, env)
        def.module_consts_ord
    in
    let def = { def with module_consts = cs; module_all = all } in
    def, env
  in
  let infer_module_nodes env tenv undefined_out_nodes def =
    let nodes, newnodes, env =
      infer_whole_nodes env tenv undefined_out_nodes def.module_nodes def.module_newnodes
    in
    let all =
      def.module_all
      |> Idmap.fold (fun id def all -> Idmap.add id (MNode def) all) nodes
      |> Idmap.fold (fun id def all -> Idmap.add id (MNewnode def) all) newnodes
    in
    let def =
      { def with module_nodes = nodes; module_newnodes = newnodes; module_all = all }
    in
    def, env
  in
  let def, env = infer_module_params env tenv def in
  let def, env = infer_module_header_nodes env tenv def in
  let def, env, undefined_out_nodes = infer_module_mode_annot env tenv def in
  let def, env = infer_module_consts env tenv def in
  let def, _ = infer_module_nodes env tenv undefined_out_nodes def in
  def
;;

let infer_state env tenv file mname def =
  let make_env def env =
    List.fold_right
      (fun (id, t) env -> add_env id (StateParam t) env)
      def.state_params
      env
  in
  let infer_state_mode_annot env tenv def =
    let env, annot, undef_out_nodes = infer_mode_annot env tenv def.state_mode_annot in
    let def = { def with state_mode_annot = annot } in
    def, env, undef_out_nodes
  in
  let infer_state_consts env tenv def =
    let cs, all, env =
      List.fold_left
        (fun (cs, all, env) id ->
          let def = Idmap.find id cs in
          let def = infer_constdef env tenv def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (SConst def) all in
          let env = add_env def.const_id (StateConst def.const_type) env in
          cs, all, env)
        (def.state_consts, def.state_all, env)
        def.state_consts_ord
    in
    let def = { def with state_consts = cs; state_all = all } in
    def, env
  in
  let infer_state_nodes env tenv undefined_out_nodes def =
    let nodes, newnodes, env =
      infer_whole_nodes env tenv undefined_out_nodes def.state_nodes def.state_newnodes
    in
    let all =
      def.state_all
      |> Idmap.fold (fun id def all -> Idmap.add id (SNode def) all) nodes
      |> Idmap.fold (fun id def all -> Idmap.add id (SNewnode def) all) newnodes
    in
    let def =
      { def with state_nodes = nodes; state_newnodes = newnodes; state_all = all }
    in
    def, env
  in
  let infer_state_switch env tenv switch_expr : expression =
    let t = TState (file, mname) in
    let env = add_env "Retain" (LocalId t) env in
    let astsw, tsw = infer_expression_acc env tenv 1 switch_expr |> deref_expr_type in
    let t = unify t tsw in
    astsw, t
  in
  let env = make_env def env in
  let def, env, undefined_out_nodes = infer_state_mode_annot env tenv def in
  let def, env = infer_state_consts env tenv def in
  let def, env = infer_state_nodes env tenv undefined_out_nodes def in
  let sw = infer_state_switch env tenv def.state_switch in
  { def with state_switch = sw }
;;

let infer_smodule env tenv file def =
  let infer_smodule_params env tenv def =
    let params = List.map (infer_param env tenv) def.smodule_params in
    let def = { def with smodule_params = params } in
    let env =
      List.fold_right (fun (id, t) env -> add_env id (ModuleParam t) env) params env
    in
    def, env
  in
  let infer_state_params env tenv def =
    let states =
      Idmap.map
        (fun st ->
          let params = List.map (infer_param env tenv) st.state_params in
          { st with state_params = params })
        def.smodule_states
    in
    let all =
      Idmap.fold (fun id def all -> Idmap.add id (SMState def) all) states def.smodule_all
    in
    let def = { def with smodule_states = states; smodule_all = all } in
    let env =
      Idmap.fold
        (fun _ state env ->
          let cons = state.state_id in
          let _, tparams = List.split state.state_params in
          let tvalue =
            match tparams with
            | [] -> TUnit
            | [ t ] -> t
            | _ -> TTuple tparams
          in
          add_env cons (StateCons (file, def.smodule_id, tvalue)) env)
        states
        env
    in
    def, env
  in
  let infer_smodule_header_nodes env tenv def =
    let in_nodes = List.map (infer_header_node env tenv) def.smodule_in in
    let out_nodes = List.map (infer_header_node env tenv) def.smodule_out in
    let shared_nodes = List.map (infer_header_node env tenv) def.smodule_shared in
    let def =
      { def with
        smodule_in = in_nodes
      ; smodule_out = out_nodes
      ; smodule_shared = shared_nodes
      }
    in
    let env =
      env
      |> List.fold_right
           (fun (id, init, t) env ->
             add_env id (NodeId (InputNode, Option.is_some init, t)) env)
           def.smodule_in
      |> List.fold_right
           (fun (id, init, t) env ->
             add_env id (NodeId (OutputNode, Option.is_some init, t)) env)
           def.smodule_out
      |> List.fold_right
           (fun (id, init, t) env ->
             add_env id (NodeId (SharedNode, Option.is_some init, t)) env)
           def.smodule_shared
    in
    def, env
  in
  let infer_smodule_consts env tenv def =
    let cs, all, env =
      List.fold_left
        (fun (cs, all, env) id ->
          let def = Idmap.find id cs in
          let def = infer_constdef env tenv def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (SMConst def) all in
          let env = add_env def.const_id (ModuleConst def.const_type) env in
          cs, all, env)
        (def.smodule_consts, def.smodule_all, env)
        def.smodule_consts_ord
    in
    let def = { def with smodule_consts = cs; smodule_all = all } in
    def, env
  in
  let infer_smodule_init env tenv def =
    let astinit, tinit = infer_expression env tenv 1 def.smodule_init in
    let tinit = unify (TState (file, def.smodule_id)) tinit in
    { def with smodule_init = astinit, tinit }
  in
  let infer_smodule_states env tenv def =
    let mid = def.smodule_id in
    let sts, all =
      Idmap.fold
        (fun id def (sts, all) ->
          let def = infer_state env tenv file mid def in
          let sts = Idmap.add id def sts in
          let all = Idmap.add id (SMState def) all in
          sts, all)
        def.smodule_states
        (def.smodule_states, def.smodule_all)
    in
    { def with smodule_states = sts; smodule_all = all }
  in
  let def, env = infer_smodule_params env tenv def in
  let def, env = infer_state_params env tenv def in
  let def, env = infer_smodule_header_nodes env tenv def in
  let def, env = infer_smodule_consts env tenv def in
  let def = infer_smodule_init env tenv def in
  let def = infer_smodule_states env tenv def in
  def
;;

let infer (other_progs : xfrp Idmap.t) (file : string) (prog : xfrp) : xfrp =
  let register_modevals file def env : env =
    (env, 0)
    |> Idmap.fold
         (fun modev acc (env, i) ->
           let entry = ModeValue (file, def.mode_id, i, acc) in
           add_env modev entry env, i + 1)
         def.mode_vals
    |> fst
  in
  let register_typeconses file def env : env =
    Idmap.fold
      (fun c tval env ->
        let tret = Type.TId (file, def.type_id) in
        let entry = ValueCons (file, tval, tret) in
        add_env c entry env)
      def.type_conses
      env
  in
  let register_const file def env : env =
    let entry = ConstId (file, def.const_type) in
    add_env def.const_id entry env
  in
  let register_fun file def env : env =
    let _, tparams = List.split def.fun_params in
    let entry = FunId (file, tparams, def.fun_rettype) in
    add_env def.fun_id entry env
  in
  let register_module file def env : env =
    let ptype = List.map (fun (_, t) -> t) def.module_params in
    let itype = List.map (fun (_, _, t) -> t) def.module_in in
    let otype = List.map (fun (_, _, t) -> t) def.module_out in
    let entry = ModuleCons (file, ptype, itype, otype) in
    add_env def.module_id entry env
  in
  let register_smodule file def env : env =
    let ptype = List.map (fun (_, t) -> t) def.smodule_params in
    let itype = List.map (fun (_, _, t) -> t) def.smodule_in in
    let otype = List.map (fun (_, _, t) -> t) def.smodule_out in
    let entry = ModuleCons (file, ptype, itype, otype) in
    add_env def.smodule_id entry env
  in
  let use_program file prog (env, tenv) =
    let env =
      env
      |> Idmap.fold
           (fun _ def env -> if def.mode_pub then register_modevals file def env else env)
           prog.xfrp_modes
      |> Idmap.fold
           (fun _ def env ->
             if def.type_pub then register_typeconses file def env else env)
           prog.xfrp_types
      |> Idmap.fold
           (fun _ def env -> if def.const_pub then register_const file def env else env)
           prog.xfrp_consts
      |> Idmap.fold
           (fun _ def env -> if def.fun_pub then register_fun file def env else env)
           prog.xfrp_funs
      |> Idmap.fold
           (fun _ def env -> if def.module_pub then register_module file def env else env)
           prog.xfrp_modules
      |> Idmap.fold
           (fun _ def env ->
             if def.smodule_pub then register_smodule file def env else env)
           prog.xfrp_smodules
    in
    let tenv =
      tenv
      |> Idmap.fold
           (fun _ def tenv ->
             if def.mode_pub then add_menv def.mode_id file tenv else tenv)
           prog.xfrp_modes
      |> Idmap.fold
           (fun _ def tenv ->
             if def.type_pub then add_tenv def.type_id file tenv else tenv)
           prog.xfrp_types
    in
    env, tenv
  in
  let make_env_tenv prog =
    List.fold_right
      (fun file env_tenv ->
        let data = Idmap.find file other_progs in
        use_program file data env_tenv)
      prog.xfrp_use
      (Idmap.empty, { ts = Idmap.empty; ms = Idmap.empty })
  in
  let add_file_modes env tenv prog =
    let all, env, tenv =
      Idmap.fold
        (fun id def (all, env, tenv) ->
          let all = Idmap.add id (XFRPMode def) all in
          let env = register_modevals file def env in
          let tenv = add_menv def.mode_id file tenv in
          all, env, tenv)
        prog.xfrp_modes
        (prog.xfrp_all, env, tenv)
    in
    let prog = { prog with xfrp_all = all } in
    prog, env, tenv
  in
  let infer_file_types env tenv prog =
    let type_ord = Dependency.tsort_types prog.xfrp_types in
    let ts, all, env, tenv =
      List.fold_left
        (fun (ts, all, env, tenv) id ->
          let def = Idmap.find id ts in
          let def = infer_typedef env tenv def in
          let ts = Idmap.add id def ts in
          let all = Idmap.add id (XFRPType def) all in
          let env = register_typeconses file def env in
          let tenv = add_tenv def.type_id file tenv in
          ts, all, env, tenv)
        (prog.xfrp_types, prog.xfrp_all, env, tenv)
        type_ord
    in
    let prog = { prog with xfrp_types = ts; xfrp_all = all } in
    prog, env, tenv
  in
  let infer_file_materials env tenv prog =
    let material_ord = Dependency.tsort_materials prog.xfrp_consts prog.xfrp_funs in
    let cs, fs, all, env =
      List.fold_left
        (fun (cs, fs, all, env) id ->
          match Idmap.find id all with
          | XFRPConst def ->
            let def = infer_constdef env tenv def in
            let cs = Idmap.add id def cs in
            let all = Idmap.add id (XFRPConst def) all in
            let env = register_const file def env in
            cs, fs, all, env
          | XFRPFun def ->
            let def = infer_fundef env tenv def in
            let fs = Idmap.add id def fs in
            let all = Idmap.add id (XFRPFun def) all in
            let env = register_fun file def env in
            cs, fs, all, env
          | _ -> assert false)
        (prog.xfrp_consts, prog.xfrp_funs, prog.xfrp_all, env)
        material_ord
    in
    let prog = { prog with xfrp_consts = cs; xfrp_funs = fs; xfrp_all = all } in
    prog, env
  in
  let infer_file_modules env tenv prog =
    let module_ord = Dependency.tsort_modules prog.xfrp_modules prog.xfrp_smodules in
    let ms, sms, all, env =
      List.fold_left
        (fun (ms, sms, all, env) id ->
          match Idmap.find id all with
          | XFRPModule def ->
            let def = infer_module env tenv def in
            let ms = Idmap.add id def ms in
            let all = Idmap.add id (XFRPModule def) all in
            let env = register_module file def env in
            ms, sms, all, env
          | XFRPSModule def ->
            let def = infer_smodule env tenv file def in
            let sms = Idmap.add id def sms in
            let all = Idmap.add id (XFRPSModule def) all in
            let env = register_smodule file def env in
            ms, sms, all, env
          | _ -> assert false)
        (prog.xfrp_modules, prog.xfrp_smodules, prog.xfrp_all, env)
        module_ord
    in
    let prog = { prog with xfrp_modules = ms; xfrp_smodules = sms; xfrp_all = all } in
    prog, env
  in
  let env, tenv = make_env_tenv prog in
  let prog, env, tenv = add_file_modes env tenv prog in
  let prog, env, tenv = infer_file_types env tenv prog in
  let prog, env = infer_file_materials env tenv prog in
  let prog, _ = infer_file_modules env tenv prog in
  prog
;;
