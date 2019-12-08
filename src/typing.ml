(* Type inference *)
open Syntax
open Type
open Env
open Extension.Format

exception UnifyError of t * t
exception TypeError of string

(* Raise type error with given message `msg`. *)
let raise_err msg =
  raise (TypeError msg)

(* Raise type error with message printed by `f_pp`. *)
let raise_err_pp (f_pp : formatter -> unit) =
  let msg = f_pp str_formatter; flush_str_formatter () in
  raise (TypeError msg)

(* Raise type imcompatible error with `t1` and `t2`. *)
let raise_imcompatible t1 t2 =
  raise_err_pp (fun ppf ->
      fprintf ppf "%a and %a is not compatible" pp_t t1 pp_t t2
    )

(* Adjusting level of unification target pointed by another free variable
   with `id` and `level`. *)
let rec adjust_level id level = function
  | TVar({contents} as r) ->
     begin
       match contents with
       | TVGeneric(_) -> assert false
       | TVBound(t) -> adjust_level id level t
       | TVFree(id', level') ->
          if id = id' then raise_err "recursive type"
          else r := TVFree(id', (min level level'))
     end
  | TFun(args, ret) ->
     List.iter (adjust_level id level) args;
     adjust_level id level ret
  | TTuple(ts) -> List.iter (adjust_level id level) ts
  | _ -> ()

(* Unify type `t1` and `t2`. *)
let rec unify t1 t2 =
  match t1,t2 with
  | TBool, TBool | TInt, TInt | TFloat, TFloat | TUnit, TUnit | TState, TState
    -> t1
  | TId(x), TId(y) -> if x = y then t1 else raise_imcompatible t1 t2
  | TTuple(xs), TTuple(ys) ->
     let ts = unify_list xs ys in
     TTuple(ts)
  | TFun(params1, t1), TFun(params2, t2) ->
     let params = unify_list params1 params2 in
     let ret = unify t1 t2 in
     TFun(params, ret)
  | TVar({contents = TVBound(t1)} as r), t2
    | t1, TVar({contents = TVBound(t2)} as r) ->
     let t = unify t1 t2 in
     r := TVBound(t); t
  | TVar({contents = TVFree(id, level)} as r), t
    | t, TVar({contents = TVFree(id, level)} as r) ->
     adjust_level id level t; r := TVBound(t); t
  | _, _ -> raise_imcompatible t1 t2

(* Unify type list `ts1` and `ts2`. *)
and unify_list ts1 ts2 =
  let len1 = List.length ts1 in
  let len2 = List.length ts2 in
  if len1 != len2 then
    raise (UnifyError (TTuple(ts1), TTuple(ts2)))
  else List.map2 unify ts1 ts2

(* Generalize free variables. *)
let rec generalize level = function
  | TTuple(ts) -> List.iter (generalize level) ts
  | TFun(params, t) ->
     List.iter (generalize level) params; generalize level t
  | TVar({contents = TVFree(id,level')} as r) ->
     if level' > level then r := TVGeneric(id) else ()
  | TVar({contents = TVBound(t)}) -> generalize level t
  | _ -> ()

(* Instantiate generic variables. *)
let instantiate level t =
    let general_to_free = Hashtbl.create 10 in
    let rec visit = function
      | TTuple(ts) -> TTuple(List.map visit ts)
      | TFun(params, t) ->
         let inst_params = List.map visit params in
         let inst_return = visit t in
         TFun(inst_params, inst_return)
      | TVar({contents = TVGeneric(id)}) ->
         begin
           match Hashtbl.find_opt general_to_free id with
           | Some(var) -> var
           | None ->
              let newvar = gen_tvar_free level in
              Hashtbl.add general_to_free id newvar;
              newvar
         end
      | TVar({contents = TVBound(t')}) -> visit t'
      | _ as t -> t
    in
    visit t

(* Replace TEmpty with a fresh free variable. *)
let rec replace_tempty level = function
  | TEmpty -> gen_tvar_free level
  | TTuple(ts) ->
     let ts' = List.map (replace_tempty level) ts in
     TTuple(ts')
  | TFun(tparams, tret) ->
     let tparams' = List.map (replace_tempty level) tparams in
     let tret' = replace_tempty level tret in
     TFun(tparams', tret')
  | TVar({contents = TVBound(t)}) -> replace_tempty level t
  | _ as t -> t

(* Return if given type is not polymorphic type. *)
let rec is_concrete = function
  | TBool | TInt | TFloat | TUnit | TId(_) | TState
    -> true
  | TTuple(ts) -> List.for_all is_concrete ts
  | TFun(args,t) -> (List.for_all is_concrete args) && (is_concrete t)
  | TVar({contents = TVBound(t)}) -> is_concrete t
  | TVar(_) -> false
  | TEmpty -> assert false

let rec flatten_type = function
  | TTuple(ts) ->
     let ts = List.map flatten_type ts in
     TTuple(ts)
  | TFun(targs, tret) ->
     let targs = List.map flatten_type targs in
     let tret = flatten_type tret in
     TFun(targs, tret)
  | TVar({contents = TVBound(t)}) -> flatten_type t
  | t -> t
            
let rec deref_pattern_type (ast, t) =
  let t = flatten_type t in
  match ast with
  | PWild | PId(_)| PConst(_) ->
     (ast, t)
  | PTuple(ps) ->
     let ps = List.map deref_pattern_type ps in
     (PTuple(ps), t)
  | PVariant(c, p) ->
     let p = deref_pattern_type p in
     (PVariant(c, p), t)
            
let rec deref_expr_type (ast, t) =
  begin
    let t = flatten_type t in
    match ast with
    | EUniOp(op, e) ->
       let e = deref_expr_type e in
       (EUniOp(op, e), t)
       
    | EBinOp(op, e1, e2) ->
       let e1 = deref_expr_type e1 in
       let e2 = deref_expr_type e2 in
       (EBinOp(op, e1, e2), t)
    | EVariant(c, e) ->
       let e = deref_expr_type e in
       (EVariant(c, e), t)
    | ETuple(es) ->
       let es = List.map deref_expr_type es in
       (ETuple(es), t)
    | EConst(_) | ERetain | EId(_) | EAnnot(_, _) | EDot(_, _) ->
       (ast, t)
    | EFuncall(f, args) ->
       let args = List.map deref_expr_type args in
       (EFuncall(f, args), t)
    | EIf(etest, ethen, eelse) ->
       let etest = deref_expr_type etest in
       let ethen = deref_expr_type ethen in
       let eelse = deref_expr_type eelse in
       (EIf(etest, ethen, eelse), t)
    | ELet(bs, body) ->
       let bs = List.map deref_binder_type bs in
       let body = deref_expr_type body in
       (ELet(bs, body), t)
    | ECase(e, bs) ->
       let e = deref_expr_type e in
       let bs = List.map deref_branch_type bs in
       (ECase(e, bs), t)
  end
and deref_binder_type { binder_id; binder_body } =
  let (id, t) = binder_id in
  let t = flatten_type t in
  let body = deref_expr_type binder_body in
  { binder_id = (id, t); binder_body = body }
and deref_branch_type { branch_pat; branch_body } =
  let pat = deref_pattern_type branch_pat in
  let body = deref_expr_type branch_body in
  { branch_pat = pat; branch_body = body }
            
(*----- inference functions -----*)
let infer_identifier env level id =
  try
    match Idmap.find id env with
    | ConstId(t) -> ConstId(instantiate level t)
    | NodeId(t) -> NodeId(instantiate level t)
    | SubmoduleId(ts) ->  SubmoduleId(List.map (instantiate level) ts)
    | ValueCons(tc, tv) ->
       let tc = instantiate level tc in
       let tv = instantiate level tv in
       ValueCons(tc, tv)
    | ModuleCons(pts, its, ots) ->
       let pts = List.map (instantiate level) pts in
       let its = List.map (instantiate level) its in
       let ots = List.map (instantiate level) ots in
       ModuleCons(pts, its, ots)
  with
  | Not_found ->
     raise_err_pp (fun ppf ->
         fprintf ppf "Unknown %a" pp_identifier id
       )

let infer_literal _env _level ast =
  match ast with
  | LTrue | LFalse -> TBool
  | LInt(_) -> TInt
  | LFloat(_) -> TFloat
  | LUnit -> TUnit

let rec infer_pattern env level (ast, _) =
  (* return result + id-type bind *)
  match ast with
  | PWild ->
     let var = gen_tvar_free level in
     let res = (ast, var) in
     (res, [])
  | PId(id) ->
     let var = gen_tvar_free level in
     let res = (ast, var) in
     (res, [(id, var)])
  | PConst(l) ->
     let tl = infer_literal env level l in
     let res = (PConst(l), tl) in
     (res, [])
  | PTuple(ps) ->
     let (ps', binds) = List.map (infer_pattern env level) ps |> List.split in
     let (_, tps) = List.split ps' in
     let res = (PTuple(ps'), TTuple(tps)) in
     (res, List.concat binds)
  | PVariant(c, p) ->
     let ((_, tp) as p', binds) = infer_pattern env level p in
     begin
       match (infer_identifier env level c) with
       | ValueCons(tp2, tret) ->
          let _ = unify tp tp2 in
          let res = (PVariant(c, p'), tret) in
          (res, binds)
       | ModuleCons(_, _, _) ->
          raise_err_pp (fun ppf ->
              fprintf ppf "expected constructor : %a" pp_identifier c
            )
       | _ -> assert false
     end

let rec infer_expression env level (ast, _) =

  let infer_uniop op e1 =
    let (_, te1) as e1' = infer_expression env level e1 in
    let ast' = EUniOp(op, e1') in
    match op with
    | UInv | UPlus | UMinus | UFPlus | UFMinus ->
       let _ = unify TInt te1 in
       (ast', TInt)
    | UNot ->
       let _ = unify TBool te1 in
       (ast', TBool)
  in

  let infer_binop op e1 e2 =
    let (_, te1) as e1' = infer_expression env level e1 in
    let (_, te2) as e2' = infer_expression env level e2 in
    let ast' = EBinOp(op, e1', e2') in
    match op with
    | BMul |BDiv | BAdd | BSub
      | BMod | BShl | BShr
      | BAnd | BOr | BXor
      | BLt | BLeq | BGt | BGeq
      -> let _ = unify TInt te1 in
         let _ = unify TInt te2 in
         (ast', TInt)
    | BFMul |BFDiv | BFAdd | BFSub
      | BFLt | BFLeq | BFGt | BFGeq
      -> let _ = unify TFloat te1 in
         let _ = unify TFloat te2 in
         (ast', TFloat)
    | BLand | BLor
      -> let _ = unify TBool te1 in
         let _ = unify TBool te2 in
         (ast', TBool)
    | BEq | BNeq
      -> let tvar = gen_tvar_free level in
         let _ = unify tvar te1 in
         let _ = unify tvar te2 in
         (ast', TBool)
  in

  let infer_retain () =
    match (infer_identifier env level "Retain") with
    | NodeId(t) -> (ast, t)
    | _ -> assert false (* fail in register "Retain" *)
  in

  let infer_idref id =
    match (infer_identifier env level id) with
    | ConstId(t) | NodeId(t) -> (ast, t)
    | SubmoduleId(_) ->
       raise_err_pp (fun ppf ->
           fprintf ppf "submodule cannot refer directly : %a" pp_identifier id
         )
    | _ -> assert false
  in

  let infer_annot id _annot =
    match (infer_identifier env level id) with
    | NodeId(t) -> (ast, t)
    | ConstId(_) | SubmoduleId(_) ->
       raise_err_pp (fun ppf ->
           fprintf ppf "expected node : %a" pp_identifier id
         )
    | _ -> assert false
  in

  let infer_variant c v =
    let (_, tv) as v' = infer_expression env level v in
    let ast' = EVariant(c, v') in
    match (infer_identifier env level c) with
    | ValueCons(tv2, tret) ->
       let _ = unify tv tv2 in
       (ast', tret)
    | ModuleCons(_, _, _) ->
       raise_err_pp (fun ppf ->
           fprintf ppf "expected constructor : %a" pp_identifier c
         )
    | _ -> assert false
  in

  let infer_tuple es =
    let es' = List.map (infer_expression env level) es in
    let (_, tes) = List.split es' in
    let ast' = ETuple(es') in
    (ast', TTuple(tes))
  in

  let infer_funcall f args =
    let args' = List.map (infer_expression env level) args in
    let (_, targs) = List.split args' in
    let ast' = EFuncall(f, args') in
    match (infer_identifier env level f) with
    | ConstId(TFun(targs2, tret)) ->
       let _ = unify_list targs targs2 in
       (ast', tret)
    | NodeId(_) | SubmoduleId(_) ->
       raise_err_pp (fun ppf ->
           fprintf ppf "expected a function : %a" pp_identifier f
         )
    | _ -> assert false
  in

  let infer_let binds body =
    let infer_binder (acc, nowenv) {binder_id = (id, tid); binder_body = body} =
      let tid = replace_tempty level tid in
      let (_, tbody) as body' = infer_expression nowenv (level+1) body in
      let () = generalize level tbody in
      let _ = unify tid tbody in
      let newenv = add_env_const id tbody nowenv in
      let res = { binder_id = (id, tbody); binder_body = body'} in
      (res :: acc, newenv)
    in

    let (binds', newenv) = List.fold_left infer_binder ([], env) binds in
    let (_, tbody) as body' = infer_expression newenv level body in
    let ast' = ELet(List.rev binds', body') in
    (ast', tbody)
  in

  let infer_if etest ethen eelse =
    let (_, ttest) as etest' = infer_expression env level etest in
    let (_, tthen) as ethen' = infer_expression env level ethen in
    let (_, telse) as eelse' = infer_expression env level eelse in
    let ast' = EIf(etest', ethen', eelse') in
    let _ = unify ttest TBool in
    let _ = unify tthen telse in
    (ast', tthen)
  in

  let infer_case expr branchs =

    let infer_branch texpr {branch_pat; branch_body} =
      let ((_, tpat) as pat', newbinds) = infer_pattern env level branch_pat in
      let newenv =
        List.fold_right (fun (id, t) env-> add_env_const id t env) newbinds env
      in
      let (_, tbody) as body'= infer_expression newenv level branch_body in
      let res = { branch_pat = pat'; branch_body = body' } in
      let _ = unify texpr tpat in
      (res, tbody)
    in

    let (_, texpr) as expr' = infer_expression env (level+1) expr in
    let () = generalize level texpr in
    let (branchs', tbranchs) =
      List.map (infer_branch texpr) branchs |> List.split
    in
    let ast' = ECase(expr', branchs') in
    let tvar = gen_tvar_free level in
    let _ = List.map (unify tvar) tbranchs in
    (ast', tvar)
  in
  match ast with
  | EUniOp(op, e1) -> infer_uniop op e1
  | EBinOp(op, e1, e2) -> infer_binop op e1 e2
  | EVariant(c,v) -> infer_variant c v
  | ETuple(es) -> infer_tuple es
  | EConst(l) ->
     let tl = infer_literal env level l in
     (EConst(l), tl)
  | ERetain -> infer_retain ()
  | EId(id) -> infer_idref id
  | EAnnot(id, annot) -> infer_annot id annot
  | EFuncall(f, args) -> infer_funcall f args
  | EIf(etest, ethen, eelse) -> infer_if etest ethen eelse
  | ELet(binders, body) -> infer_let binders body
  | ECase(e, branchs) -> infer_case e branchs

let infer_constdef env def =
  let t = replace_tempty 1 def.const_type in
  let (_, tbody) as body =
    infer_expression env 1 def.const_body |> deref_expr_type
  in
  let t = unify t tbody in
  if not (is_concrete t) then
    raise_err_pp (fun ppf ->
        fprintf ppf "type of constant is not concrete : %a"
          pp_identifier def.const_id
      )
  else { def with const_body = body; const_type = t }

let infer_fundef env def =
  let t = replace_tempty 1 def.fun_type in
  let env =
    List.fold_right (fun (id, t) e->
        add_env_const id (replace_tempty 1 t) e
      ) def.fun_params env
  in
  let (_, tbody) as body =
    infer_expression env 1 def.fun_body |> deref_expr_type 
  in
  let params =
    List.map (fun (id, _) ->
        match Idmap.find id env with
        | ConstId(t) ->
           let t = flatten_type t in
           (id, t)
        | _ -> assert false
      ) def.fun_params
  in
  let (_, tparams) = List.split params in
  let t = unify (TFun(tparams, tbody)) t in
  let () = generalize 0 t in
  { def with fun_params = params; fun_type = t; fun_body = body }

let infer_node env def =
  let t = replace_tempty 1 def.node_type in
  let init =
    match def.node_init with
    | Some(expr) ->
       let (_, texpr) as expr =
         infer_expression env 1 expr |> deref_expr_type
       in
       let _ = unify t texpr in
       Some(expr)
    | None -> None
  in
  let (_, tbody) as body =
    infer_expression env 1 def.node_body |> deref_expr_type
  in
  let t = unify t tbody in
  if not (is_concrete t) then
    raise_err_pp (fun ppf ->
        fprintf ppf "type of node is not concrete : %a"
          pp_identifier def.node_id
      )
  else { def with node_init = init; node_body = body; node_type = t }

let infer_submodule env def =
  match (infer_identifier env 1 def.submodule_id) with
  | ValueCons(_, _) ->
     raise_err_pp (fun ppf ->
         fprintf ppf "expected constructor : %a"
           pp_identifier def.submodule_id
       )
  | ModuleCons(pts, its, ots) ->
     let margs =
       List.map (fun e ->
           infer_expression env 1 e |> deref_expr_type
         ) def.submodule_margs
     in
     let (_, tmargs) = List.split margs in
     let _ = unify_list pts tmargs in
     let inputs =
       List.map (fun e ->
           infer_expression env 1 e |> deref_expr_type
         ) def.submodule_inputs
     in
     let (_, tinputs) = List.split inputs in
     let _ = unify_list its tinputs in
     {
       def with submodule_type = ots;
                submodule_margs = margs;
                submodule_inputs = inputs;
     }
  | _ -> assert false
  
let infer_header_node env (id, init, t) =
  match init with
  | None -> (id, None, t)
  | Some(expr) ->
     let (_, texpr) as expr =
       infer_expression env 1 expr |> deref_expr_type
     in
     let _ = unify t texpr in
     (id, Some(expr), t)

let check_header_nodes
      (node_decls : (identifier * (expression option) * Type.t) list)
      (nodes : node Idmap.t) : unit =
  List.iter (fun (id, _, t) ->
      let node = Idmap.find id nodes in
      let t' = node.node_type in
      let _ = unify t t' in
      ()
    ) node_decls

let infer_module env def =

  let make_env def env =
    env
    |> List.fold_right
         (fun (id, t) env -> add_env_const id t env) def.module_params
    |> List.fold_right
         (fun (id, _, t) env -> add_env_node id t env) def.module_in
    |> List.fold_right
         (fun (id, _, t) env -> add_env_node id t env) def.module_out
  in    

  let infer_module_consts env def =
    let (cs, all, env) =
      List.fold_left (fun (cs, all, env) id ->
          let def = Idmap.find id cs in 
          let def = infer_constdef env def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (MConst def) all in
          let env = register_const def env in
          (cs, all, env)
        ) (def.module_consts, def.module_all, env) def.module_consts_ord
    in
    let def = {def with module_consts = cs; module_all = all } in
    (def, env)
  in

  let infer_module_nodes env def =
    let (ns, subms, all, env) =
      List.fold_left (fun (ns, subms, all, env) id ->
          match Idmap.find id all with
          | MNode(def) ->
             let def = infer_node env def in
             let ns = Idmap.add id def ns in
             let all = Idmap.add id (MNode def) all in
             let env = register_node def env in
             (ns, subms, all, env)
          | MSubmodule(def) ->
             let def = infer_submodule env def in
             let subms = Idmap.add id def subms in
             let all = Idmap.add id (MSubmodule def) all in
             let env = register_submodule def env in
             (ns, subms, all, env)
          | _ -> assert false
        ) (def.module_nodes, def.module_submodules, def.module_all, env)
        def.module_update_ord
    in
    let def =
      { def with module_nodes = ns; module_submodules = subms; module_all = all }
    in
    (def, env)
  in
  
  let env = make_env def env in
  let in_nodes = List.map (infer_header_node env) def.module_in in
  let out_nodes = List.map (infer_header_node env) def.module_out in
  let def =
    { def with module_in = in_nodes; module_out = out_nodes }
  in
  let (def, env) = infer_module_consts env def in
  let (def, _) = infer_module_nodes env def in
  let () = check_header_nodes def.module_out def.module_nodes in
  def
  
let infer_state env def =

  let make_env def env =
    List.fold_right (fun (id,t) env ->
        add_env_const id t env
      ) def.state_params env
  in
  
  let infer_state_consts env def =
    let (cs, all, env) =
      List.fold_left (fun (cs, all, env) id ->
          let def = Idmap.find id cs in 
          let def = infer_constdef env def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (SConst def) all in
          let env = register_const def env in
          (cs, all, env)
        ) (def.state_consts, def.state_all, env) def.state_consts_ord
    in
    let def = { def with state_consts = cs; state_all = all } in
    (def, env)
  in

  let infer_state_nodes env def =
    let (ns, subms, all, env) =
      List.fold_left (fun (ns, subms, all, env) id ->
          match Idmap.find id all with
          | SNode(def) ->
             let def = infer_node env def in
             let ns = Idmap.add id def ns in
             let all = Idmap.add id (SNode def) all in
             let env = register_node def env in
             (ns, subms, all, env)
          | SSubmodule(def) ->
             let def = infer_submodule env def in
             let subms = Idmap.add id def subms in
             let all = Idmap.add id (SSubmodule def) all in
             let env = register_submodule def env in
             (ns, subms, all, env)
          | _ -> assert false
        ) (def.state_nodes, def.state_submodules, def.state_all, env)
        def.state_update_ord
    in
    let def =
      { def with state_nodes = ns; state_submodules = subms; state_all = all }
    in
    (def, env)
  in

  let infer_state_switch env switch_expr : expression =
    let (astsw, tsw) =
      infer_expression env 1 switch_expr |> deref_expr_type
    in
    let _ = unify TState tsw in
    (astsw, TState)
  in

  let env = make_env def env in
  let (def, env) = infer_state_consts env def in
  let (def, env) = infer_state_nodes env def in
  let sw = infer_state_switch env def.state_switch in
  { def with state_switch = sw }

let infer_smodule env def =

  let make_env def env = 
    env
    |> List.fold_right
         (fun (id, t) env -> add_env_const id t env) def.smodule_params
    |> List.fold_right
         (fun (id, _, t) env -> add_env_node id t env) def.smodule_in
    |> List.fold_right
         (fun (id, _, t) env -> add_env_node id t env) def.smodule_out
    |> List.fold_right
         (fun (id, _, t) env -> add_env_node id t env) def.smodule_shared
  in

  let register_state_conses def env =
    Idmap.fold (fun _ state env ->
        let cons = state.state_id in
        let (_, tparams) = List.split state.state_params in
        let tvalue =
          match tparams with
          | [] -> TUnit
          | _ -> TTuple(tparams)
        in
        add_env_valuecons cons tvalue TState env
      ) def.smodule_states env
  in

  let infer_smodule_init env init_expr =
    let (astinit, tinit) =
      infer_expression env 1 init_expr |> deref_expr_type
    in
    let _ = unify TState tinit in
    (astinit, TState)
  in

  let infer_smodule_consts env def =
    let (cs, all, env) =
      List.fold_left (fun (cs, all, env) id ->
          let def = Idmap.find id cs in 
          let def = infer_constdef env def in
          let cs = Idmap.add id def cs in
          let all = Idmap.add id (SMConst def) all in
          let env = register_const def env in
          (cs, all, env)
        ) (def.smodule_consts, def.smodule_all, env) def.smodule_consts_ord
    in
    let def = { def with smodule_consts = cs; smodule_all = all } in
    (def, env)
  in

  let infer_smodule_states env def =
    let (sts, all) =
      Idmap.fold (fun id def (sts, all) ->
          let def = infer_state env def in
          let sts = Idmap.add id def sts in
          let all = Idmap.add id (SMState def) all in
          (sts, all)
        ) def.smodule_states (def.smodule_states, def.smodule_all)
    in
    { def with smodule_states = sts; smodule_all = all }
  in

  let check_state_header_nodes def =
    Idmap.iter (fun _ state ->
        check_header_nodes def.smodule_out state.state_nodes;
        check_header_nodes def.smodule_shared state.state_nodes;
      ) def.smodule_states
  in

  let env = make_env def env in
  let in_nodes = List.map (infer_header_node env) def.smodule_in in
  let out_nodes = List.map (infer_header_node env) def.smodule_out in
  let shared_nodes = List.map (infer_header_node env) def.smodule_shared in
  let init = infer_smodule_init env def.smodule_init in
  let def =
    {
      def with smodule_in = in_nodes;
               smodule_out = out_nodes;
               smodule_shared = shared_nodes;
               smodule_init = init;
    }
  in
  let env = register_state_conses def env in
  let (def, env) = infer_smodule_consts env def in
  let def = infer_smodule_states env def in
  let () = check_state_header_nodes def in
  def
  
let infer (other_progs : xfrp Idmap.t) (prog : xfrp) : xfrp =

  let make_env prog =
    List.fold_right (fun file env ->
        let data = Idmap.find file other_progs in
        use_program data env
      ) prog.xfrp_use Idmap.empty
  in
  
  let infer_file_materials env prog =
    let material_ord =
      Dependency.tsort_materials prog.xfrp_consts prog.xfrp_funs
    in
    let (cs, fs, all, env) = 
      List.fold_left (fun (cs, fs, all, env) id ->
          match Idmap.find id all with
          | XFRPConst(def) ->
             let def = infer_constdef env def in
             let cs = Idmap.add id def cs in
             let all = Idmap.add id (XFRPConst def) all in
             let env = register_const def env in
             (cs, fs, all, env)
          | XFRPFun(def) ->
             let def = infer_fundef env def in
             let fs = Idmap.add id def fs in
             let all = Idmap.add id (XFRPFun def) all in
             let env = register_fun def env in
             (cs, fs, all, env)
          | _ -> assert false
        ) (prog.xfrp_consts, prog.xfrp_funs, prog.xfrp_all, env) material_ord
    in
    let prog =
      { prog with xfrp_consts = cs; xfrp_funs = fs; xfrp_all = all }
    in
    (prog, env)
  in
  
  let infer_file_modules env prog =
    let module_ord =
      Dependency.tsort_modules prog.xfrp_modules prog.xfrp_smodules
    in
    let (ms, sms, all, env) =
      List.fold_left (fun (ms, sms, all, env) id ->
          match Idmap.find id all with
          | XFRPModule(def) ->
             let def = infer_module env def in
             let ms = Idmap.add id def ms in
             let all = Idmap.add id (XFRPModule def) all in
             let env = register_module def env in
             (ms, sms, all, env)
          | XFRPSModule(def) ->
             let def = infer_smodule env def in
             let sms = Idmap.add id def sms in
             let all = Idmap.add id (XFRPSModule def) all in
             let env = register_smodule def env in
             (ms, sms, all, env)
          | _ -> assert false
        ) (prog.xfrp_modules, prog.xfrp_smodules, prog.xfrp_all, env)
        module_ord
    in
    let prog =
      { prog with xfrp_modules = ms; xfrp_smodules = sms; xfrp_all = all }
    in
    (prog, env)
  in
  
  let env = make_env prog in
  let (prog, env) = infer_file_materials env prog in
  let (prog, _) = infer_file_modules env prog in
  prog
