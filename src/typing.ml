(* Type inference *)
open Syntax
open Type
open Data
open Extension.Format

exception UnifyError of t * t   
exception TypeError of string

(* raise type error with given message `msg` *)                     
let raise_err msg =
  raise (TypeError msg)
                     
(* raise type error with message printed by `f_pp` *)                     
let raise_err_pp (f_pp : formatter -> unit) =
  let msg = f_pp str_formatter; flush_str_formatter () in
  raise (TypeError msg)

(* raise type imcompatible error with `t1` and `t2` *)  
let raise_imcompatible t1 t2 =
  raise_err_pp (fun ppf ->
      fprintf ppf "%a and %a is not compatible" pp_t t1 pp_t t2
    )
  
(* adjusting level of unification target pointed by another free variable 
   with `id` and `level` *)   
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

(* unify type `t1` and `t2` *)       
let rec unify t1 t2 =
  if t1 == t2 then ()
  else
    match t1,t2 with
    | TBool, TBool | TInt, TInt | TFloat, TFloat | TUnit, TUnit | TState, TState
      -> ()
    | TId(x), TId(y) -> if x = y then () else raise_imcompatible t1 t2
    | TTuple(xs), TTuple(ys) -> unify_list xs ys
    | TFun(params1, t1), TFun(params2, t2)
      -> unify_list params1 params2; unify t1 t2
    | TVar({contents = TVBound(t1)}), t2
      | t1, TVar({contents = TVBound(t2)})
      -> unify t1 t2
    | TVar({contents = TVFree(id, level)} as r), t
      | t, TVar({contents = TVFree(id, level)} as r)
      -> adjust_level id level t;
         r := TVBound(t)
    | _, _ -> raise_imcompatible t1 t2

(* unify type list `ts1` and `ts2` *)
and unify_list ts1 ts2 =
  let len1 = List.length ts1 in
  let len2 = List.length ts2 in
  if len1 != len2 then
    raise (UnifyError (TTuple(ts1), TTuple(ts2)))
  else List.iter2 unify ts1 ts2

(* generalize free variables *)  
let rec generalize level = function
  | TTuple(ts) -> List.iter (generalize level) ts
  | TFun(params, t) ->
     List.iter (generalize level) params; generalize level t
  | TVar({contents = TVFree(id,level')} as r) ->
     if level' > level then r := TVGeneric(id) else ()
  | TVar({contents = TVBound(t)}) -> generalize level t
  | _ -> ()

(* instantiate generic variables *)            
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

(* replace TEmpty with a fresh free variable *)            
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
            
(* return if given type is not polymorphic type *)            
let rec is_concrete = function
  | TBool | TInt | TFloat | TUnit | TId(_) | TState
    -> true
  | TTuple(ts) -> List.for_all is_concrete ts
  | TFun(args,t) -> (List.for_all is_concrete args) && (is_concrete t)
  | TVar({contents = TVBound(t)}) -> is_concrete t
  | TVar(_) -> false
  | TEmpty -> assert false
            
(* inference functions*)
let infer_identifier env level id =
  match Idmap.find_opt id env with
  | Some(x) -> instantiate level x
  | None ->
     raise_err_pp (fun ppf ->
         fprintf ppf "Unbound id : %a" pp_identifier id
       )

let rec infer_literal env level (ast, _) =
  match ast with
  | LTrue | LFalse
    -> (ast, TBool)
  | LInt(_) -> (ast, TInt)
  | LFloat(_) -> (ast, TFloat)
  | LUnit -> (ast, TUnit)
  | LTuple ls ->
     let ls' = List.map (infer_literal env level) ls in
     let (_, tls) = List.split ls' in
     (LTuple(ls'), TTuple(tls))
  | LVariant(c,v) ->
     let tc = infer_identifier env level c in
       let (_, tv) as v' = infer_literal env level v in
       match tc with
       | TFun([tv2], tret) ->
          let () = unify tv tv2 in
          (LVariant(c, v'), tret)
       | _ -> assert false

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
     let (_, tl) as l' = infer_literal env level l in
     let res = (PConst(l'), tl) in 
     (res, [])
  | PTuple(ps) ->
     let (ps', binds) = List.map (infer_pattern env level) ps |> List.split in
     let (_, tps) = List.split ps' in
     let res = (PTuple(ps'), TTuple(tps)) in
     (res, List.concat binds)
  | PVariant(c, p) ->
     let tc = infer_identifier env level c in
     let ((_, tp) as p', binds) = infer_pattern env level p in
     begin
       match tc with
       | TFun([tp2], tret) ->
          let () = unify tp tp2 in
          let res = (PVariant(c, p'), tret) in
          (res, binds)
       | _ -> assert false
     end
        
let rec infer_expression env level (ast, _) =

  let infer_uniop op e1 =
    let (_, te1) as e1' = infer_expression env level e1 in
    let ast' = EUniOp(op, e1') in
    match op with
    | UInv
      -> unify TInt te1; (ast', TInt)
    | UNot
      -> unify TBool te1; (ast', TBool)
  in
  
  let infer_binop op e1 e2 = 
    let (_, te1) as e1' = infer_expression env level e1 in
    let (_, te2) as e2' = infer_expression env level e2 in
    let ast' = EBinOp(op, e1', e2') in
    match op with
    | BMul |BDiv | BAdd | BSub
    | BMod | BShl | BShr
    | BAnd | BOr | BXor
      -> unify TInt te1;unify TInt te2; (ast', TInt)
    | BFMul |BFDiv | BFAdd | BFSub
      -> unify TFloat te1;unify TFloat te2; (ast', TFloat)
    | BLand | BLor
      -> unify TBool te1;unify TBool te2; (ast', TBool)
    | BLt | BLeq | BGt | BGeq
    | BFLt | BFLeq | BFGt | BFGeq
    | BEq | BNeq
      -> let () = printf "%a %a" pp_t te1 pp_t te2; print_newline ()  in
         let tvar = gen_tvar_free level in
         unify tvar te1;unify tvar te2; (ast', TBool)
  in

  let infer_variant c v =
    let tc = infer_identifier env level c in
    let (_, tv) as v' = infer_expression env level v in
    let ast' = EVariant(c, v') in
    match tc with
    | TFun([tv2], tret) -> unify tv tv2; (ast', tret)
    | _ -> assert false
  in

  let infer_tuple es =
    let es' = List.map (infer_expression env level) es in
    let (_, tes) = List.split es' in
    let ast' = ETuple(es') in
    (ast', TTuple(tes))
  in
    
  let infer_funcall f args =
    let tf = infer_identifier env level f in
    let args' = List.map (infer_expression env level) args in
    let (_, targs) = List.split args' in
    let ast' = EFuncall(f, args') in
    match tf with
    | TFun(targs2, tret) -> unify_list targs targs2; (ast', tret)
    | _ -> raise_err_pp (fun ppf ->
               fprintf ppf "expected a function : %a" pp_identifier f
             )
  in
  
  let infer_let binds body =
    let infer_binder (acc, nowenv) {binder_id = (id, tid); binder_body = body} =
      let tid = replace_tempty level tid in
      let (_, tbody) as body' = infer_expression nowenv (level+1) body in
      let () = generalize level tbody in
      let () = unify tid tbody in
      let newenv = Idmap.add id tbody nowenv in
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
    unify ttest TBool; unify tthen telse; (ast', tthen)
  in
  
  let infer_case expr branchs =

    let infer_branch texpr {branch_pat; branch_body} =
      let ((_, tpat) as pat', newbinds) = infer_pattern env level branch_pat in
      let newenv =
        List.fold_right (fun (id, t) env-> Idmap.add id t env) newbinds env
      in
      let (_, tbody) as body'= infer_expression newenv level branch_body in
      let res = { branch_pat = pat'; branch_body = body' } in
      unify texpr tpat; (res, tbody)
    in

    let (_, texpr) as expr' = infer_expression env (level+1) expr in
    let () = generalize level texpr in
    let (branchs', tbranchs) =
      List.map (infer_branch texpr) branchs |> List.split
    in
    let ast' = ECase(expr', branchs') in
    let tvar = gen_tvar_free level in
    List.iter (unify tvar) tbranchs; (ast', tvar)
  in
  try
    match ast with
    | EUniOp(op, e1) -> infer_uniop op e1
    | EBinOp(op, e1, e2) -> infer_binop op e1 e2
    | EVariant(c,v) -> infer_variant c v
    | ETuple(es) -> infer_tuple es
    | EConst(l) ->
       let (_, tl) as l' = infer_literal env level l in
       (EConst(l'), tl)
    | ERetain ->
       let t = infer_identifier env level "Retain" in
       (ast, t)
    | EId(id) | EAnnot(id, _) ->
       let t = infer_identifier env level id in
       (ast, t)
    | EFuncall(f, args) -> infer_funcall f args
    | EIf(etest, ethen, eelse) -> infer_if etest ethen eelse
    | ELet(binders, body) -> infer_let binders body
    | ECase(e, branchs) -> infer_case e branchs
  with
  | TypeError(msg) ->
     printf "%a" pp_expression_ast ast;
     print_newline ();
     raise_err msg
                       
let infer_constdef env def =
  let (_, t) = def.const_id in
  let t = replace_tempty 1 t in
  let (_, tbody) as body' = infer_expression env 1 def.const_body in
  unify t tbody;
  if is_concrete t then
    { def with const_body = body' }
  else
    raise_err_pp (fun ppf ->
        fprintf ppf "type of constant is not concrete : %a"
          pp_identifier (get_id def.const_id)
      )
  
let infer_fundef env def =
  let (id, t) = def.fun_id in
  let t = replace_tempty 1 t in
  let newenv =
    List.fold_right (fun (id, t) e->
        Idmap.add id (replace_tempty 1 t) e
      ) def.fun_params env
  in
  let (_, tbody) as body' = infer_expression newenv 1 def.fun_body in
  let params' = 
    List.map (fun (id, _) ->
        let t = Idmap.find id newenv in (id, t)
      ) def.fun_params
  in
  let (_, tparams) = List.split params' in
  let () = unify (TFun(tparams, tbody)) t in
  let () = generalize 0 t in
  let () =
    printf "(%a) -> %a" (pp_list_comma pp_t) tparams pp_t tbody;
    print_newline ()
  in
  { fun_id = (id, t); fun_params = params'; fun_body = body' }

let infer_const_fun env cdefs fdefs =
  let update_with_id defid (nowenv, accc, accf) =
    if Idmap.mem defid cdefs then
      let newdef = infer_constdef nowenv (Idmap.find defid cdefs) in
      let newenv = Idmap.add defid (get_type newdef.const_id) nowenv in
      let newaccc = Idmap.add defid newdef accc in
      (newenv, newaccc, accf)
    else if Idmap.mem defid fdefs then
      let newdef = infer_fundef nowenv (Idmap.find defid fdefs) in
      let newenv = Idmap.add defid (get_type newdef.fun_id) nowenv in
      let newaccf = Idmap.add defid newdef accf in
      (newenv, accc, newaccf)
    else
      assert false
  in
  let id_order = Dependency.tsort_const_fun cdefs fdefs in
  List.fold_right update_with_id id_order (env, Idmap.empty, Idmap.empty)
  
let infer_state env sdef =
  let infer_node env def =
    let (id, _) = def.node_id in
    let t = Idmap.find id env in
    let env = Idmap.add "Retain" t env in
    let (_, tbody) as body' = infer_expression env 1 def.node_body in
    let () = unify t tbody in
    let init' =
      match def.init with
      | None -> None
      | Some(l) ->
         let (_, tl) as l' = infer_literal env 1 l in
         unify t tl; Some(l')
    in
    if is_concrete t then
      { init = init'; node_id = (id, t); node_body = body' }
    else
      raise_err_pp (fun ppf ->
          fprintf ppf "type of node is not concrete : %a"
            pp_identifier id
        )
  in

  let infer_switch env switch =
    let env' = Idmap.add "Retain" TState env in
    let (_, tswitch) as switch' = infer_expression env' 1 switch in
    unify TState tswitch; switch'
  in

  let add_node ndef env =
    let (id, t) = ndef.node_id in
    let t = replace_tempty 0 t in
    match Idmap.find_opt id env with
    | Some(t2) -> unify t t2; Idmap.add id t env (* case of output node *)
    | None -> Idmap.add id t env;
  in
  
  let env =
    List.fold_right (fun (id, t) e ->
        Idmap.add id t e 
      ) sdef.state_params env
    |> List.fold_right add_node sdef.nodes
  in
  let nodes' = List.map (infer_node env) sdef.nodes in
  let switch' = infer_switch env sdef.switch in
  { sdef with nodes = nodes'; switch = switch' }
  
let make_base_env data =
  let add_type_con tdef env =
    List.fold_right (fun (c, v) env ->
        let tc = TFun([v], TId(tdef.type_id)) in
        Idmap.add c tc env
      ) tdef.variant_defs env
  in
  let add_state_con sdef env =
    let (_, ts) = List.split sdef.state_params in
    let tv = 
      match ts with
      | [] -> TUnit
      | [x] -> x
      | _ -> TTuple(ts)
    in
    let tc = TFun([tv], TState) in
    Idmap.add sdef.state_id tc env
  in
  Idmap.empty
  |> Idmap.fold (fun _ def env -> add_type_con def env) data.tdefs
  |> Idmap.fold (fun _ def env -> add_state_con def env) data.sdefs  
  
let infer_progdata data =
  let infer_ionode env node =
    let (id, lopt, t) = node in
    match lopt with
    | None -> node
    | Some(l) ->
       let (_, tl) as l' = infer_literal env 0 l in
       unify t tl; (id, Some(l'), t)
  in
  let infer_init env (c,v) =
    let tc = infer_identifier env 0 c in
    let (_, tv) as v' = infer_literal env 0 v in
    match tc with
    | TFun([tv2], tret) -> unify tv tv2; unify TState tret; (c, v')
    | _ -> assert false;
  in

  let env = make_base_env data in
  let module_in' = Idmap.map (infer_ionode env) data.module_in in
  let module_out' = Idmap.map (infer_ionode env) data.module_out in
  let module_init' = infer_init env data.module_init in
  let env =
    Idmap.fold (fun _ (id, _, t) e ->
        Idmap.add id t e
      ) data.module_in env
    |> Idmap.fold (fun _ (id, _, t) e ->
           Idmap.add id t e
         ) data.module_out
  in
  let (env, cdefs', fdefs') = infer_const_fun env data.cdefs data.fdefs in
  let sdefs' = Idmap.map (infer_state env) data.sdefs in
  {
    data with
    module_in = module_in';
    module_out = module_out';
    module_init = module_init';
    cdefs = cdefs';
    fdefs = fdefs';
    sdefs = sdefs';
  }
