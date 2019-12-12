open Syntax

type env = idinfo Idmap.t

exception NameConflict of identifier

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_env (id : identifier) (entry : idinfo) (env : env) : env =
  match Idmap.find_opt id env with
  | Some(_) -> raise (NameConflict id)
  | None -> Idmap.add id entry env

(*----- Register definition to environment -----*)
let register_type file def env : env =
  Idmap.fold (fun c tval env ->
      let tret = Type.TId def.type_id in
      let entry = ValueCons (file, tval, tret) in
      add_env c entry env
    ) def.type_conses env

let register_const file def env : env =
  let entry = ConstId (file, def.const_type) in
  add_env def.const_id entry env

let register_fun file def env : env =
  let (_, tparams) = List.split def.fun_params in
  let entry = FunId (file, tparams, def.fun_rettype) in
  add_env def.fun_id entry env

let register_module file def env : env =
  let ptype = List.map (fun (_, t) -> t) def.module_params in
  let itype = List.map (fun (_, _, t) -> t) def.module_in in
  let otype = List.map (fun (_, _, t) -> t) def.module_out in
  let entry = ModuleCons (file, ptype, itype, otype) in
  add_env def.module_id entry env

let register_smodule file def env : env =
  let ptype = List.map (fun (_, t) -> t) def.smodule_params in
  let itype = List.map (fun (_, _, t) -> t) def.smodule_in in
  let otype = List.map (fun (_, _, t) -> t) def.smodule_out in
  let entry = ModuleCons (file, ptype, itype, otype) in
  add_env def.smodule_id entry env

let register_nodedecl (id, _, t) env : env =
  add_env id (NodeId t) env

let register_node def env : env =
  add_env def.node_id (NodeId def.node_type) env

let register_newnode def env : env =
  let binds_with_index =
    List.mapi (fun i (_, id, t) -> (i, id, t)) def.newnode_binds
  in
  List.fold_left (fun env (i, id, t) ->
      let entry = NewnodeId (def.newnode_id, i, t) in
      add_env id entry env
    ) env binds_with_index

let use_program filename prog env : env =
  env
  |> Idmap.fold (fun _ def env ->
         if def.type_pub then register_type filename def env else env
       ) prog.xfrp_types
  |> Idmap.fold (fun _ def env ->
         if def.const_pub then register_const filename def env else env
       ) prog.xfrp_consts
  |> Idmap.fold (fun _ def env ->
         if def.fun_pub then register_fun filename def env else env
       ) prog.xfrp_funs
  |> Idmap.fold (fun _ def env ->
         if def.module_pub then register_module filename def env else env
       ) prog.xfrp_modules
  |> Idmap.fold (fun _ def env ->
         if def.smodule_pub then register_smodule filename def env else env
       ) prog.xfrp_smodules
