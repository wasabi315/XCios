open Syntax
open Type

type env_entry =
  | ConstId of Type.t
  | NodeId of Type.t
  | NewnodeId of identifier * int * Type.t
  | ValueCons of Type.t * Type.t
  | ModuleCons of Type.t list * Type.t list * Type.t list

type env = env_entry Idmap.t

exception NameConflict of identifier

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_env (id : identifier) (entry : env_entry) (env : env) : env =
  match Idmap.find_opt id env with
  | Some(_) -> raise (NameConflict id)
  | None -> Idmap.add id entry env

let add_env_const (id : identifier) (t : Type.t) (env : env) : env =
  let entry = ConstId(t) in
  add_env id entry env

let add_env_node (id : identifier) (t : Type.t) (env : env) : env =
  let entry = NodeId(t) in
  add_env id entry env

let add_env_newnode (nid : identifier) (mid : identifier) (pos : int) (t : Type.t)
      (env : env) : env =
  let entry = NewnodeId(mid, pos, t) in
  add_env nid entry env

let add_env_valuecons (id : identifier) (targ : Type.t) (tret : Type.t)
      (env : env) : env =
  let entry = ValueCons(targ, tret) in
  add_env id entry env

let add_env_modulecons (id : identifier) (tparam : Type.t list) (tin : Type.t list)
      (tout : Type.t list) (env : env) : env =
  let entry = ModuleCons(tparam, tin, tout) in
  add_env id entry env
          
(*----- Register definition to environment -----*)
let register_type def env : env =
  Idmap.fold (fun c v env ->
      add_env_valuecons c v (TId def.type_id) env
    ) def.type_conses env

let register_const def env : env =
  add_env_const def.const_id def.const_type env

let register_fun def env : env =
  add_env_const def.fun_id def.fun_type env

let register_nodedecl (id, _, t) env : env =
  add_env_node id t env

let register_node def env : env =
  add_env_node def.node_id def.node_type env

let register_newnode def env : env =
  let binds_with_index =
    List.mapi (fun i (_, id, t) -> (i, id, t)) def.newnode_binds
  in
  List.fold_left (fun env (i, id, t) ->
      add_env_newnode id def.newnode_id i t env 
    ) env binds_with_index
  
let register_module def env : env =
  let ptype = List.map (fun (_, t) -> t) def.module_params in
  let itype = List.map (fun (_, _, t) -> t) def.module_in in
  let otype = List.map (fun (_, _, t) -> t) def.module_out in
  add_env_modulecons def.module_id ptype itype otype env

let register_smodule def env : env =
  let ptype = List.map (fun (_, t) -> t) def.smodule_params in
  let itype = List.map (fun (_, _, t) -> t) def.smodule_in in
  let otype = List.map (fun (_, _, t) -> t) def.smodule_out in
  add_env_modulecons def.smodule_id ptype itype otype env

let use_program prog env : env =
  env
  |> Idmap.fold (fun _ def env ->
         if def.type_pub then register_type def env else env
       ) prog.xfrp_types
  |> Idmap.fold (fun _ def env ->
         if def.const_pub then register_const def env else env
       ) prog.xfrp_consts
  |> Idmap.fold (fun _ def env ->
         if def.fun_pub then register_fun def env else env
       ) prog.xfrp_funs
  |> Idmap.fold (fun _ def env ->
         if def.module_pub then register_module def env else env
       ) prog.xfrp_modules
  |> Idmap.fold (fun _ def env ->
         if def.smodule_pub then register_smodule def env else env
       ) prog.xfrp_smodules
