open Syntax
open Type

type env_entry =
  | ConstId of Type.t
  | NodeId of Type.t
  | SubmoduleId of Type.t list
  | ValueCons of Type.t * Type.t
  | ModuleCons of Type.t list * Type.t list

type env = env_entry Idmap.t

exception NameConflict of identifier

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_env (id : identifier) (entry : env_entry) (env : env) : env =
  match Idmap.find_opt id env with
  | Some(_) -> raise (NameConflict id)
  | None -> Idmap.add id entry env


(*----- Register definition to environment -----*)
let register_type def env : env =
  Idmap.fold (fun c v env ->
      let entry = ValueCons(v, TId(def.type_id)) in 
      add_env c entry env
    ) def.type_conses env

let register_const def env : env =
  let entry = ConstId(def.const_type) in
  add_env def.const_id entry env

let register_fun def env : env =
  let entry = ConstId(def.fun_type) in
  add_env def.fun_id entry env

let register_nodedecl (id, _, t) env : env =
  let entry = NodeId(t) in
  add_env id entry env

let register_node def env : env =
  let entry = NodeId(def.node_type) in
  add_env def.node_id entry env

let register_module def env : env =
  let itype = List.map (fun (_, _, t) -> t) def.module_in in
  let otype = List.map (fun (_, _, t) -> t) def.module_out in
  let entry = ModuleCons(itype, otype) in
  add_env def.module_id entry env

let register_smodule def env : env =
  let itype = List.map (fun (_, _, t) -> t) def.smodule_in in
  let otype = List.map (fun (_, _, t) -> t) def.smodule_out in
  let entry = ModuleCons(itype, otype) in
  add_env def.smodule_id entry env
