open Syntax

type env = idinfo Idmap.t
type tenv = string Idmap.t

exception NameConflict of identifier

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_uniq (id : identifier) (value : 'a) (map : 'a Idmap.t) : 'a Idmap.t =
  match Idmap.find_opt id map with
  | Some _ -> raise (NameConflict id)
  | None -> Idmap.add id value map
;;

let add_env (id : identifier) (entry : idinfo) (env : env) : env = add_uniq id entry env

let add_env_shadowing (id : identifier) (entry : idinfo) (env : env) : env =
  Idmap.add id entry env
;;

let add_tenv (id : identifier) (file : string) (tenv : tenv) : tenv =
  add_uniq id file tenv
;;
