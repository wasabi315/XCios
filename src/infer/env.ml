open Syntax

type env =
  { id_to_info : idinfo Idmap.t
  ; ty_id_to_file : string Idmap.t
  ; modety_id_to_file : string Idmap.t
  }

let empty_env : env =
  { id_to_info = Idmap.empty
  ; ty_id_to_file = Idmap.empty
  ; modety_id_to_file = Idmap.empty
  }
;;

exception NameConflict of identifier
exception NotFound of identifier

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_uniq (id : identifier) (value : 'a) (map : 'a Idmap.t) : 'a Idmap.t =
  match Idmap.find_opt id map with
  | Some _ -> raise (NameConflict id)
  | None -> Idmap.add id value map
;;

let add_info (id : identifier) (entry : idinfo) (env : env) : env =
  { env with id_to_info = add_uniq id entry env.id_to_info }
;;

let add_info_shadowing (id : identifier) (entry : idinfo) (env : env) : env =
  { env with id_to_info = Idmap.add id entry env.id_to_info }
;;

let add_ty (id : identifier) (file : string) (env : env) : env =
  { env with ty_id_to_file = add_uniq id file env.ty_id_to_file }
;;

let add_modety (id : identifier) (file : string) (env : env) : env =
  { env with modety_id_to_file = add_uniq id file env.modety_id_to_file }
;;

let find_info (id : identifier) (env : env) : idinfo option =
  Idmap.find_opt id env.id_to_info
;;

let find_ty (id : identifier) (env : env) : string option =
  Idmap.find_opt id env.ty_id_to_file
;;

let find_modety (id : identifier) (env : env) : string option =
  Idmap.find_opt id env.modety_id_to_file
;;
