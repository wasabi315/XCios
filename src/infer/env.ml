open Syntax
open Errors

type usage =
  { num_read : int
  ; num_def : int
  ; num_pass : int
  }

let empty_usage : usage = { num_read = 0; num_def = 0; num_pass = 0 }

type env =
  { id_to_info : idinfo Idmap.t
  ; ty_id_to_file : string Idmap.t
  ; modety_id_to_file : string Idmap.t
  ; inaccs : identifier Idmap.t
  ; usages : (identifier, usage) Hashtbl.t
  }

let pp_usage ppf usage =
  Format.fprintf ppf "R=%d D=%d P=%d" usage.num_read usage.num_def usage.num_pass
;;

let pp_env ppf env =
  let open Format in
  let open Extension.Format in
  fprintf ppf "@[<v 2>env:";
  fprintf ppf "@,id_to_info: @[<hov>%a@]" (pp_idmap pp_idinfo) env.id_to_info;
  fprintf ppf "@,ty_id_to_file: @[<hov>%a@]" (pp_idmap pp_print_string) env.ty_id_to_file;
  fprintf
    ppf
    "@,modety_id_to_file: @[<hov>%a@]"
    (pp_idmap pp_print_string)
    env.modety_id_to_file;
  fprintf ppf "@,inaccs: @[<hov>%a@]" (pp_idmap pp_identifier) env.inaccs;
  fprintf
    ppf
    "@,usages: @[<hov>%a@]"
    (pp_print_hashtbl ~pp_sep:pp_print_commaspace (fun ppf (id, usage) ->
       fprintf ppf "%a -> %a" pp_identifier id pp_usage usage))
    env.usages;
  fprintf ppf "@]@,"
;;

let empty_env : env =
  { id_to_info = Idmap.empty
  ; ty_id_to_file = Idmap.empty
  ; modety_id_to_file = Idmap.empty
  ; inaccs = Idmap.empty
  ; usages = Hashtbl.create 16
  }
;;

(* Add new entry to environment.
   If `id` is already used, then raise NameConflict Exception *)
let add_uniq (id : identifier) (value : 'a) (map : 'a Idmap.t) : 'a Idmap.t =
  match Idmap.find_opt id map with
  | Some _ -> raise_name_conflict id
  | None -> Idmap.add id value map
;;

let add_info (id : identifier) (entry : idinfo) (env : env) : env =
  { env with id_to_info = add_uniq id entry env.id_to_info }
;;

let add_info_shadowing (id : identifier) (entry : idinfo) (env : env) : env =
  { env with
    id_to_info = Idmap.add id entry env.id_to_info
  ; inaccs = Idmap.remove id env.inaccs
  }
;;

let add_ty (id : identifier) (file : string) (env : env) : env =
  { env with ty_id_to_file = add_uniq id file env.ty_id_to_file }
;;

let add_modety (id : identifier) (file : string) (env : env) : env =
  { env with modety_id_to_file = add_uniq id file env.modety_id_to_file }
;;

let find_info (id : identifier) (env : env) : idinfo =
  match Idmap.find_opt id env.id_to_info with
  | Some info -> info
  | None -> raise_unknown id
;;

let find_ty (id : identifier) (env : env) : string =
  match Idmap.find_opt id env.ty_id_to_file with
  | Some file -> file
  | None -> raise_unknown id
;;

let find_modety (id : identifier) (env : env) : string =
  match Idmap.find_opt id env.modety_id_to_file with
  | Some file -> file
  | None -> raise_unknown id
;;

let add_inacc (id : identifier) (modev : identifier) (env : env) : env =
  { env with inaccs = Idmap.add id modev env.inaccs }
;;

let find_inacc (id : identifier) (env : env) : identifier option =
  Idmap.find_opt id env.inaccs
;;

let clear_usage (env : env) : unit = Hashtbl.clear env.usages

let get_usage (id : identifier) (env : env) : usage =
  Hashtbl.find_opt env.usages id |> Option.value ~default:empty_usage
;;

let incr_read (id : identifier) (env : env) =
  let usage =
    Hashtbl.find_opt env.usages id
    |> Option.value ~default:empty_usage
    |> fun usage -> { usage with num_read = usage.num_read + 1 }
  in
  Hashtbl.replace env.usages id usage
;;

let incr_def (id : identifier) (env : env) =
  let usage =
    Hashtbl.find_opt env.usages id
    |> Option.value ~default:empty_usage
    |> fun usage -> { usage with num_def = usage.num_def + 1 }
  in
  Hashtbl.replace env.usages id usage
;;

let incr_pass (id : identifier) (env : env) =
  let usage =
    Hashtbl.find_opt env.usages id
    |> Option.value ~default:empty_usage
    |> fun usage -> { usage with num_pass = usage.num_pass + 1 }
  in
  Hashtbl.replace env.usages id usage
;;
