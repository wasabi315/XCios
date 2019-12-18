open Syntax
open Extension.Format
open Gather
open Lifetime
   
type metainfo =
  {
    used_materials : Idset.t;
    lifetime : lifetime;
  }
let pp_metainfo ppf metainfo =
  fprintf ppf "@[<v 2>metainfo:@;";
  fprintf ppf "@[<hv>used_materials: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;<0 0>" pp_idset metainfo.used_materials;
  fprintf ppf "}@]@;";
  fprintf ppf "@[<v>lifetime: {@;<0 2>";
  fprintf ppf "%a@;" pp_lifetime metainfo.lifetime;
  fprintf ppf "}@]@]"

exception NoMain
let get_metainfo entry_file all_data =
  let filedata = Idmap.find entry_file all_data in
  match Idmap.find_opt "Main" filedata.xfrp_all with
  | Some (XFRPModule def) ->
     let used_materials = gather_def_module all_data entry_file def in
     let lifetime = get_module_lifetime all_data def in
     {
       used_materials = used_materials;
       lifetime = lifetime;
     }
  | Some (XFRPSModule def) ->
     let used_materials = gather_def_smodule all_data entry_file def in
     let lifetime = get_smodule_lifetime all_data def in
     {
       used_materials = used_materials;
       lifetime = lifetime;
     }
  | _ -> raise NoMain
