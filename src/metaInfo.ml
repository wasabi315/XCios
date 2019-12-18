open Syntax
open Extension.Format

type metainfo =
  {
    used_materials : Idset.t;
  }
let pp_metainfo ppf metainfo =
  fprintf ppf "@[<v>metainfo: {@;<0 2>";
  fprintf ppf "@[<hv>used_materials: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;<0 0>" pp_idset metainfo.used_materials;
  fprintf ppf "}@]@;";
  fprintf ppf "}@]"

exception NoMain
let get_metainfo entry_file all_data =
  let filedata = Idmap.find entry_file all_data in
  match Idmap.find_opt "Main" filedata.xfrp_all with
  | Some (XFRPModule def) ->
     let used_materials =
       Gather.gather_def_module all_data entry_file def
     in
     { used_materials = used_materials }
  | Some (XFRPSModule def) ->
     let used_materials =
       Gather.gather_def_smodule all_data entry_file def
     in
     { used_materials = used_materials }
  | _ -> raise NoMain
