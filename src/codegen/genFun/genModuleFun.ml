open Syntax
open GenModuleElemFun
open GenModuleUpdateFun
open GenModuleFreeFun
open MetaInfo

let define_module_fun metainfo fun_writers =
  let all_modules = metainfo.all_elements.all_modules in
  List.fold_left (fun fun_writers (file, module_or_smodule) ->
      match module_or_smodule with
      | XFRPModule m ->
         fun_writers
         |> define_module_elem_fun metainfo (file, m)
         |> define_module_update_fun metainfo (file, m)
         |> define_module_free_fun metainfo (file, m)
      | XFRPSModule sm ->
         fun_writers
         |> define_smodule_elem_fun metainfo (file, sm)
         |> define_smodule_update_fun metainfo (file, sm)
         |> define_smodule_free_fun metainfo (file, sm)
      | _ -> assert false
    ) fun_writers all_modules
