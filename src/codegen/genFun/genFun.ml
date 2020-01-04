open Extension.Format
open CodegenUtil
open GenTypeFun
open GenMaterialFun
open GenModuleFun

let generate ppf metainfo =
  let fun_writers =
    []
    |> define_type_fun metainfo
    |> define_material_fun metainfo
    |> define_module_fun metainfo
  in
  let (prototype_writers, definition_writers) = List.split fun_writers in
  let prototype_writers = List.rev prototype_writers in
  let definition_writers = List.rev definition_writers in
  fprintf ppf "@[<v>%a@]"
    (exec_all_writers ()) (prototype_writers @ definition_writers)
