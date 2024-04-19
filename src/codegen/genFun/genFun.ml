open Extension.Format
open CodegenUtil
open GenTypeFun
open GenMaterialFun
open GenModuleFun
open GenGlobalFun
open GenModeFun

let generate ppf metainfo =
  let fun_writers =
    []
    |> define_is_accessibles metainfo
    |> define_type_fun metainfo
    |> define_material_fun metainfo
    |> define_module_fun metainfo
    |> define_refresh_mark_fun metainfo
  in
  let prototype_writers, definition_writers = List.split fun_writers in
  let prototype_writers = add_extern_prototype metainfo prototype_writers in
  let prototype_writers = List.rev prototype_writers in
  let definition_writers = List.rev definition_writers in
  fprintf ppf "@[<v>%a@]" (exec_all_writers ()) prototype_writers;
  fprintf
    ppf
    "@,@,@[<v>%a@]"
    (exec_all_writers () ~pp_sep:pp_print_cut2)
    definition_writers;
  fprintf ppf "@,@,%a" gen_activate_fun metainfo
;;

let generate_header ppf metainfo =
  let prototype_writers = [] |> define_type_fun_header metainfo in
  fprintf ppf "@[<v>%a@]" (exec_all_writers ()) prototype_writers
;;
