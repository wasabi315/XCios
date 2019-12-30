open Extension.Format
open CodegenUtil

let generate ppf metainfo =
  let fun_writers =
    [] |> GenTypeFun.define_type_funs metainfo
  in
  let (prototype_writers, definition_writers) = List.split fun_writers in
  let prototype_writers = List.rev prototype_writers in
  let definition_writers = List.rev definition_writers in
  fprintf ppf "@[<v>%a@]"
    (exec_all_writers ()) (prototype_writers @ definition_writers)
