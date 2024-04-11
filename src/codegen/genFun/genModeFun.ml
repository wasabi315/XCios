open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo

let define_is_accessible (file, { mode_id; mode_vals; mode_acc_vals; _ }) =
  let gen_funname ppf () = fprintf ppf "%a_is_accessible" gen_mode_name (file, mode_id) in
  let gen_arg ppf () = fprintf ppf "enum %a modev" gen_mode_name (file, mode_id) in
  let gen_prototype ppf () = fprintf ppf "bool %a(%a);" gen_funname () gen_arg () in
  let gen_definition ppf () =
    let gen_head ppf () = fprintf ppf "bool %a(%a)" gen_funname () gen_arg () in
    let gen_body ppf () =
      match mode_vals, mode_acc_vals with
      | [], _ -> fprintf ppf "return true;"
      | _, [] -> fprintf ppf "return false;"
      | _, modev :: _ ->
        fprintf
          ppf
          "return modev >= %a::%a;"
          gen_mode_name
          (file, mode_id)
          pp_identifier
          modev
    in
    gen_codeblock gen_head gen_body ppf ()
  in
  gen_prototype, gen_definition
;;

let define_is_accessibles metainfo fun_writers =
  List.map define_is_accessible metainfo.typedata.modes @ fun_writers
;;
