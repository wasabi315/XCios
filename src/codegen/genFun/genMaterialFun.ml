open Extension.Format
open Syntax
open CodegenUtil
open GenExpr
open MetaInfo

let define_global_const_fun metainfo (file, constdef) fun_writers =
  let constname = asprintf "%a" gen_global_constname (file, constdef.const_id) in
  let gen_funname ppf () = fprintf ppf "static void init_%s" constname in
  let gen_prototype ppf () = fprintf ppf "%a();" gen_funname () in
  let gen_definition ppf () =
    let codegen_ctx = CTXGlobalConst in
    let body_writers, gen_expr =
      get_expr_generator metainfo codegen_ctx constdef.const_body
    in
    let gen_body_lastline ppf () =
      fprintf ppf "@[<hv 2>%a =@ @[%a@];@]" pp_print_string constname gen_expr ()
    in
    gen_codeblock
      (fun ppf () -> fprintf ppf "%a()" gen_funname ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf
      ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;

let define_global_fun metainfo (file, fundef) fun_writers =
  let gen_funname ppf () =
    fprintf
      ppf
      "static %a %a"
      (gen_value_type metainfo)
      fundef.fun_rettype
      gen_global_funname
      (file, fundef.fun_id)
  in
  let gen_prototype ppf () =
    let param_printer =
      pp_print_list (gen_value_type metainfo) ~pp_sep:pp_print_commaspace
    in
    let _, paramtypes = List.split fundef.fun_params in
    fprintf ppf "%a(@[<h>%a@]);" gen_funname () param_printer paramtypes
  in
  let gen_definition_params ppf () =
    (pp_print_list
       (fun ppf (id, t) ->
         fprintf ppf "@[<h>%a %a@]" (gen_value_type metainfo) t pp_print_string id)
       ~pp_sep:pp_print_commaspace)
      ppf
      fundef.fun_params
  in
  let gen_definition ppf () =
    let codegen_ctx = CTXGlobalConst in
    let body_writers, gen_expr =
      get_expr_generator metainfo codegen_ctx fundef.fun_body
    in
    let gen_body_lastline ppf () = fprintf ppf "@[<h>return @[%a@];@]" gen_expr () in
    gen_codeblock
      (fun ppf () -> fprintf ppf "%a(@[<h>%a@])" gen_funname () gen_definition_params ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf
      ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;

let define_material_fun metainfo fun_writers =
  let all_consts = metainfo.all_elements.all_consts in
  let all_funs = metainfo.all_elements.all_funs in
  fun_writers
  |> List.fold_right (define_global_const_fun metainfo) (List.rev all_consts)
  |> List.fold_right (define_global_fun metainfo) (List.rev all_funs)
;;
