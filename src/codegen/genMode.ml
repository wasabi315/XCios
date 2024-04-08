open Extension.Format
open Syntax
open MetaInfo
open CodegenUtil

let gen_mode ppf (file, mode) =
  let gen_mode_head ppf () =
    fprintf ppf "enum class %a" gen_mode_name (file, mode.mode_id)
  in
  let gen_mode_body ppf () =
    fprintf ppf "%a" (pp_list_comma pp_identifier) (mode.mode_vals @ mode.mode_acc_vals)
  in
  fprintf ppf "%a;" (gen_codeblock gen_mode_head gen_mode_body) ()
;;

let gen_with_mode ppf =
  fprintf ppf "template <typename M, typename T>@,";
  fprintf ppf "@[<v 2>struct WithMode {@,";
  fprintf ppf "M mode[2];@,";
  fprintf ppf "T value;";
  fprintf ppf "@]@,};@,@,"
;;

let generate ppf metainfo =
  gen_with_mode ppf;
  pp_list_break2 gen_mode ppf metainfo.typedata.modes
;;
