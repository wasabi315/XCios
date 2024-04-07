open Extension.Format
open Syntax
open MetaInfo
open CodegenUtil

(*
   let gen_mode ppf (file, mode) =
  let gen_mode_head ppf () =
    fprintf ppf "enum class %a" gen_mode_name (file, mode.mode_id)
  in
  let gen_mode_body ppf () =
    fprintf ppf "%a" (pp_list_comma pp_identifier) (mode.mode_vals @ mode.mode_acc_vals)
  in
  fprintf ppf "%a;" (gen_codeblock gen_mode_head gen_mode_body) ()
;; *)

let generate _ppf _metainfo = ()
