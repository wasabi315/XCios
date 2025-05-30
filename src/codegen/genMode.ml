open Extension.Format
open Syntax
open MetaInfo
open CodegenUtil

let gen_mode ppf (file, mode) =
  let gen_mode_head ppf () = fprintf ppf "enum %a" gen_mode_name (file, mode.mode_id) in
  let gen_mode_body ppf () =
    (match mode.mode_val_ord with
     | None -> Idmap.to_seq mode.mode_vals |> Seq.map fst |> List.of_seq
     | Some modev_ord -> modev_ord)
    |> List.map (fun modev -> (file, mode.mode_id), modev)
    |> fprintf ppf "%a" (pp_list_comma gen_modev_name)
  in
  fprintf ppf "%a;" (gen_codeblock gen_mode_head gen_mode_body) ()
;;

let gen_max ppf = fprintf ppf "#define MAX(a, b) ((a) > (b) ? (a) : (b))@,@,"

let generate ppf metainfo =
  gen_max ppf;
  pp_list_break2 gen_mode ppf metainfo.typedata.modes
;;
