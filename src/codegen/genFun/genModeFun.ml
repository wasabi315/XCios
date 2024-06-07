open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo

let define_is_accessible (file, { mode_id; mode_vals; _ }) =
  let gen_funname ppf () = fprintf ppf "%a_is_accessible" gen_mode_name (file, mode_id) in
  let gen_arg ppf () = fprintf ppf "enum %a modev" gen_mode_name (file, mode_id) in
  let gen_prototype ppf () = fprintf ppf "int %a(%a);" gen_funname () gen_arg () in
  let gen_definition ppf () =
    let gen_head ppf () = fprintf ppf "int %a(%a)" gen_funname () gen_arg () in
    let gen_body ppf () =
      let acc_modevs = Idmap.filter (fun _ acc -> acc = Acc) mode_vals in
      if Idmap.is_empty acc_modevs
      then fprintf ppf "return 0"
      else fprintf ppf "@[<hov 2>return@ ";
      Idmap.to_seq acc_modevs
      |> Seq.iteri (fun i (modev, _) ->
        if i > 0 then fprintf ppf " ||@ ";
        fprintf ppf "modev == %a" gen_modev_name ((file, mode_id), modev));
      fprintf ppf ";@]"
    in
    gen_codeblock gen_head gen_body ppf ()
  in
  gen_prototype, gen_definition
;;

let define_is_accessibles metainfo fun_writers =
  List.map define_is_accessible metainfo.typedata.modes @ fun_writers
;;
