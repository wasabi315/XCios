open MetaInfo
open Extension.Format

let generate_main metainfo =
  let entry_file = metainfo.entry_file in
  let out =
    open_out (entry_file ^ ".cpp") |> formatter_of_out_channel
  in
  fprintf out "@[<v>";
  fprintf out "%a" GenDataType.generate metainfo;
  fprintf out "@,@,%a" GenMemory.generate metainfo;
  fprintf out "@,@,%a" GenGlobal.generate metainfo;
  fprintf out "@,@,%a" GenFun.generate metainfo;
  fprintf out "@]@."

let codegen metainfo =
  printf "%a@." pp_metainfo metainfo;
  generate_main metainfo
