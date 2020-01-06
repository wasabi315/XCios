open MetaInfo
open Extension.Format
   
let generate_main metainfo =
  let entry_file = metainfo.entry_file in
  let ochan = open_out (entry_file ^ ".cpp") in
  let out = formatter_of_out_channel ochan in
  fprintf out "@[<v>";
  fprintf out "#include \"%s.h\"" entry_file;
  fprintf out "@,@,%a" GenDataType.generate metainfo;
  fprintf out "@,@,%a" GenMemory.generate metainfo;
  fprintf out "@,@,%a" GenGlobal.generate metainfo;
  fprintf out "@,@,%a" GenFun.generate metainfo;
  fprintf out "@]@.";
  close_out ochan

let generate_header metainfo =
  let entry_file = metainfo.entry_file in
  let ochan = open_out (entry_file ^ ".h") in
  let out = formatter_of_out_channel ochan in
  let include_guard =
    asprintf "%s_H" (String.uppercase_ascii entry_file)
  in
  fprintf out "@[<v>";
  fprintf out "#ifndef %s" include_guard;
  fprintf out "@,#define %s" include_guard;
  fprintf out "@,@,void activate();";
  fprintf out "@,@,#endif";
  fprintf out "@]@.";
  close_out ochan

let codegen metainfo =
  generate_main metainfo;
  generate_header metainfo
