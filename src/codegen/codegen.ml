open MetaInfo
open Extension.Format

let generate_main metainfo =
  printf "@[<v>";
  printf "%a" GenDataType.generate metainfo;
  printf "@,%a" GenMemory.generate metainfo;
  printf "@,%a" GenGlobal.generate metainfo;
  printf "@,%a" GenFun.generate metainfo;
  printf "@]"

let codegen metainfo =
  printf "%a@." pp_metainfo metainfo;
  generate_main metainfo
