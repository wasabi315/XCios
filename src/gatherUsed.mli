open Syntax
open MetaInfo

(** Gather definitions which an entry module depends on *)
val fill_used_materials : xfrp Idmap.t -> string -> metainfo -> metainfo
