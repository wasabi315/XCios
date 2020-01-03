open Syntax
open MetaInfo

(** Calculate max requirement size for each type *)
val calc_alloc_amount : xfrp Idmap.t -> metainfo -> metainfo
