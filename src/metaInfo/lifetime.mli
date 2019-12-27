open Syntax
open MetaInfo

(** Get life time information of an entry module *)
val fill_lifetime : xfrp Idmap.t -> string -> metainfo -> metainfo

