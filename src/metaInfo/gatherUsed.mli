open Syntax

(** Gather definitions which an entry module depends on *)
val gather : xfrp Idmap.t -> string -> Idset.t
