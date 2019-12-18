open Syntax

(** Gather definitions which a module depends on *)
val gather_def_module : xfrp Idmap.t -> string -> xfrp_module -> Idset.t

(** Gather definitions which a switch module depends on *)
val gather_def_smodule : xfrp Idmap.t -> string -> xfrp_smodule -> Idset.t
