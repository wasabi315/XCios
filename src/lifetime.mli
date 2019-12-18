open Syntax
open Extension.Format

type nodelife =
  {
    curref_life  : int Idmap.t;
    lastref_life : int Idmap.t;
  }

type lifetime =
  {
    timestamp : int Idmap.t;
    nodelifes : nodelife Idmap.t;
  }

(** A pretty printer for nodelife *)
val pp_nodelife : formatter -> nodelife -> unit

(** A pretty printer for lifetime *)
val pp_lifetime : formatter -> lifetime -> unit

(** Get life time information of a module *)
val get_module_lifetime : xfrp Idmap.t -> xfrp_module -> lifetime

(** Get life time information of a switch module *)
val get_smodule_lifetime : xfrp Idmap.t -> xfrp_smodule -> lifetime

