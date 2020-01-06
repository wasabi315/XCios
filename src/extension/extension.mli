module Hashset : sig
  type 'a t = ('a, unit) Hashtbl.t

  (** Hashset.create n creates new empty set with size n *)
  val create : ?random:bool -> int -> 'a t

  (** Hashset.mem tests if x belongs to s *)
  val mem : 'a t -> 'a -> bool

  (** Hashset.add s x adds x to s *)
  val add : 'a t -> 'a -> unit
end

module Format : sig
  include module type of Format

  (** A type for printer of 'a *)
  type 'a printer = formatter -> 'a -> unit

  (** A pretty printer for list using `sep_str` + space break hint as a separator *)
  val pp_list_sep : string -> 'a printer -> ('a list) printer

  (** A pretty printer for list using comma + space break hint as a separator *)
  val pp_list_comma : 'a printer -> ('a list) printer

  (** A pretty printer for list using full break hint as a separator *)
  val pp_list_break : 'a printer -> ('a list) printer

  (** A pretty printer for list using double full break hint as a separator *)
  val pp_list_break2 : 'a printer -> ('a list) printer

  (** A pretty printer for option. *)
  val pp_opt : 'a printer -> unit printer -> ('a option) printer

  (** A pretty printer for funcall-like format (func(arg1, arg2, ...)) *)
  val pp_funcall : 'a printer -> 'b printer -> ('a * 'b list) printer

  (** A dummy pretty printer. Do nothing. *)
  val pp_none : unit printer

  (** Print comma and space break hint *)
  val pp_print_commaspace : unit printer

  (** Print cut break hint twice *)
  val pp_print_cut2 : unit printer

  (** A pretty printter for Hashtable *)
  val pp_print_hashtbl : ?pp_sep: unit printer ->
                         ('a * 'b) printer ->
                         ('a, 'b) Hashtbl.t printer

  (** A pretty printer for Hashset (= ('a, unit) Hashtbl.t) *)
  val pp_print_hashset : ?pp_sep:unit printer ->
                         'a printer ->
                         'a Hashset.t printer
end
