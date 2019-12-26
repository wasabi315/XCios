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
end
