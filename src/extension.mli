module Format : sig
  include module type of Format

  (** A pretty printer for list using `sep_str` + space break hint as a separator *)
  val pp_list_sep : string ->
                    (formatter -> 'a -> unit) ->
                    formatter -> 'a list -> unit;;

  (** A pretty printer for list using comma + space break hint as a separator *)
  val pp_list_comma : (formatter -> 'a -> unit) ->
                      formatter -> 'a list -> unit;;

  (** A pretty printer for list using full break hint as a separator *)
  val pp_list_break : (formatter -> 'a -> unit) ->
                       formatter -> 'a list -> unit;;
  
  (** A pretty printer for list using double full break hint as a separator *)
  val pp_list_break2 : (formatter -> 'a -> unit) ->
                       formatter -> 'a list -> unit;;

  (** A pretty printer for option. *)
  val pp_opt : (formatter -> 'a -> unit) ->
               (formatter -> unit -> unit) ->
               formatter -> 'a option -> unit;;

  (** A pretty printer for funcall-like format (func(arg1, arg2, ...)) *)
  val pp_funcall : (formatter -> 'a -> unit) ->
                   (formatter -> 'b -> unit) ->
                   formatter -> 'a * 'b list -> unit;;

  (** A dummy pretty printer. Do nothing. *)
  val pp_none : formatter -> unit -> unit;;
end


