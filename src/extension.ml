module Format = struct
  include Format
  (* A pretty printer for list. Separator is comma + space (break hint) *)
  let pp_list_comma pp_element =
    let separetor ppf () = fprintf ppf ",@ " in
    pp_print_list pp_element ~pp_sep:separetor

  (* A pretty printer for option. *)
  let pp_opt pp_some pp_none ppf = function
    | Some(x) -> pp_some ppf x
    | None -> pp_none ppf ()
end

