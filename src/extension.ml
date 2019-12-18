module Format = struct
  include Format

  let pp_list_sep sep_str pp_element =
    let separetor ppf () = fprintf ppf "%s@ " sep_str in
    pp_print_list pp_element ~pp_sep:separetor

  let pp_list_comma pp_element =
      pp_list_sep "," pp_element

  let pp_list_break pp_element =
    let separator ppf () = fprintf ppf "@;" in
    pp_print_list pp_element ~pp_sep:separator

  let pp_list_break2 pp_element =
    let separator ppf () = fprintf ppf "@;@;" in
    pp_print_list pp_element ~pp_sep:separator

  let pp_opt pp_some pp_none ppf = function
    | Some(x) -> pp_some ppf x
    | None -> pp_none ppf ()

  let pp_funcall pp_func pp_args ppf (f, args) : unit =
    fprintf ppf "%a(@[%a@])"
      pp_func f
      (pp_list_comma pp_args) args

  let pp_none _ppf () = ()
end
