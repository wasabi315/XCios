module Hashset = struct
  type 'a t = ('a, unit) Hashtbl.t

  let create ?(random = false) size = Hashtbl.create size ~random
  let is_empty s = Hashtbl.length s = 0
  let mem s x = Hashtbl.mem s x
  let add s x = Hashtbl.add s x ()
  let remove s x = Hashtbl.remove s x
  let to_list s = Hashtbl.to_seq_keys s |> List.of_seq
end

module List = struct
  include List

  let pairs xs =
    List.concat_map
      (fun x -> List.concat_map (fun y -> if x = y then [] else [ x, y ]) xs)
      xs
  ;;
end

module Format = struct
  include Format

  type 'a printer = formatter -> 'a -> unit

  let pp_list_sep sep_str pp_element =
    let separetor ppf () = fprintf ppf "%s@ " sep_str in
    pp_print_list pp_element ~pp_sep:separetor
  ;;

  let pp_list_comma pp_element = pp_list_sep "," pp_element

  let pp_list_break pp_element =
    let separator ppf () = fprintf ppf "@;" in
    pp_print_list pp_element ~pp_sep:separator
  ;;

  let pp_list_break2 pp_element =
    let separator ppf () = fprintf ppf "@;@;" in
    pp_print_list pp_element ~pp_sep:separator
  ;;

  let pp_opt pp_some pp_none ppf = function
    | Some x -> pp_some ppf x
    | None -> pp_none ppf ()
  ;;

  let pp_funcall pp_func pp_args ppf (f, args) : unit =
    fprintf ppf "%a(@[%a@])" pp_func f (pp_list_comma pp_args) args
  ;;

  let pp_none _ppf () = ()
  let pp_print_commaspace ppf () = fprintf ppf ",@ "
  let pp_print_cut2 ppf () = fprintf ppf "@,@,"

  let pp_print_hashtbl ?(pp_sep = pp_print_cut) pp_key_value ppf table =
    let binds = Hashtbl.fold (fun k v binds -> (k, v) :: binds) table [] |> List.rev in
    pp_print_list pp_key_value ppf binds ~pp_sep
  ;;

  let pp_print_hashset ?(pp_sep = pp_print_cut) pp_key ppf set =
    let pp_key_value ppf (k, ()) = pp_key ppf k in
    pp_print_hashtbl pp_key_value ppf set ~pp_sep
  ;;
end
