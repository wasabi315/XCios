open Extension.Format
open Syntax
open Type

let gen_codeblock gen_head gen_body ppf () =
  fprintf ppf "@[<v>%a {@;<0 2>" gen_head ();
  fprintf ppf "@[%a@]@;" gen_body ();
  fprintf ppf "}@]"

let rec gen_ctype ppf = function
  | TBool | TInt -> pp_print_string ppf "int"
  | TFloat -> pp_print_string ppf "double"
  | TState(file, module_name) ->
     let file = String.capitalize_ascii file in
     fprintf ppf "State%s%s*" file module_name
  | TId(file, type_name) ->
     let file = String.capitalize_ascii file in
     fprintf ppf "%s%s*" file type_name
  | TTuple(ts) ->
     fprintf ppf "Tuple%a*"
       (pp_print_list gen_ctype ~pp_sep:pp_none) ts
  | _ -> assert false

let get_newnode_field_name newnode =
  let len = String.length newnode.newnode_id in
  let number_str = String.sub newnode.newnode_id 1 (len-1) in
  "newnode" ^ number_str
