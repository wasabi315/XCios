open Extension
open Extension.Format
open Syntax
open Type
open MetaInfo

let gen_codeblock gen_head gen_body ppf () =
  fprintf ppf "@[<v>%a {@;<0 2>" gen_head ();
  fprintf ppf "@[%a@]@;" gen_body ();
  fprintf ppf "}@]"

let gen_anonymous_struct gen_body var_name ppf () =
  fprintf ppf "%a %a;"
    (gen_codeblock (fun ppf () -> pp_print_string ppf "struct") gen_body) ()
    pp_print_string var_name

let gen_anonymous_union gen_body var_name ppf () =
  fprintf ppf "%a %a;"
    (gen_codeblock (fun ppf () -> pp_print_string ppf "union") gen_body) ()
    pp_print_string var_name

let gen_tstate_typename ppf (file, module_name) =
  fprintf ppf "State%s%s" file module_name

let gen_tid_typename ppf (file, type_name) =
  fprintf ppf "struct %s%s" file type_name

let rec gen_ttuple_typename ppf ts =

  let gen_element_name ppf = function
    | TBool -> pp_print_string ppf "Bool"
    | TInt -> pp_print_string ppf "Int"
    | TFloat -> pp_print_string ppf "Double"
    | TState(file, module_name) ->
       gen_tstate_typename ppf (file, module_name)
    | TId(file, type_name) ->
       gen_tid_typename ppf (file, type_name)
    | TTuple(ts) ->
       gen_ttuple_typename ppf ts
    | _ -> assert false
  in

  fprintf ppf "Tuple%a"
    (pp_print_list gen_element_name ~pp_sep:pp_none) ts

let gen_ctype metainfo ppf t =
  let enum_types = metainfo.typedata.enum_types in
  match t with
  | TBool | TInt -> pp_print_string ppf "int"
  | TFloat -> pp_print_string ppf "double"
  | TState(file, module_name) ->
     let file = String.capitalize_ascii file in
     if Hashset.mem enum_types t then
       pp_print_string ppf "int"
     else
       fprintf ppf "struct %a*" gen_tstate_typename (file, module_name)
  | TId(file, type_name) ->
     let file = String.capitalize_ascii file in
     if Hashset.mem enum_types t then
       pp_print_string ppf "int"
     else
       fprintf ppf "struct %a*" gen_tid_typename (file, type_name)
  | TTuple(ts) ->
     fprintf ppf "struct %a*" gen_ttuple_typename ts
  | _ -> assert false

let gen_newnode_field ppf newnode =
  let len = String.length newnode.newnode_id in
  let number_str = String.sub newnode.newnode_id 1 (len-1) in
  fprintf ppf "newnode%s" number_str

let gen_module_memory_name ppf (file, module_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "struct Memory%s%s" file module_name

let gen_state_memory_type ppf (file, module_name, state_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "struct Memory%s%s%s" file module_name state_name
