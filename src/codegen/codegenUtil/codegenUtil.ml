open Extension
open Extension.Format
open Syntax
open Type
open MetaInfo

type writer = unit printer

(* writer for the prototype and writer for the definition *)
type fun_writer = writer * writer

let exec_all_writers ?(pp_sep = pp_print_cut) () ppf writers =
  let exec ppf writer = fprintf ppf "%a" writer () in
  (pp_print_list exec ~pp_sep) ppf writers
;;

let gen_codeblock gen_head gen_body ppf () =
  fprintf ppf "@[<v>%a {@;<0 2>" gen_head ();
  fprintf ppf "@[%a@]@;" gen_body ();
  fprintf ppf "}@]"
;;

let gen_anonymous_struct gen_body var_name ppf () =
  fprintf
    ppf
    "%a %a;"
    (gen_codeblock (fun ppf () -> pp_print_string ppf "struct") gen_body)
    ()
    pp_print_string
    var_name
;;

let gen_anonymous_union gen_body var_name ppf () =
  fprintf
    ppf
    "%a %a;"
    (gen_codeblock (fun ppf () -> pp_print_string ppf "union") gen_body)
    ()
    pp_print_string
    var_name
;;

let gen_tstate_typename ppf (file, module_id) =
  let file = String.capitalize_ascii file in
  fprintf ppf "State%s%s" file module_id
;;

let gen_tid_typename ppf (file, type_id) =
  let file = String.capitalize_ascii file in
  fprintf ppf "%s%s" file type_id
;;

let rec gen_ttuple_typename ppf ts =
  let gen_element_name ppf = function
    | TBool -> pp_print_string ppf "Bool"
    | TInt -> pp_print_string ppf "Int"
    | TFloat -> pp_print_string ppf "Double"
    | TState (file, module_name) -> gen_tstate_typename ppf (file, module_name)
    | TId (file, type_name) -> gen_tid_typename ppf (file, type_name)
    | TTuple ts -> gen_ttuple_typename ppf ts
    | _ -> assert false
  in
  fprintf ppf "Tuple%a" (pp_print_list gen_element_name ~pp_sep:pp_none) ts
;;

let gen_mode_name ppf (file, mode_id) =
  let file = String.capitalize_ascii file in
  fprintf ppf "Mode%s%s" file mode_id
;;

let gen_global_constname ppf (file, const_id) =
  let file = String.capitalize_ascii file in
  pp_print_string ppf (conc_id [ file; const_id ])
;;

let gen_global_funname ppf (file, fun_id) =
  let file = String.capitalize_ascii file in
  pp_print_string ppf (conc_id [ file; fun_id ])
;;

let rec gen_value_type metainfo ppf t =
  let enum_types = metainfo.typedata.enum_types in
  match t with
  | TBool | TInt -> pp_print_string ppf "int"
  | TFloat -> pp_print_string ppf "double"
  | TState (file, module_name) ->
    let file = String.capitalize_ascii file in
    if Hashset.mem enum_types t
    then pp_print_string ppf "int"
    else fprintf ppf "struct %a*" gen_tstate_typename (file, module_name)
  | TId (file, type_name) ->
    let file = String.capitalize_ascii file in
    if Hashset.mem enum_types t
    then pp_print_string ppf "int"
    else fprintf ppf "struct %a*" gen_tid_typename (file, type_name)
  | TTuple ts -> fprintf ppf "struct %a*" gen_ttuple_typename ts
  | TMode (_, _, t) -> gen_value_type metainfo ppf t
  | _ -> assert false
;;

let gen_newnode_field ppf newnode =
  let len = String.length newnode.newnode_id in
  let number_str = String.sub newnode.newnode_id 1 (len - 1) in
  fprintf ppf "newnode%s" number_str
;;

let gen_global_modulename ppf (file, module_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "%s%s" file module_name
;;

let gen_module_memory_type ppf (file, module_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "struct Memory%a" gen_global_modulename (file, module_name)
;;

let gen_global_statename ppf (file, module_name, state_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "%s%s%s" file module_name state_name
;;

let gen_state_memory_type ppf (file, module_name, state_name) =
  let file = String.capitalize_ascii file in
  fprintf ppf "struct Memory%a" gen_global_statename (file, module_name, state_name)
;;

let gen_tid_consname ppf (file, type_id, cons_id) =
  fprintf ppf "%a_%a" gen_tid_typename (file, type_id) pp_print_string cons_id
;;

let gen_ttuple_consname ppf types = fprintf ppf "%a_Cons" gen_ttuple_typename types

let gen_tstate_consname ppf (file, module_id, cons_id) =
  fprintf ppf "%a_%a" gen_tstate_typename (file, module_id) pp_print_string cons_id
;;

let gen_mode_calc_fun_name ppf (modul, node_id) =
  fprintf ppf "%a_calc_mode_%a" gen_global_modulename modul pp_identifier node_id
;;

let gen_module_init ppf () = fprintf ppf "memory->init"
let gen_state_init state_id ppf () = fprintf ppf "memory->statebody.%s.init" state_id
let gen_module_node_address ppf (_nattr, node_id) = fprintf ppf "memory->%s" node_id

let gen_module_node_curr_address ppf (_nattr, node_id, ty) =
  match ty with
  | TMode _ -> fprintf ppf "memory->%s->value" node_id
  | _ -> fprintf ppf "memory->%s[current_side]" node_id
;;

let gen_module_node_last_address ppf (_nattr, node_id) =
  fprintf ppf "memory->%s[!current_side]" node_id
;;

let gen_state_node_address state_id ppf (nattr, node_id) =
  match nattr with
  | InputNode | SharedNode | OutputNode -> fprintf ppf "memory->%s" node_id
  | NormalNode -> fprintf ppf "memory->statebody.%s.%s" state_id node_id
;;

let gen_state_node_curr_address state_id ppf (nattr, node_id, ty) =
  match nattr, ty with
  | (InputNode | OutputNode), TMode _ -> fprintf ppf "memory->%s->value" node_id
  | _, TMode _ -> assert false
  | (InputNode | SharedNode | OutputNode), _ ->
    fprintf ppf "memory->%s[current_side]" node_id
  | NormalNode, _ -> fprintf ppf "memory->statebody.%s.%s[current_side]" state_id node_id
;;

let gen_state_node_last_address state_id ppf (nattr, node_id) =
  match nattr with
  | InputNode | SharedNode | OutputNode -> fprintf ppf "memory->%s[!current_side]" node_id
  | NormalNode -> fprintf ppf "memory->statebody.%s.%s[!current_side]" state_id node_id
;;

let get_module_sig metainfo file module_id =
  match Hashtbl.find metainfo.moduledata (file, module_id) with
  | ModuleInfo info -> info.module_param_sig, info.module_in_sig, info.module_out_sig
  | SModuleInfo info -> info.smodule_param_sig, info.smodule_in_sig, info.smodule_out_sig
;;

let rec get_mark_writer metainfo target_type gen_address gen_life =
  match target_type with
  | TBool | TInt | TFloat -> None
  | TState (file, module_id) ->
    let writer ppf () =
      fprintf
        ppf
        "@[<h>mark_%a(%a, %a);@]"
        gen_tstate_typename
        (file, module_id)
        gen_address
        ()
        gen_life
        ()
    in
    Some writer
  | TId (file, type_id) ->
    if Hashset.mem metainfo.typedata.enum_types target_type
    then None
    else (
      let writer ppf () =
        fprintf
          ppf
          "@[<h>mark_%a(%a, %a);@]"
          gen_tid_typename
          (file, type_id)
          gen_address
          ()
          gen_life
          ()
      in
      Some writer)
  | TTuple types ->
    let writer ppf () =
      fprintf
        ppf
        "@[<h>mark_%a(%a, %a);@]"
        gen_ttuple_typename
        types
        gen_address
        ()
        gen_life
        ()
    in
    Some writer
  | TMode (_, _, t) -> get_mark_writer metainfo t gen_address gen_life
  | _ -> assert false
;;

let rec get_free_writer metainfo target_type gen_address =
  match target_type with
  | TBool | TInt | TFloat -> None
  | TState (file, module_id) ->
    let writer ppf () =
      fprintf
        ppf
        "@[<h>free_%a(%a);@]"
        gen_tstate_typename
        (file, module_id)
        gen_address
        ()
    in
    Some writer
  | TId (file, type_id) ->
    if Hashset.mem metainfo.typedata.enum_types target_type
    then None
    else (
      let writer ppf () =
        fprintf ppf "@[<h>free_%a(%a);@]" gen_tid_typename (file, type_id) gen_address ()
      in
      Some writer)
  | TTuple types ->
    let writer ppf () =
      fprintf ppf "@[<h>free_%a(%a);@]" gen_ttuple_typename types gen_address ()
    in
    Some writer
  | TMode (_, _, t) -> get_free_writer metainfo t gen_address
  | _ -> assert false
;;

let gen_update gen_body gen_mark_opt gen_tick_opt ppf () =
  fprintf ppf "@[<v>";
  gen_body ppf ();
  (match gen_mark_opt with
   | Some writer -> fprintf ppf "@,%a" writer ()
   | None -> ());
  (match gen_tick_opt with
   | Some writer -> fprintf ppf "@,%a" writer ()
   | None -> ());
  fprintf ppf "@]"
;;
