open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo
open Type

let gen_param metainfo ppf (id, t) =
  fprintf ppf "@[<h>%a %a;@]" (gen_value_type metainfo) t pp_print_string id
;;

let gen_header_node metainfo ppf = function
  | id, _, TMode (file, mode_id, t) ->
    fprintf
      ppf
      "@[<h>struct %a* %a;@]"
      (gen_with_mode_type metainfo)
      (file, mode_id, t)
      pp_print_string
      id
  | id, _, t ->
    fprintf ppf "@[<h>%a %a[2];@]" (gen_value_type metainfo) t pp_print_string id
;;

let gen_local_const metainfo ppf const =
  fprintf
    ppf
    "@[<h>%a %a;@]"
    (gen_value_type metainfo)
    const.const_type
    pp_print_string
    const.const_id
;;

let gen_normal_node metainfo ppf node =
  match node.node_attr with
  | NormalNode ->
    fprintf
      ppf
      "@[<h>%a %a[2];@]"
      (gen_value_type metainfo)
      node.node_type
      pp_print_string
      node.node_id
  | _ -> ()
;;

let gen_newnode metainfo ppf newnode =
  let gen_normal_bind_node ppf (_, node_id, node_type) =
    fprintf
      ppf
      "@[<h>%a %a[2];@]"
      (gen_value_type metainfo)
      node_type
      pp_print_string
      node_id
  in
  let file, module_name =
    match newnode.newnode_module with
    | id, ModuleCons (file, _, _, _) -> file, id
    | _ -> assert false
  in
  let file = String.capitalize_ascii file in
  let normal_bind_nodes =
    List.filter_map
      (function
       | NormalNode, NBDef id, t -> Some (NormalNode, id, t)
       | _ -> None)
      newnode.newnode_binds
  in
  fprintf
    ppf
    "@[<h>%a %a;@]"
    gen_module_memory_type
    (file, module_name)
    gen_newnode_field
    newnode;
  if normal_bind_nodes = []
  then ()
  else fprintf ppf "@,%a" (pp_print_list gen_normal_bind_node) normal_bind_nodes
;;

let filter_normal_nodes nodes =
  List.filter
    (fun node ->
      match node.node_attr with
      | NormalNode -> true
      | _ -> false)
    nodes
;;

let gen_module metainfo ppf (file, xfrp_module) =
  let gen_head ppf () = gen_module_memory_type ppf (file, xfrp_module.module_id) in
  let gen_body ppf () =
    let params = xfrp_module.module_params in
    let in_nodes = xfrp_module.module_in in
    let out_nodes = xfrp_module.module_out in
    let consts = idmap_value_list xfrp_module.module_consts in
    let normal_nodes = idmap_value_list xfrp_module.module_nodes |> filter_normal_nodes in
    let newnodes = idmap_value_list xfrp_module.module_newnodes in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]";
    if params = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_param metainfo)) params;
    if in_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_header_node metainfo)) in_nodes;
    if out_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_header_node metainfo)) out_nodes;
    if consts = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_local_const metainfo)) consts;
    if normal_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_normal_node metainfo)) normal_nodes;
    if newnodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_newnode metainfo)) newnodes;
    fprintf ppf "@]"
  in
  fprintf ppf "%a;" (gen_codeblock gen_head gen_body) ()
;;

let gen_state metainfo ppf (file, module_name, state) =
  let gen_head ppf () = gen_state_memory_type ppf (file, module_name, state.state_id) in
  let gen_body ppf () =
    let consts = idmap_value_list state.state_consts in
    let normal_nodes = idmap_value_list state.state_nodes |> filter_normal_nodes in
    let newnodes = idmap_value_list state.state_newnodes in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]";
    (* state parameters are included in state type value *)
    if consts = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_local_const metainfo)) consts;
    if normal_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_normal_node metainfo)) normal_nodes;
    if newnodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_newnode metainfo)) newnodes;
    fprintf ppf "@]"
  in
  fprintf ppf "%a;" (gen_codeblock gen_head gen_body) ()
;;

let gen_smodule metainfo ppf (file, xfrp_smodule) =
  let gen_statebody ppf () =
    let gen_field ppf state =
      fprintf
        ppf
        "@[<h>%a %a;@]"
        gen_state_memory_type
        (file, xfrp_smodule.smodule_id, state.state_id)
        pp_print_string
        state.state_id
    in
    let gen_body ppf () =
      let states = idmap_value_list xfrp_smodule.smodule_states in
      fprintf ppf "@[<v>%a@]" (pp_print_list gen_field) states
    in
    (gen_anonymous_union gen_body "statebody") ppf ()
  in
  let gen_head ppf () = gen_module_memory_type ppf (file, xfrp_smodule.smodule_id) in
  let gen_body ppf () =
    let params = xfrp_smodule.smodule_params in
    let in_nodes = xfrp_smodule.smodule_in in
    let out_nodes = xfrp_smodule.smodule_out in
    let shared_nodes = xfrp_smodule.smodule_shared in
    let consts = idmap_value_list xfrp_smodule.smodule_consts in
    let _, tstate = xfrp_smodule.smodule_init in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]";
    if params = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_param metainfo)) params;
    if in_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_header_node metainfo)) in_nodes;
    if out_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_header_node metainfo)) out_nodes;
    if shared_nodes = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_header_node metainfo)) shared_nodes;
    if consts = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list (gen_local_const metainfo)) consts;
    fprintf ppf "@,@[<h>%a state;@]" (gen_value_type metainfo) tstate;
    fprintf ppf "@,%a" gen_statebody ();
    fprintf ppf "@]"
  in
  let gen_module_memory ppf () = fprintf ppf "%a;" (gen_codeblock gen_head gen_body) () in
  let file_module_state_list =
    idmap_value_list xfrp_smodule.smodule_states
    |> List.map (fun state -> file, xfrp_smodule.smodule_id, state)
  in
  let gen_all_state_memory = pp_print_list (gen_state metainfo) ~pp_sep:pp_print_cut2 in
  fprintf ppf "@[<v>";
  fprintf ppf "%a@,@,%a" gen_all_state_memory file_module_state_list gen_module_memory ();
  fprintf ppf "@]"
;;

let generate ppf metainfo =
  let gen_single_module ppf (file, module_or_smodule) =
    match module_or_smodule with
    | XFRPModule m -> gen_module metainfo ppf (file, m)
    | XFRPSModule sm -> gen_smodule metainfo ppf (file, sm)
    | _ -> assert false
  in
  (pp_print_list gen_single_module ~pp_sep:pp_print_cut2)
    ppf
    metainfo.all_elements.all_modules
;;
