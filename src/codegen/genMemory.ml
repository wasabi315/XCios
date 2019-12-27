open Extension.Format
open Syntax
open Codegen
open MetaInfo

let gen_param ppf (id, t) =
  fprintf ppf "@[<h>%a %a;@]" gen_ctype t pp_print_string id

let gen_header_node ppf (id, _, t) =
  fprintf ppf "@[<h>%a %a[2];@]" gen_ctype t pp_print_string id

let gen_local_const ppf const =
  fprintf ppf "@[<h>%a %a;@]"
    gen_ctype const.const_type pp_print_string const.const_id

let gen_normal_node ppf node =
  match node.node_attr with
  | NormalNode ->
     fprintf ppf "@[<h>%a %a[2];@]"
       gen_ctype node.node_type pp_print_string node.node_id
  | _ -> ()

let gen_newnode ppf newnode =
  let (file, module_name) =
    match newnode.newnode_module with
    | (id, (ModuleCons (file, _, _, _))) -> (file, id)
    | _ -> assert false
  in
  let file = String.capitalize_ascii file in
  fprintf ppf "@[<h>Memory%a%a %a;@]"
    pp_print_string file
    pp_print_string module_name
    pp_print_string (get_newnode_field_name newnode)

let filter_normal_nodes nodes =
  List.filter (fun node ->
      match node.node_attr with
      | NormalNode -> true
      | _ -> false
    ) nodes

let gen_module ppf (file, xfrp_module) =
  let file = String.capitalize_ascii file in

  let gen_head ppf () =
    fprintf ppf "struct Memory%s%s" file xfrp_module.module_id
  in

  let gen_body ppf () =
    let params = xfrp_module.module_params in
    let in_nodes = xfrp_module.module_in in
    let out_nodes = xfrp_module.module_out in
    let consts = idmap_value_list xfrp_module.module_consts in
    let normal_nodes =
      idmap_value_list xfrp_module.module_nodes |> filter_normal_nodes
    in
    let newnodes = idmap_value_list xfrp_module.module_newnodes in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]@,";
    if params = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_param) params;
    if in_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_header_node) in_nodes;
    if out_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_header_node) out_nodes;
    if consts = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_local_const) consts;
    if normal_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_normal_node) normal_nodes;
    if newnodes = [] then () else
      fprintf ppf "%a" (pp_print_list gen_newnode) newnodes;
    fprintf ppf "@]"
  in

  (gen_codeblock gen_head gen_body) ppf ()

let gen_state ppf (module_name, state) =

  let gen_head ppf () =
    fprintf ppf "struct Memory%s%s" module_name state.state_id
  in

  let gen_body ppf () =
    let consts = idmap_value_list state.state_consts in
    let normal_nodes =
      idmap_value_list state.state_nodes |> filter_normal_nodes
    in
    let newnodes = idmap_value_list state.state_newnodes in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]@,";
    (* state parameters are included in state type value *)
    if consts = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_local_const) consts;
    if normal_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_normal_node) normal_nodes;
    if newnodes = [] then () else
      fprintf ppf "%a" (pp_print_list gen_newnode) newnodes;
    fprintf ppf "@]"
  in

  (gen_codeblock gen_head gen_body) ppf ()

let gen_smodule ppf (file, xfrp_smodule) =
  let file = String.capitalize_ascii file in

  let gen_state ppf () =

    let gen_field ppf state =
      fprintf ppf "@[<h>struct Memory%s%s%s %s;@]"
        file xfrp_smodule.smodule_id state.state_id state.state_id
    in

    let gen_head ppf () =
      pp_print_string ppf "union"
    in

    let gen_body ppf () =
      let states = idmap_value_list xfrp_smodule.smodule_states in
      fprintf ppf "@[<v>%a@]" (pp_print_list gen_field) states;
    in

    fprintf ppf "%a %a"
      (gen_codeblock gen_head gen_body) ()
      pp_print_string "memory"
  in

  let gen_head ppf () =
    fprintf ppf "struct Memory%s%s" file xfrp_smodule.smodule_id
  in

  let gen_body ppf () =
    let params = xfrp_smodule.smodule_params in
    let in_nodes = xfrp_smodule.smodule_in in
    let out_nodes = xfrp_smodule.smodule_out in
    let shared_nodes = xfrp_smodule.smodule_shared in
    let consts = idmap_value_list xfrp_smodule.smodule_consts in
    let (_, tstate) = xfrp_smodule.smodule_init in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int init;@]@,";
    if params = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_param) params;
    if in_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_header_node) in_nodes;
    if out_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_header_node) out_nodes;
    if shared_nodes = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_header_node) shared_nodes;
    if consts = [] then () else
      fprintf ppf "%a@," (pp_print_list gen_local_const) consts;
    fprintf ppf "@[<h>%a state;@]@," gen_ctype tstate;
    fprintf ppf "%a" gen_state ();
    fprintf ppf "@]"
  in

  (gen_codeblock gen_head gen_body) ppf ()

let generate ppf (all_data, metainfo) =

  let gen_single_module file ppf module_id =
    let filedata = Idmap.find file all_data in
    match Idmap.find module_id filedata.xfrp_all with
    | XFRPModule m -> gen_module ppf (file, m)
    | XFRPSModule sm -> gen_smodule ppf (file, sm)
    | _ -> assert false
  in

  let gen_single_file ppf file =
    let filedata = Idmap.find file all_data in
    let ord =
      Dependency.tsort_modules filedata.xfrp_modules filedata.xfrp_smodules
    in
    let generator = gen_single_module file in
    (pp_print_list generator) ppf ord
  in

  (pp_print_list gen_single_file) ppf metainfo.file_ord
