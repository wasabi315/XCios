open Syntax
open Type

exception Error of string

let check_name_conflict (f_id : 'a -> identifier) (elems : 'a list) : unit =
  let _ =
    List.fold_right
      (fun elem set ->
        let id = f_id elem in
        if Idset.mem id set
        then (
          let msg = Format.asprintf "Detect name confliction in %a" pp_identifier id in
          raise (Error msg))
        else Idset.add id set)
      elems
      Idset.empty
  in
  ()
;;

let check_name_conflict_module elems = check_name_conflict module_elem_id elems
let check_name_conflict_state elems = check_name_conflict state_elem_id elems
let check_name_conflict_smodule elems = check_name_conflict smodule_elem_id elems
let check_name_conflict_file elems = check_name_conflict xfrp_elem_id elems

let check_module_attr id = function
  | SharedNode ->
    let msg = Format.asprintf "Invalid node attribute for %a(shared)" pp_identifier id in
    raise (Error msg)
  | _ -> ()
;;

let check_module_attr_node (node : node) : unit =
  check_module_attr node.node_id node.node_attr
;;

let check_module_attr_newnode (newnode : newnode) : unit =
  List.iter (fun (attr, id, _) -> check_module_attr id attr) newnode.newnode_binds
;;

let check_nodes in_decls out_decls shared_decls nodes newnodes mode_annot =
  let register_node id attr conflict_msg_f all_nodes =
    match Idmap.find_opt id all_nodes with
    | Some _ ->
      let msg = conflict_msg_f id in
      raise (Error msg)
    | None -> Idmap.add id attr all_nodes
  in
  let get_all_declared_nodes out_decl shared_decl =
    let add id attr all_nodes =
      let conflict_msg_f id =
        Format.asprintf "Multiple node declaration : %a" pp_identifier id
      in
      register_node id attr conflict_msg_f all_nodes
    in
    Idmap.empty
    |> List.fold_right (fun (id, _, _) all_nodes -> add id OutputNode all_nodes) out_decl
    |> List.fold_right
         (fun (id, _, _) all_nodes -> add id SharedNode all_nodes)
         shared_decl
  in
  let get_all_defined_nodes nodes newnodes =
    let add id attr all_nodes =
      let conflict_msg_f id =
        Format.asprintf "Multiple node definition : %a" pp_identifier id
      in
      register_node id attr conflict_msg_f all_nodes
    in
    let add_newnode def all_nodes =
      List.fold_left
        (fun all_nodes (attr, id, _) -> add id attr all_nodes)
        all_nodes
        def.newnode_binds
    in
    Idmap.empty
    |> Idmap.fold (fun _ def all_nodes -> add def.node_id def.node_attr all_nodes) nodes
    |> Idmap.fold (fun _ def all_nodes -> add_newnode def all_nodes) newnodes
  in
  let get_all_nodes_with_mode in_decls out_decls =
    in_decls @ out_decls
    |> List.filter_map (function
      | id, _, TMode (_, _, _) -> Some id
      | _ -> None)
    |> Idset.of_list
  in
  let check_header_nodes_defined all_decls all_nodes =
    Idmap.iter
      (fun id decl_attr ->
        match Idmap.find_opt id all_nodes with
        | Some def_attr ->
          if decl_attr != def_attr
          then (
            let msg = Format.asprintf "Conflict node attribute : %a" pp_identifier id in
            raise (Error msg))
          else ()
        | None ->
          let msg = Format.asprintf "Header node is not defined : %a" pp_identifier id in
          raise (Error msg))
      all_decls
  in
  let check_undecl_header_nodes all_nodes all_decls =
    Idmap.iter
      (fun id def_attr ->
        let decl_attr_opt = Idmap.find_opt id all_decls in
        match def_attr, decl_attr_opt with
        | NormalNode, _ -> ()
        | _, Some decl_attr ->
          if decl_attr != def_attr
          then (
            let msg = Format.asprintf "Conflict node attribute : %a" pp_identifier id in
            raise (Error msg))
          else ()
        | _, None ->
          let msg = Format.asprintf "Undeclared header node : %a" pp_identifier id in
          raise (Error msg))
      all_nodes
  in
  let check_mode_annot all_nodes_with_mode mode_annot =
    let annotd_nodes = mode_annot |> List.map fst |> Idset.of_list in
    let non_annotd_nodes = Idset.diff all_nodes_with_mode annotd_nodes in
    if not (Idset.is_empty non_annotd_nodes)
    then (
      let msg = Format.asprintf "Not mode-annotated : %a" pp_idset non_annotd_nodes in
      raise (Error msg));
    let unneeded_annots = Idset.diff annotd_nodes all_nodes_with_mode in
    if not (Idset.is_empty unneeded_annots)
    then (
      let msg =
        Format.asprintf "Unneeded mode annotation : %a" pp_idset unneeded_annots
      in
      raise (Error msg))
  in
  let all_decls = get_all_declared_nodes out_decls shared_decls in
  let all_nodes = get_all_defined_nodes nodes newnodes in
  let all_nodes_with_mode = get_all_nodes_with_mode in_decls out_decls in
  check_header_nodes_defined all_decls all_nodes;
  check_undecl_header_nodes all_nodes all_decls;
  check_mode_annot all_nodes_with_mode mode_annot
;;
