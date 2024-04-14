open Extension.Format
open Syntax
open Type
open CodegenUtil
open MetaInfo

let get_params_free metainfo gen_address params =
  List.fold_left
    (fun writers param ->
      let _, param_type = param in
      let gen_address ppf () = gen_address ppf param in
      let free_writer_opt = get_free_writer metainfo param_type gen_address in
      match free_writer_opt with
      | Some writer -> writer :: writers
      | None -> writers)
    []
    params
  |> List.rev
;;

let get_consts_free metainfo gen_address consts =
  List.fold_left
    (fun writers const ->
      let gen_address ppf () = gen_address ppf const in
      let free_writer_opt = get_free_writer metainfo const.const_type gen_address in
      match free_writer_opt with
      | Some writer -> writer :: writers
      | None -> writers)
    []
    consts
  |> List.rev
;;

let get_nodes_free metainfo lifetime gen_address node_sigs =
  List.fold_left
    (fun writers node_sig ->
      let _, node_id, node_type = node_sig in
      let gen_address ppf () = gen_address ppf node_sig in
      let free_current = Idmap.find node_id lifetime.free_current in
      let free_writer_opt = get_free_writer metainfo node_type gen_address in
      match free_current, free_writer_opt with
      | None, Some writer -> writer :: writers
      | _, _ -> writers)
    []
    node_sigs
  |> List.rev
;;

let get_submodules_free gen_address newnodes =
  List.fold_left
    (fun writers newnode ->
      let file, module_id =
        match newnode.newnode_module with
        | module_id, ModuleCons (file, _, _, _) -> file, module_id
        | _ -> assert false
      in
      let submodule_free ppf () =
        fprintf
          ppf
          "free_%a(&(%a));"
          gen_global_modulename
          (file, module_id)
          gen_address
          newnode
      in
      submodule_free :: writers)
    []
    newnodes
  |> List.rev
;;

let define_module_free_fun metainfo (file, xfrp_module) fun_writers =
  let gen_funname ppf () =
    fprintf ppf "static void free_%a" gen_global_modulename (file, xfrp_module.module_id)
  in
  let gen_memorytype ppf () = gen_module_memory_type ppf (file, xfrp_module.module_id) in
  let gen_prototype ppf () = fprintf ppf "%a(%a*);" gen_funname () gen_memorytype () in
  let gen_definition ppf () =
    let gen_head ppf () = fprintf ppf "%a(%a* memory)" gen_funname () gen_memorytype () in
    let gen_body ppf () =
      let params_free =
        get_params_free
          metainfo
          (fun ppf (param_id, _) -> fprintf ppf "memory->%s" param_id)
          xfrp_module.module_params
      in
      let consts_free =
        get_consts_free
          metainfo
          (fun ppf const -> fprintf ppf "memory->%s" const.const_id)
          (idmap_value_list xfrp_module.module_consts)
      in
      let all_nodes =
        []
        |> List.fold_right
             (fun (id, _, t) nodes -> (InputNode, id, t) :: nodes)
             (List.rev xfrp_module.module_in)
        |> List.fold_right
             (fun (id, _, t) nodes -> (OutputNode, id, t) :: nodes)
             (List.rev xfrp_module.module_in)
        |> idmap_fold_values
             (fun node nodes ->
               if node.node_attr != NormalNode
               then nodes
               else (node.node_attr, node.node_id, node.node_type) :: nodes)
             xfrp_module.module_nodes
        |> idmap_fold_values
             (fun newnode nodes ->
               List.fold_left
                 (fun nodes (nattr, id, t) ->
                   if nattr != NormalNode then nodes else (nattr, id, t) :: nodes)
                 nodes
                 newnode.newnode_binds)
             xfrp_module.module_newnodes
        |> List.rev
      in
      let nodes_free =
        let lifetime =
          let module_id = xfrp_module.module_id in
          match Hashtbl.find metainfo.moduledata (file, module_id) with
          | ModuleInfo info -> info.module_lifetime
          | _ -> assert false
        in
        get_nodes_free
          metainfo
          lifetime
          (fun ppf (nattr, id, ty) ->
            match ty with
            | TMode _ -> fprintf ppf "memory->%s->value" id
            | _ -> fprintf ppf "%a[current_side]" gen_module_node_address (nattr, id))
          all_nodes
      in
      let submodules_free =
        get_submodules_free
          (fun ppf newnode -> fprintf ppf "memory->%a" gen_newnode_field newnode)
          (idmap_value_list xfrp_module.module_newnodes)
      in
      let all_writers = params_free @ consts_free @ nodes_free @ submodules_free in
      fprintf ppf "@[<v>";
      fprintf ppf "if (memory->init) return;";
      if all_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) all_writers;
      fprintf ppf "@,memory->init = 1;";
      fprintf ppf "@]"
    in
    (gen_codeblock gen_head gen_body) ppf ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;

let define_smodule_free_fun metainfo (file, xfrp_smodule) fun_writers =
  let gen_funname ppf () =
    fprintf ppf "static void free_%a" gen_global_modulename (file, xfrp_smodule.smodule_id)
  in
  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, xfrp_smodule.smodule_id)
  in
  let gen_prototype ppf () = fprintf ppf "%a(%a*);" gen_funname () gen_memorytype () in
  let gen_definition ppf () =
    let all_header_nodes =
      []
      |> List.fold_right
           (fun (id, _, t) nodes -> (InputNode, id, t) :: nodes)
           (List.rev xfrp_smodule.smodule_in)
      |> List.fold_right
           (fun (id, _, t) nodes -> (OutputNode, id, t) :: nodes)
           (List.rev xfrp_smodule.smodule_out)
      |> List.fold_right
           (fun (id, _, t) nodes -> (SharedNode, id, t) :: nodes)
           (List.rev xfrp_smodule.smodule_shared)
    in
    let state_lifetime =
      let module_id = xfrp_smodule.smodule_id in
      match Hashtbl.find metainfo.moduledata (file, module_id) with
      | SModuleInfo info -> info.state_lifetime
      | _ -> assert false
    in
    let gen_head ppf () = fprintf ppf "%a(%a* memory)" gen_funname () gen_memorytype () in
    let get_state_free state =
      let consts_free =
        get_consts_free
          metainfo
          (fun ppf const ->
            fprintf ppf "memory->statebody.%s.%s" state.state_id const.const_id)
          (idmap_value_list state.state_consts)
      in
      let all_nodes =
        all_header_nodes
        |> idmap_fold_values
             (fun node nodes ->
               if node.node_attr != NormalNode
               then nodes
               else (node.node_attr, node.node_id, node.node_type) :: nodes)
             state.state_nodes
        |> idmap_fold_values
             (fun newnode nodes ->
               List.fold_left
                 (fun nodes (nattr, id, t) ->
                   if nattr != NormalNode then nodes else (nattr, id, t) :: nodes)
                 nodes
                 newnode.newnode_binds)
             state.state_newnodes
        |> List.rev
      in
      let nodes_free =
        let lifetime = Idmap.find state.state_id state_lifetime in
        get_nodes_free
          metainfo
          lifetime
          (fun ppf (nattr, id, ty) ->
            match ty with
            | TMode _ -> fprintf ppf "memory->%s->value" id
            | _ ->
              fprintf
                ppf
                "%a[current_side]"
                (gen_state_node_address state.state_id)
                (nattr, id))
          all_nodes
      in
      let submodules_free =
        get_submodules_free
          (fun ppf newnode ->
            fprintf
              ppf
              "memory->statebody.%a.%a"
              pp_print_string
              state.state_id
              gen_newnode_field
              newnode)
          (idmap_value_list state.state_newnodes)
      in
      consts_free @ nodes_free @ submodules_free
    in
    let gen_body ppf () =
      let params_free =
        get_params_free
          metainfo
          (fun ppf (param_id, _) -> fprintf ppf "memory->%s" param_id)
          xfrp_smodule.smodule_params
      in
      let consts_free =
        get_consts_free
          metainfo
          (fun ppf const -> fprintf ppf "memory->%s" const.const_id)
          (idmap_value_list xfrp_smodule.smodule_consts)
      in
      let all_writers = params_free @ consts_free in
      let states_free =
        let tstate = TState (file, xfrp_smodule.smodule_id) in
        let tag_table = Hashtbl.find metainfo.typedata.cons_tag tstate in
        List.fold_left
          (fun states_free state ->
            let cons_tag = Idmap.find state.state_id tag_table in
            let state_free = get_state_free state in
            if state_free = [] then states_free else (cons_tag, state_free) :: states_free)
          []
          (idmap_value_list xfrp_smodule.smodule_states)
        |> List.rev
      in
      fprintf ppf "@[<v>";
      fprintf ppf "if (memory->init) return;";
      if all_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) all_writers;
      fprintf ppf "@,if (memory->state->fresh) {@,";
      fprintf ppf "}";
      if states_free = []
      then ()
      else
        (pp_print_list
           (fun ppf (tag, state_free) ->
             fprintf ppf " else if (memory->state->tag == %d) {@;<0 2>" tag;
             fprintf ppf "@[<v>%a@]@," (exec_all_writers ()) state_free;
             fprintf ppf "}")
           ~pp_sep:pp_none)
          ppf
          states_free;
      fprintf
        ppf
        "@,free_%a(memory->state);"
        gen_tstate_typename
        (file, xfrp_smodule.smodule_id);
      fprintf ppf "@,memory->init = 1;";
      fprintf ppf "@]"
    in
    (gen_codeblock gen_head gen_body) ppf ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;
