open Syntax
open MetaInfo

let update_nodelife clock self_id expr nodelife =

  let update id life =
    Idmap.add id (clock + 1) life
  in

  let rec rec_f (ast, _) nodelife =
    match ast with
    | EUniOp(_, e) -> rec_f e nodelife
    | EBinOp(_, e1, e2) -> nodelife |> rec_f e1 |> rec_f e2
    | EVariant(_, e) -> rec_f e nodelife
    | ETuple(es) -> List.fold_right rec_f es nodelife
    | EConst(_) -> nodelife
    | ERetain ->
       let () = assert (self_id != "") in (* for newnode input *)
       let lastref_life = update self_id nodelife.lastref_life in
       { nodelife with lastref_life = lastref_life }
    | EId (id, NodeId _) ->
       let curref_life = update id nodelife.curref_life in
       { nodelife with curref_life = curref_life }
    | EId (_, StateParam _) ->
       let lastref_life = update "switch" nodelife.lastref_life in
       { nodelife with lastref_life = lastref_life }
    | EId _ -> nodelife
    | EAnnot ((id, NodeId _), _) ->
       let lastref_life = update id nodelife.lastref_life in
       { nodelife with lastref_life = lastref_life }
    | EAnnot _ -> assert false
    | EFuncall(_, args) -> List.fold_right rec_f args nodelife
    | EIf(etest, ethen, eelse) ->
       nodelife |> rec_f etest |> rec_f ethen |> rec_f eelse
    | ELet(binders, e) ->
       nodelife
       |> List.fold_right (fun binder life ->
              rec_f binder.binder_body life
            ) binders
       |> rec_f e
    | ECase(e, branchs) ->
       nodelife
       |> rec_f e
       |> List.fold_right (fun branch life ->
              rec_f branch.branch_body life
            ) branchs
  in

  rec_f expr nodelife

let rec visit_node _all_data global_prefix def (clock, lifetime, nodelife) =
  let curref_life =
    Idmap.add def.node_id (clock + 1) nodelife.curref_life
  in
  let nodelife =
    { nodelife with curref_life = curref_life }
    |> update_nodelife clock def.node_id def.node_body
  in
  let clock = clock + 1 in
  let global_name = conc_id [global_prefix; def.node_id] in
  let timestamp = Idmap.add global_name clock lifetime.timestamp in
  let lifetime = { lifetime with timestamp = timestamp } in
  (clock, lifetime, nodelife)

and visit_newnode all_data _global_prefix def (clock, lifetime, nodelife) =
  let nodelife =
    List.fold_left (fun nodelife expr ->
        update_nodelife clock "" expr nodelife
      ) nodelife def.newnode_inputs
  in
  let instance_name = conc_id ["instance"; def.newnode_id] in
  match def.newnode_module with
  | (id, ModuleCons (file, _, _, _)) ->
     let filedata = Idmap.find file all_data in
     begin
       match Idmap.find id filedata.xfrp_all with
       | XFRPModule def ->
          let (clock, lifetime) =
            visit_module all_data instance_name def (clock, lifetime)
          in
          (clock, lifetime, nodelife)
       | XFRPSModule def ->
          let (clock, lifetime) =
            visit_smodule all_data instance_name def (clock, lifetime)
          in
          (clock, lifetime, nodelife)
       | _ -> assert false
     end
  | _ -> assert false

and visit_input_nodes clock (id, _, _) nodelife =
  let curref_life = Idmap.add id (clock+1) nodelife.curref_life in
  { nodelife with curref_life = curref_life }

and visit_init clock id init nodelife =
  match init with
  | Some _ ->
     let lastref_life = Idmap.add id (clock + 1) nodelife.lastref_life in
     { nodelife with lastref_life = lastref_life }
  | None -> nodelife

and visit_header_init clock (id, init, _) nodelife =
  visit_init clock id init nodelife

and visit_node_init clock node nodelife =
  visit_init clock node.node_id node.node_init nodelife

and visit_module all_data instance_name def (clock, lifetime) =
  let base_nodelife =
    nodelife_empty
    |> List.fold_right (visit_input_nodes clock) def.module_in
    |> List.fold_right (visit_header_init clock) def.module_in
    |> List.fold_right (visit_header_init clock) def.module_out
    |> idmap_fold_values (visit_node_init clock) def.module_nodes
  in
  let clock = clock + 1 in
  let timestamp =
    Idmap.add (conc_id [instance_name; "init"]) clock lifetime.timestamp
  in
  let lifetime = { lifetime with timestamp = timestamp } in
  let (clock, lifetime, nodelife) =
    List.fold_right (fun id (clock, lifetime, nodelife) ->
        match Idmap.find id def.module_all with
        | MNode def ->
           visit_node all_data instance_name def (clock, lifetime, nodelife)
        | MNewnode def ->
           visit_newnode all_data instance_name def (clock, lifetime, nodelife)
        | _ -> assert false
      ) (List.rev def.module_update_ord) (clock, lifetime, base_nodelife)
  in
  let nodelifes = Idmap.add instance_name nodelife lifetime.nodelifes in
  let lifetime = { lifetime with nodelifes = nodelifes } in
  (clock, lifetime)

and visit_switch _all_data state_name expr (clock, lifetime, nodelife) =
  let nodelife =
    update_nodelife clock "switch" expr nodelife
  in
  let clock = clock + 1 in
  let global_name = conc_id [state_name; "switch"] in
  let timestamp = Idmap.add global_name clock lifetime.timestamp in
  let lifetime = { lifetime with timestamp = timestamp } in
  (clock, lifetime, nodelife)

and visit_state all_data base_nodelife state_name def (clock, lifetime) =
  let nodelife =
    idmap_fold_values (visit_node_init clock) def.state_nodes base_nodelife
  in
  let clock = clock + 1 in
  let timestamp =
    Idmap.add (conc_id [state_name; "init"]) clock lifetime.timestamp
  in
  let lifetime = { lifetime with timestamp = timestamp } in
  let (clock, lifetime, nodelife) =
    (clock, lifetime, nodelife)
    |> List.fold_right (fun id (clock, lifetime, nodelife) ->
           match Idmap.find id def.state_all with
           | SNode def ->
              visit_node all_data state_name def (clock, lifetime, nodelife)
           | SNewnode def ->
              visit_newnode all_data state_name def (clock, lifetime, nodelife)
           | _ -> assert false
         ) (List.rev def.state_update_ord)
    |> visit_switch all_data state_name def.state_switch
  in
  let nodelifes = Idmap.add state_name nodelife lifetime.nodelifes in
  let lifetime = { lifetime with nodelifes = nodelifes } in
  (clock, lifetime)

and visit_state_init clock nodelife =
  let lastref_life = Idmap.add "switch" (clock + 1) nodelife.lastref_life in
  { nodelife with lastref_life = lastref_life}

and visit_smodule all_data instance_name def (clock, lifetime) =
  let base_nodelife =
    nodelife_empty
    |> List.fold_right (visit_input_nodes clock) def.smodule_in
    |> List.fold_right (visit_header_init clock) def.smodule_in
    |> List.fold_right (visit_header_init clock) def.smodule_out
    |> List.fold_right (visit_header_init clock) def.smodule_shared
    |> visit_state_init clock
  in
  let clock = clock + 1 in
  let timestamp =
    Idmap.add (conc_id [instance_name; "init"]) clock lifetime.timestamp
  in
  let lifetime = { lifetime with timestamp = timestamp } in
  Idmap.fold (fun _ def (next_clock, lifetime) ->
      let state_name = conc_id [instance_name; def.state_id] in
      let (next_clock', lifetime) =
        visit_state all_data base_nodelife state_name def (clock, lifetime)
      in
      (max next_clock next_clock', lifetime)
    ) def.smodule_states (clock, lifetime)

let extend_curref_life metainfo =
  let timestamp = metainfo.lifetime.timestamp in
  let clockperiod = metainfo.lifetime.clockperiod in
  let nodelifes =
    Idmap.mapi (fun instance_id nodelife ->
        let update_head =
          (Idmap.find (conc_id [instance_id; "init"]) timestamp) - 1
        in
        let next_update_head = update_head + clockperiod in
        let curref_life =
          Idmap.fold (fun id _ life ->
              Idmap.add id next_update_head life
            ) nodelife.lastref_life nodelife.curref_life
        in
        { nodelife with curref_life = curref_life }
      ) metainfo.lifetime.nodelifes
  in
  let lifetime = { metainfo.lifetime with nodelifes = nodelifes } in
  { metainfo with lifetime = lifetime }

let fill_lifetime all_data entry_file metainfo =
  let filedata = Idmap.find entry_file all_data in
  let main_instance_name = "instance_#0" in
  match Idmap.find "Main" filedata.xfrp_all with
  | XFRPModule def ->
     let (period, lifetime) =
       visit_module all_data main_instance_name def (0, lifetime_empty)
     in
     let lifetime = { lifetime with clockperiod = period } in
     { metainfo with lifetime = lifetime } |> extend_curref_life
  | XFRPSModule def ->
     let (period, lifetime) =
       visit_smodule all_data main_instance_name def (0, lifetime_empty)
     in
     let lifetime = { lifetime with clockperiod = period } in
     { metainfo with lifetime = lifetime } |> extend_curref_life
  | _ -> assert false
