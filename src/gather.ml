open Syntax

let update_used all_data expr used =
  let rec rec_f (ast, _) used =
    match ast with
    | EUniOp(_, e) -> rec_f e used
    | EBinOp(_, e1, e2) -> used |> rec_f e1 |> rec_f e2
    | EVariant(_, e) -> rec_f e used
    | ETuple(es) -> List.fold_right rec_f es used
    | EId (id, ConstId (file, _)) ->
       let global_name = conc_id [file; "const"; id] in
       if Idset.mem global_name used then used else
         let filedata = Idmap.find file all_data in
         let constdef = Idmap.find id filedata.xfrp_consts in
         used |> rec_f constdef.const_body |> Idset.add global_name
    | EConst _ | ERetain | EId _ | EAnnot _ -> used
    | EFuncall((id, FunId (file, _, _)), args) ->
       let used = List.fold_right rec_f args used in
       let global_name = conc_id [file; "fun"; id] in
       if Idset.mem global_name used then used else
         let filedata = Idmap.find file all_data in
         let fundef = Idmap.find id filedata.xfrp_funs in
         used |> rec_f fundef.fun_body |> Idset.add global_name
    | EFuncall _ -> assert false
    | EIf(etest, ethen, eelse) ->
       used |> rec_f etest |> rec_f ethen |> rec_f eelse
    | ELet(binders, e) ->
       used
       |> List.fold_right (fun binder used ->
              rec_f binder.binder_body used
            ) binders
       |> rec_f e
    | ECase(e, branchs) ->
       used
       |> rec_f e
       |> List.fold_right (fun branch used ->
              rec_f branch.branch_body used
            ) branchs
  in
  rec_f expr used

let rec visit_node all_data def used =
  let used =
    match def.node_init with
    | Some e -> update_used all_data e used
    | None -> used
  in
  update_used all_data def.node_body used

and visit_newnode all_data def used =
  let used =
    used
    |> List.fold_right (update_used all_data) def.newnode_margs
    |> List.fold_right (update_used all_data) def.newnode_inputs
  in
  match def.newnode_module with
  | (id, ModuleCons (file, _, _, _)) ->
     let filedata = Idmap.find file all_data in
     begin
       match Idmap.find id filedata.xfrp_all with
       | XFRPModule def ->
          let global_name = conc_id [file; "module"; def.module_id] in
          if Idset.mem global_name used then used else
            visit_module all_data file def used
       | XFRPSModule def ->
          let global_name = conc_id [file; "smodule"; def.smodule_id] in
          if Idset.mem global_name used then used else
            visit_smodule all_data file def used
       | _ -> assert false
     end
  | _ -> assert false

and visit_header_node all_data (_, init, _) used =
  match init with
  | Some e -> update_used all_data e used
  | None -> used

and visit_module_materials all_data consts nodes newnodes used =
  used
  |> Idmap.fold (fun _ def used ->
         update_used all_data def.const_body used
       ) consts
  |> Idmap.fold (fun _ def used ->
         visit_node all_data def used
       ) nodes
  |> Idmap.fold (fun _ def used ->
         visit_newnode all_data def used
       ) newnodes

and visit_module all_data file def used =
  let global_name = conc_id [file; "module"; def.module_id] in
  used
  |> Idset.add global_name
  |> List.fold_right (visit_header_node all_data) def.module_in
  |> List.fold_right (visit_header_node all_data) def.module_out
  |> visit_module_materials
       all_data def.module_consts def.module_nodes def.module_newnodes

and visit_state all_data def used =
  visit_module_materials
    all_data def.state_consts def.state_nodes def.state_newnodes used

and visit_smodule all_data file def used =
  let global_name = conc_id [file; "smodule"; def.smodule_id] in
  used
  |> Idset.add global_name
  |> List.fold_right (visit_header_node all_data) def.smodule_in
  |> List.fold_right (visit_header_node all_data) def.smodule_out
  |> List.fold_right (visit_header_node all_data) def.smodule_shared
  |> Idmap.fold (fun _ def used ->
         update_used all_data def.const_body used
       ) def.smodule_consts
  |> Idmap.fold (fun _ def used ->
         visit_state all_data def used
       ) def.smodule_states

let gather_def_module all_data entry_file def =
  visit_module all_data entry_file def Idset.empty
let gather_def_smodule all_data entry_file def =
  visit_smodule all_data entry_file def Idset.empty
