open Syntax
open MetaInfo

let lifetime_empty =
  { timestamp = Idmap.empty; free_current = Idmap.empty; free_last = Idmap.empty }
;;

let update_timestamp id clock lifetime =
  let timestamp = Idmap.add id clock lifetime.timestamp in
  { lifetime with timestamp }
;;

let update_free_current id life lifetime =
  let free_current =
    match Idmap.find_opt id lifetime.free_current with
    | Some None -> lifetime.free_current
    | Some (Some clock) ->
      let life = max life clock in
      Idmap.add id (Some life) lifetime.free_current
    | None -> Idmap.add id (Some life) lifetime.free_current
  in
  { lifetime with free_current }
;;

let update_free_last id life lifetime =
  let free_current = Idmap.add id None lifetime.free_current in
  let free_last =
    match Idmap.find_opt id lifetime.free_last with
    | Some clock ->
      let life = max life clock in
      Idmap.add id life lifetime.free_last
    | None -> Idmap.add id life lifetime.free_last
  in
  { lifetime with free_current; free_last }
;;

let visit_expr clock self_id expr lifetime =
  let rec rec_f (ast, _) lifetime =
    match ast with
    | EUniOp (_, e) -> rec_f e lifetime
    | EBinOp (_, e1, e2) -> lifetime |> rec_f e1 |> rec_f e2
    | EVariant (_, e) -> rec_f e lifetime
    | ETuple es -> List.fold_right rec_f es lifetime
    | EConst _ -> lifetime
    | ERetain ->
      let () = assert (self_id != "") in
      (* for newnode input *)
      update_free_last self_id (clock + 1) lifetime
    | EId (id, NodeId _) -> update_free_current id (clock + 1) lifetime
    | EId (_, StateParam _) -> update_free_last "state" (clock + 1) lifetime
    | EId _ -> lifetime
    | EAnnot ((id, NodeId _), _) -> update_free_last id (clock + 1) lifetime
    | EAnnot _ -> assert false
    | EFuncall (_, args) -> List.fold_right rec_f args lifetime
    | EIf (etest, ethen, eelse) -> lifetime |> rec_f etest |> rec_f ethen |> rec_f eelse
    | ELet (binders, e) ->
      lifetime
      |> List.fold_right (fun binder life -> rec_f binder.binder_body life) binders
      |> rec_f e
    | ECase (e, branchs) ->
      lifetime
      |> rec_f e
      |> List.fold_right (fun branch life -> rec_f branch.branch_body life) branchs
  in
  rec_f expr lifetime
;;

let rec visit_node def (clock, lifetime) =
  let lifetime = visit_expr clock def.node_id def.node_body lifetime in
  let clock = clock + 1 in
  let lifetime =
    lifetime
    |> update_free_current def.node_id clock
    |> update_timestamp def.node_id clock
  in
  clock, lifetime

and visit_newnode moduledata def (clock, lifetime, mode_calc) =
  let lifetime =
    List.fold_left
      (fun lifetime expr -> visit_expr clock "" expr lifetime)
      lifetime
      def.newnode_inputs
  in
  let clock, in_sig, out_sig =
    match def.newnode_module with
    | module_id, ModuleCons (file, _, _, _) ->
      (match Hashtbl.find moduledata (file, module_id) with
       | ModuleInfo info ->
         clock + info.module_clockperiod, info.module_in_sig, info.module_out_sig
       | SModuleInfo info ->
         clock + info.smodule_clockperiod, info.smodule_in_sig, info.smodule_out_sig)
    | _ -> assert false
  in
  let lifetime =
    lifetime
    |> List.fold_right
         (fun (_, id, _) lifetime -> update_free_current id clock lifetime)
         def.newnode_binds
    |> update_timestamp def.newnode_id clock
  in
  let mode_calc =
    List.fold_right2
      (fun (expr, _) (id2, ty) mode_calc ->
        match expr, ty with
        | EId (id1, _), Type.TMode _ ->
          let entry = Idmap.find id1 mode_calc in
          let entry =
            { entry with child_modev = (def.newnode_id, id2) :: entry.child_modev }
          in
          Idmap.add id1 entry mode_calc
        | _ -> mode_calc)
      def.newnode_inputs
      in_sig
      mode_calc
  in
  let mode_calc =
    List.fold_right2
      (fun (_, id1, _) (id2, ty) mode_calc ->
        match ty with
        | Type.TMode _ ->
          let entry = Idmap.find id1 mode_calc in
          let entry =
            { entry with child_modev = (def.newnode_id, id2) :: entry.child_modev }
          in
          Idmap.add id1 entry mode_calc
        | _ -> mode_calc)
      def.newnode_binds
      out_sig
      mode_calc
  in
  clock, lifetime, mode_calc

and visit_input_node (id, _, _) lifetime = update_free_current id 2 lifetime

and visit_init id init lifetime =
  match init with
  | Some _ -> update_free_last id 2 lifetime
  | None -> lifetime

and visit_header_init (id, init, _) lifetime = visit_init id init lifetime
and visit_node_init node lifetime = visit_init node.node_id node.node_init lifetime

and visit_mode_annot annot =
  annot
  |> List.to_seq
  |> Seq.map (function
    | node_id, (modev, ModeValue (file, mode_id, _)) ->
      node_id, { mode_type = file, mode_id; self_modev = modev; child_modev = [] }
    | _ -> assert false)
  |> Idmap.of_seq

and visit_module file def moduledata =
  let param_sig = def.module_params in
  let in_sig = List.map (fun (id, _, t) -> id, t) def.module_in in
  let out_sig = List.map (fun (id, _, t) -> id, t) def.module_out in
  let mode_calc = visit_mode_annot def.module_mode_annot in
  let lifetime =
    lifetime_empty
    |> List.fold_right visit_input_node def.module_in
    |> List.fold_right visit_header_init def.module_in
    |> List.fold_right visit_header_init def.module_out
    |> idmap_fold_values visit_node_init def.module_nodes
  in
  let clock = 2 in
  let clock, lifetime, mode_calc =
    List.fold_right
      (fun id (clock, lifetime, mode_calc) ->
        match Idmap.find id def.module_all with
        | MNode def ->
          let clock, lifetime = visit_node def (clock, lifetime) in
          clock, lifetime, mode_calc
        | MNewnode def -> visit_newnode moduledata def (clock, lifetime, mode_calc)
        | _ -> assert false)
      (List.rev def.module_update_ord)
      (clock, lifetime, mode_calc)
  in
  let clock = clock + 1 in
  let lifetime =
    List.fold_left
      (fun lifetime (id, _, _) -> update_free_current id clock lifetime)
      lifetime
      def.module_out
  in
  let module_info =
    { module_clockperiod = clock
    ; module_param_sig = param_sig
    ; module_in_sig = in_sig
    ; module_out_sig = out_sig
    ; module_lifetime = lifetime
    ; module_mode_calc = mode_calc
    }
  in
  Hashtbl.add moduledata (file, def.module_id) (ModuleInfo module_info);
  moduledata

and visit_switch expr (clock, lifetime) =
  let lifetime = visit_expr clock "state" expr lifetime in
  let clock = clock + 1 in
  let lifetime = update_timestamp "state" clock lifetime in
  clock, lifetime

and visit_state moduledata def lifetime mode_calc =
  let lifetime = idmap_fold_values visit_node_init def.state_nodes lifetime in
  let clock = 2 in
  let clock, lifetime, mode_calc =
    List.fold_right
      (fun id (clock, lifetime, mode_calc) ->
        match Idmap.find id def.state_all with
        | SNode def ->
          let clock, lifetime = visit_node def (clock, lifetime) in
          clock, lifetime, mode_calc
        | SNewnode def -> visit_newnode moduledata def (clock, lifetime, mode_calc)
        | _ -> assert false)
      (List.rev def.state_update_ord)
      (clock, lifetime, mode_calc)
  in
  let clock, lifetime = visit_switch def.state_switch (clock, lifetime) in
  clock, lifetime, mode_calc

and visit_state_init lifetime = update_free_last "state" 2 lifetime

and visit_smodule file def moduledata =
  let lifetime =
    lifetime_empty
    |> List.fold_right visit_input_node def.smodule_in
    |> List.fold_right visit_header_init def.smodule_in
    |> List.fold_right visit_header_init def.smodule_out
    |> List.fold_right visit_header_init def.smodule_shared
    |> visit_state_init
  in
  let clock, state_lifetime, state_mode_calc =
    idmap_fold_values
      (fun state (clock, state_lifetime, state_mode_calc) ->
        let mode_calc = visit_mode_annot state.state_mode_annot in
        let clock', lifetime', mode_calc =
          visit_state moduledata state lifetime mode_calc
        in
        let clock = max clock clock' in
        let state_lifetime = Idmap.add state.state_id lifetime' state_lifetime in
        let state_mode_calc = Idmap.add state.state_id mode_calc state_mode_calc in
        clock, state_lifetime, state_mode_calc)
      def.smodule_states
      (0, Idmap.empty, Idmap.empty)
  in
  let clock = clock + 1 in
  let state_lifetime =
    Idmap.map
      (fun lifetime ->
        List.fold_left
          (fun lifetime (id, _, _) -> update_free_current id clock lifetime)
          lifetime
          def.smodule_out)
      state_lifetime
  in
  let param_sig = def.smodule_params in
  let in_sig = List.map (fun (id, _, t) -> id, t) def.smodule_in in
  let out_sig = List.map (fun (id, _, t) -> id, t) def.smodule_out in
  let smodule_info =
    { smodule_clockperiod = clock
    ; smodule_param_sig = param_sig
    ; smodule_in_sig = in_sig
    ; smodule_out_sig = out_sig
    ; state_lifetime
    ; state_mode_calc
    }
  in
  Hashtbl.add moduledata (file, def.smodule_id) (SModuleInfo smodule_info);
  moduledata
;;

let calc_moduledata metainfo =
  let moduledata =
    List.fold_left
      (fun moduledata (file, module_or_smodule) ->
        match module_or_smodule with
        | XFRPModule m -> visit_module file m moduledata
        | XFRPSModule sm -> visit_smodule file sm moduledata
        | _ -> assert false)
      metainfo.moduledata
      metainfo.all_elements.all_modules
  in
  { metainfo with moduledata }
;;
