open Syntax
open Type
open MetaInfo

let cache_sizeof_type : (Type.t, alloc_amount) Hashtbl.t =
  Hashtbl.create 20

let rec get_sizeof_type all_data t =
  match Hashtbl.find_opt cache_sizeof_type t with
  | Some(x) -> x
  | None ->
     begin
       match t with
       | TBool | TInt | TFloat | TUnit -> alloc_amount_empty ()
       | TState (file, module_id) ->
          let amount =
            calc_sizeof_tstate all_data file module_id
          in
          Hashtbl.add cache_sizeof_type t amount;
          amount
       | TId (file, type_id) ->
          let amount =
            calc_sizeof_tid all_data file type_id
          in
          Hashtbl.add cache_sizeof_type t amount;
          amount
       | TTuple ts ->
          let amount =
            calc_sizeof_ttuple all_data ts
          in
          Hashtbl.add cache_sizeof_type t amount;
          amount
       | _ -> assert false
     end

and calc_sizeof_tstate all_data file module_id =
  let filedata = Idmap.find file all_data in
  let smodule_def = Idmap.find module_id filedata.xfrp_smodules in
  let tstate = TState (file,module_id) in
  alloc_amount_empty ()
  |> idmap_fold_values (fun state size ->
         let tparams = List.map (fun (_, t) -> t) state.state_params in
         match tparams with
         | [] -> size
         | [t] ->
            get_sizeof_type all_data t
            |> alloc_amount_union size
         | ts ->
            get_sizeof_type all_data (TTuple ts)
            |> alloc_amount_union size
       ) smodule_def.smodule_states
  |> (fun size -> Hashtbl.add size tstate 1; size)

and calc_sizeof_tid all_data file type_id =
  let filedata = Idmap.find file all_data in
  let type_def = Idmap.find type_id filedata.xfrp_types in
  let tid = TId (file, type_id) in
  alloc_amount_empty ()
  |> idmap_fold_values (fun t amount ->
         get_sizeof_type all_data t |> alloc_amount_union amount
       ) type_def.type_conses
  |> (fun size -> Hashtbl.add size tid 1; size)

and calc_sizeof_ttuple all_data ts =
  let ttuple = TTuple ts in
  alloc_amount_empty ()
  |> List.fold_right (fun t amount ->
      get_sizeof_type all_data t
      |> alloc_amount_sum amount
    ) ts
  |> (fun size -> Hashtbl.add size ttuple 1; size)

let add_sizeof_type all_data t alloc_amount =
  get_sizeof_type all_data t |> alloc_amount_sum alloc_amount

let cache_req_expr_fun : (identifier, alloc_amount) Hashtbl.t =
  Hashtbl.create 20

let rec get_req_expr all_data expr =
  let rec rec_f (ast, t) =
    match ast with
    | EUniOp(_, e) -> rec_f e
    | EBinOp(_, e1, e2) ->
       let amount1 = rec_f e1 in
       let amount2 = rec_f e2 in
       alloc_amount_sum amount1 amount2
    | EVariant(_, e1) ->
       rec_f e1 |> (fun amount -> Hashtbl.add amount t 1; amount)
    | ETuple(es) ->
       alloc_amount_empty ()
       |> List.fold_right (fun e amount ->
              rec_f e |> alloc_amount_sum amount
            ) es
       |> (fun amount -> Hashtbl.add amount t 1; amount)
    | EConst(_) | ERetain | EId(_) | EAnnot(_, _) -> alloc_amount_empty ()
    | EFuncall((fname, finfo), args) ->
       begin
         match finfo with
         | FunId(file, _, _) ->
            get_req_expr_fun all_data file fname
            |> List.fold_right (fun e amount ->
                   rec_f e |> alloc_amount_sum amount
                 ) args
         | _ -> assert false
       end
    | EIf(etest, ethen, eelse) ->
       let amount_test = rec_f etest in
       let amount_then = rec_f ethen in
       let amount_else = rec_f eelse in
       alloc_amount_union amount_then amount_else
       |> alloc_amount_sum amount_test
    | ELet(binders, e) ->
       alloc_amount_empty ()
       |> List.fold_right (fun binder amount ->
              rec_f binder.binder_body |> alloc_amount_sum amount
            ) binders
       |> alloc_amount_sum (rec_f e)
    | ECase(e, branchs) ->
       alloc_amount_empty ()
       |> alloc_amount_sum (rec_f e)
       |> List.fold_right (fun branch amount ->
              rec_f branch.branch_body |> alloc_amount_union amount
            ) branchs
  in

  rec_f expr

and get_req_expr_fun all_data file fname =
  let global_name = conc_id [file; "fun"; fname] in
  match Hashtbl.find_opt cache_req_expr_fun global_name with
  | Some(x) -> x
  | None ->
     let file_data = Idmap.find file all_data in
     let fdef  = Idmap.find fname file_data.xfrp_funs in
     let amount = get_req_expr all_data fdef.fun_body in
     Hashtbl.add cache_req_expr_fun global_name amount;
     amount

let calc_req_begin all_data entry_file =

  let rec visit_init init req_begin =
    match init with
    | Some (_, t) -> add_sizeof_type all_data t req_begin
    | None -> req_begin

  and visit_const const req_begin =
    add_sizeof_type all_data const.const_type req_begin

  and visit_node node req_begin =
    visit_init node.node_init req_begin

  and visit_newnode newnode req_begin =
    match newnode.newnode_module with
    | (id, (ModuleCons (file, _, _, _))) ->
       let filedata = Idmap.find file all_data in
       begin
         match Idmap.find id filedata.xfrp_all with
         | XFRPModule m -> visit_module file m req_begin
         | XFRPSModule sm -> visit_smodule file sm req_begin
         | _ -> assert false
       end
    | _ -> assert false

  and visit_param (_, t) req_begin =
    add_sizeof_type all_data t req_begin

  and visit_header_node (_, init, _) req_begin =
    visit_init init req_begin

  and visit_module _file xfrp_module req_begin =
    req_begin
    |> List.fold_right visit_param xfrp_module.module_params
    |> List.fold_right visit_header_node xfrp_module.module_in
    |> List.fold_right visit_header_node xfrp_module.module_out
    |> idmap_fold_values visit_const xfrp_module.module_consts
    |> idmap_fold_values visit_node xfrp_module.module_nodes
    |> idmap_fold_values visit_newnode xfrp_module.module_newnodes

  and visit_state state req_begin =
    (* state parameters are included in state type value *)
    req_begin
    |> idmap_fold_values visit_const state.state_consts
    |> idmap_fold_values visit_node state.state_nodes
    |> idmap_fold_values visit_newnode state.state_newnodes

  and visit_smodule file xfrp_smodule req_begin =
    let tstate = TState (file, xfrp_smodule.smodule_id) in
    req_begin
    |> List.fold_right visit_param xfrp_smodule.smodule_params
    |> List.fold_right visit_header_node xfrp_smodule.smodule_in
    |> List.fold_right visit_header_node xfrp_smodule.smodule_out
    |> List.fold_right visit_header_node xfrp_smodule.smodule_shared
    |> add_sizeof_type all_data tstate
    |> idmap_fold_values visit_const xfrp_smodule.smodule_consts
    |> idmap_fold_values (fun state amount ->
           alloc_amount_empty ()
           |> visit_state state
           |> alloc_amount_union amount
         ) xfrp_smodule.smodule_states
  in

  let filedata = Idmap.find entry_file all_data in
  match Idmap.find "Main" filedata.xfrp_all with
  | XFRPModule def ->
     alloc_amount_empty () |> visit_module entry_file def
  | XFRPSModule def ->
     alloc_amount_empty () |> visit_smodule entry_file def
  | _ -> assert false

let get_free_table all_data node_to_type nodelife =

  let get_total_free_amount free_ids =
    alloc_amount_empty ()
    |> Idset.fold (fun id amount ->
           let sizeof_type = Idmap.find id node_to_type in
           add_sizeof_type all_data sizeof_type amount
         ) free_ids
  in
  
  let ref_life_to_free_table ref_life =
    to_timetable ref_life |> Intmap.map get_total_free_amount
  in

  let curref_table = ref_life_to_free_table nodelife.curref_life in
  let lastref_table = ref_life_to_free_table nodelife.lastref_life in
  Intmap.merge (fun _ v_cur v_last ->
      match v_cur, v_last with
      | Some amount1, Some amount2 -> Some (alloc_amount_sum amount1 amount2)
      | Some amount, None | None, Some amount -> Some amount
      | None, None -> None
    ) curref_table lastref_table
  
let get_module_free_table all_data xfrp_module nodelife =
  let node_to_type =
    Idmap.empty
    |> List.fold_right (fun (id, _, t) table ->
           Idmap.add id t table
         ) xfrp_module.module_in
    |> idmap_fold_values (fun node table ->
           Idmap.add node.node_id node.node_type table
         ) xfrp_module.module_nodes
    |> idmap_fold_values (fun newnode table ->
           List.fold_left (fun table (_, id, t) ->
               Idmap.add id t table
             ) table newnode.newnode_binds
         ) xfrp_module.module_newnodes
  in
  get_free_table all_data node_to_type nodelife
       
let get_state_free_table all_data xfrp_smodule state_id nodelife =
  let state = Idmap.find state_id xfrp_smodule.smodule_states in
  let (_, tstate) = state.state_switch in
  let node_to_type =
    Idmap.empty
    |> List.fold_right (fun (id, _, t) table ->
           Idmap.add id t table
         ) xfrp_smodule.smodule_in
    |> idmap_fold_values (fun node table ->
           Idmap.add node.node_id node.node_type table
         ) state.state_nodes
    |> idmap_fold_values (fun newnode table ->
           List.fold_left (fun table (_, id, t) ->
               Idmap.add id t table
             ) table newnode.newnode_binds
         ) state.state_newnodes
    |> Idmap.add "switch" tstate
  in
  get_free_table all_data node_to_type nodelife

let calc_alloc_amount all_data entry_file metainfo =
  let timestamp = metainfo.lifetime.timestamp in
  let nodelifes = metainfo.lifetime.nodelifes in

  let update_req_amount current expr req_amount =
    get_req_expr all_data expr
    |> alloc_amount_sum current
    |> alloc_amount_union req_amount
  in

  let free_noderef free_timetable clock current =
    match Intmap.find_opt clock free_timetable with
    | Some free_amount -> alloc_amount_diff current free_amount
    | None -> current
  in

  let visit_global_const const (current, req_amount) =
    let req_amount = update_req_amount current const.const_body req_amount in
    let current = add_sizeof_type all_data const.const_type current in
    (current, req_amount)
  in

  let rec visit_local_const current const req_amount =
    update_req_amount current const.const_body req_amount

  and visit_init current init_expr req_amount =
    match init_expr with
    | Some expr -> update_req_amount current expr req_amount
    | None -> req_amount

  and visit_node_init current node req_amount =
    visit_init current node.node_init req_amount

  and visit_node_body current node req_amount =
    update_req_amount current node.node_body req_amount

  and visit_newnode newnode (current, req_amount) =
    let req_amount =
      req_amount
      |> List.fold_right (update_req_amount current) newnode.newnode_margs
      |> List.fold_right (update_req_amount current) newnode.newnode_inputs
    in
    let instance_name = conc_id ["instance"; newnode.newnode_id] in
    match newnode.newnode_module with
    | (id, ModuleCons (file, _, _, _)) ->
       let filedata = Idmap.find file all_data in
       begin
         match Idmap.find id filedata.xfrp_all with
         | XFRPModule m ->
            visit_module instance_name m (current, req_amount)
         | XFRPSModule sm ->
            visit_smodule instance_name sm (current, req_amount)
         | _ -> assert false
       end
    | _ -> assert false

  and visit_header_node current (_, init, _) req_expr =
    visit_init current init req_expr

  and visit_module instance_name xfrp_module (current, req_amount) =
    let req_amount =
      req_amount
      |> List.fold_right (visit_header_node current) xfrp_module.module_in
      |> List.fold_right (visit_header_node current) xfrp_module.module_out
      |> idmap_fold_values (visit_local_const current) xfrp_module.module_consts
      |> idmap_fold_values (visit_node_init current) xfrp_module.module_nodes
    in
    let nodelife = Idmap.find instance_name nodelifes in
    let free_table =
      get_module_free_table all_data xfrp_module nodelife
    in
    List.fold_left (fun (current, req_amount) id ->
        match Idmap.find id xfrp_module.module_all with
        | MNode node ->
           let req_amount = visit_node_body current node req_amount in
           let global_name = conc_id [instance_name; node.node_id] in
           let now = Idmap.find global_name timestamp in
           let current =
             current
             |> add_sizeof_type all_data node.node_type
             |> free_noderef free_table now
           in
           (current, req_amount)
        | MNewnode def -> visit_newnode def (current, req_amount)
        | _ -> assert false
      ) (current, req_amount) xfrp_module.module_update_ord

  and visit_state state_name free_table state (current, req_amount) =
    let req_amount =
      req_amount
      |> idmap_fold_values (visit_local_const current) state.state_consts
      |> idmap_fold_values (visit_node_init current) state.state_nodes
    in
    let (current, req_amount) =
      List.fold_left (fun (current, req_amount) id ->
        match Idmap.find id state.state_all with
        | SNode node ->
           let req_amount = visit_node_body current node req_amount in
           let global_name = conc_id [state_name; node.node_id] in
           let now = Idmap.find global_name timestamp in
           let current =
             current
             |> add_sizeof_type all_data node.node_type
             |> free_noderef free_table now
           in
           (current, req_amount)
        | SNewnode def -> visit_newnode def (current, req_amount)
        | _ -> assert false
        ) (current, req_amount) state.state_update_ord
    in
    let req_amount =
      update_req_amount current state.state_switch req_amount
    in
    let (_, tstate) = state.state_switch in
    let clock_switch =
      Idmap.find (conc_id [state_name; "switch"]) timestamp
    in
    let current =
      current
      |> add_sizeof_type all_data tstate
      |> free_noderef free_table clock_switch
    in
    (current, req_amount)

  and visit_smodule instance_name xfrp_smodule (current, req_amount) =
    let req_amount =
      req_amount
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_in
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_out
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_shared
      |> update_req_amount current xfrp_smodule.smodule_init
      |> idmap_fold_values (visit_local_const current) xfrp_smodule.smodule_consts
    in
    idmap_fold_values (fun state (next, req_amount) ->
        let state_name = conc_id [instance_name; state.state_id] in
        let node_life = Idmap.find state_name nodelifes in
        let free_table =
          get_state_free_table
            all_data xfrp_smodule state.state_id node_life
        in
        let (next', req_amount) =
          visit_state state_name free_table state (current, req_amount)
        in
        let next = alloc_amount_union next next' in
        (next, req_amount)
      ) xfrp_smodule.smodule_states (alloc_amount_empty (), req_amount)
  in

  let (current, req_amount) =
    List.fold_left (fun (current, req_amount) file ->
        let filedata = Idmap.find file all_data in
        let material_ord =
          Dependency.tsort_materials filedata.xfrp_consts filedata.xfrp_funs
        in
        List.fold_left (fun (current, req_amount) id ->
            match Idmap.find_opt id filedata.xfrp_consts with
            | None -> (current, req_amount)
            | Some const ->
               let global_name = conc_id [file; "const"; const.const_id] in
               let used = Idset.mem global_name metainfo.used_materials in
               if not used then (current, req_amount) else
                 visit_global_const const (current, req_amount)
          ) (current, req_amount) material_ord
      ) (alloc_amount_empty (), alloc_amount_empty ()) metainfo.file_ord
  in
  let entry_filedata = Idmap.find entry_file all_data in
  let main_instance_name = "instance_#0" in
  let current =
    calc_req_begin all_data entry_file
    |> alloc_amount_sum current
  in
  match Idmap.find "Main" entry_filedata.xfrp_all with
  | XFRPModule m ->
     let (_, req_amount) =
       visit_module main_instance_name m (current, req_amount)
     in
     { metainfo with alloc_amount = req_amount }
  | XFRPSModule sm ->
     let (_, req_amount) =
       visit_smodule main_instance_name sm (current, req_amount)
     in
     { metainfo with alloc_amount = req_amount }
  | _ -> assert false
