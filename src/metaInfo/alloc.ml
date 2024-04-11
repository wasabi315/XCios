open Syntax
open Type
open MetaInfo

let merge_alloc_amount f amount1 amount2 =
  let amount2 = Hashtbl.copy amount2 in
  Hashtbl.fold
    (fun t val1 amount2 ->
      match Hashtbl.find_opt amount2 t with
      | Some val2 ->
        Hashtbl.replace amount2 t (f val1 val2);
        amount2
      | None ->
        Hashtbl.add amount2 t val1;
        amount2)
    amount1
    amount2
;;

let alloc_amount_union amount1 amount2 = merge_alloc_amount max amount1 amount2
let alloc_amount_sum amount1 amount2 = merge_alloc_amount ( + ) amount1 amount2

exception AllocAmountDiffError

let alloc_amount_diff amount1 amount2 =
  let amount1 = Hashtbl.copy amount1 in
  Hashtbl.fold
    (fun t val2 amount1 ->
      match Hashtbl.find_opt amount1 t with
      | Some val1 ->
        let sub = val1 - val2 in
        if sub < 0 then raise AllocAmountDiffError else Hashtbl.replace amount1 t sub;
        amount1
      | None -> raise AllocAmountDiffError)
    amount2
    amount1
;;

let cache_sizeof_type : (Type.t, alloc_amount) Hashtbl.t = Hashtbl.create 20

let rec get_sizeof_type all_data t =
  match Hashtbl.find_opt cache_sizeof_type t with
  | Some x -> x
  | None ->
    (match t with
     | TBool | TInt | TFloat | TUnit -> alloc_amount_empty ()
     | TState (file, module_id) ->
       let amount = calc_sizeof_tstate all_data file module_id in
       Hashtbl.add cache_sizeof_type t amount;
       amount
     | TId (file, type_id) ->
       let amount = calc_sizeof_tid all_data file type_id in
       Hashtbl.add cache_sizeof_type t amount;
       amount
     | TTuple ts ->
       let amount = calc_sizeof_ttuple all_data ts in
       Hashtbl.add cache_sizeof_type t amount;
       amount
     | TMode (_, _, t) -> get_sizeof_type all_data t
     | _ -> assert false)

and calc_sizeof_tstate all_data file module_id =
  let filedata = Idmap.find file all_data in
  let smodule_def = Idmap.find module_id filedata.xfrp_smodules in
  let tstate = TState (file, module_id) in
  alloc_amount_empty ()
  |> idmap_fold_values
       (fun state sizeof_state ->
         let tparams = List.map (fun (_, t) -> t) state.state_params in
         let sizeof_params =
           List.fold_left
             (fun size t -> get_sizeof_type all_data t |> alloc_amount_sum size)
             (alloc_amount_empty ())
             tparams
         in
         alloc_amount_union sizeof_state sizeof_params)
       smodule_def.smodule_states
  |> fun size ->
  Hashtbl.add size tstate 1;
  size

and calc_sizeof_tid all_data file type_id =
  let filedata = Idmap.find file all_data in
  let type_def = Idmap.find type_id filedata.xfrp_types in
  let tid = TId (file, type_id) in
  alloc_amount_empty ()
  |> idmap_fold_values
       (fun t amount -> get_sizeof_type all_data t |> alloc_amount_union amount)
       type_def.type_conses
  |> fun size ->
  Hashtbl.add size tid 1;
  size

and calc_sizeof_ttuple all_data ts =
  let ttuple = TTuple ts in
  alloc_amount_empty ()
  |> List.fold_right
       (fun t amount -> get_sizeof_type all_data t |> alloc_amount_sum amount)
       ts
  |> fun size ->
  Hashtbl.add size ttuple 1;
  size
;;

let add_sizeof_type all_data t alloc_amount =
  get_sizeof_type all_data t |> alloc_amount_sum alloc_amount
;;

let cache_req_expr_fun : (identifier, alloc_amount) Hashtbl.t = Hashtbl.create 20

let rec get_req_expr all_data expr =
  let rec rec_f (ast, t) =
    match ast with
    | EUniOp (_, e) -> rec_f e
    | EBinOp (_, e1, e2) ->
      let amount1 = rec_f e1 in
      let amount2 = rec_f e2 in
      alloc_amount_sum amount1 amount2
    | EVariant (_, e1) ->
      rec_f e1
      |> fun amount ->
      Hashtbl.add amount t 1;
      amount
    | ETuple es ->
      alloc_amount_empty ()
      |> List.fold_right (fun e amount -> rec_f e |> alloc_amount_sum amount) es
      |> fun amount ->
      Hashtbl.add amount t 1;
      amount
    | EConst _ | ERetain | EId _ | EAnnot (_, _) -> alloc_amount_empty ()
    | EFuncall ((fname, finfo), args) ->
      (match finfo with
       | FunId (file, _, _) ->
         get_req_expr_fun all_data file fname
         |> List.fold_right (fun e amount -> rec_f e |> alloc_amount_sum amount) args
       | _ -> assert false)
    | EIf (etest, ethen, eelse) ->
      let amount_test = rec_f etest in
      let amount_then = rec_f ethen in
      let amount_else = rec_f eelse in
      alloc_amount_union amount_then amount_else |> alloc_amount_sum amount_test
    | ELet (binders, e) ->
      alloc_amount_empty ()
      |> List.fold_right
           (fun binder amount -> rec_f binder.binder_body |> alloc_amount_sum amount)
           binders
      |> alloc_amount_sum (rec_f e)
    | ECase (e, branchs) ->
      alloc_amount_empty ()
      |> alloc_amount_sum (rec_f e)
      |> List.fold_right
           (fun branch amount -> rec_f branch.branch_body |> alloc_amount_union amount)
           branchs
  in
  rec_f expr

and get_req_expr_fun all_data file fname =
  let global_name = conc_id [ file; "fun"; fname ] in
  match Hashtbl.find_opt cache_req_expr_fun global_name with
  | Some x -> x
  | None ->
    let file_data = Idmap.find file all_data in
    let fdef = Idmap.find fname file_data.xfrp_funs in
    let amount = get_req_expr all_data fdef.fun_body in
    Hashtbl.add cache_req_expr_fun global_name amount;
    amount
;;

let calc_req_begin all_data entry_file =
  let rec visit_init init req_begin =
    match init with
    | Some (_, t) -> add_sizeof_type all_data t req_begin
    | None -> req_begin
  and visit_const const req_begin = add_sizeof_type all_data const.const_type req_begin
  and visit_node node req_begin = visit_init node.node_init req_begin
  and visit_newnode newnode req_begin =
    match newnode.newnode_module with
    | id, ModuleCons (file, _, _, _) ->
      let filedata = Idmap.find file all_data in
      (match Idmap.find id filedata.xfrp_all with
       | XFRPModule m -> visit_module file m req_begin
       | XFRPSModule sm -> visit_smodule file sm req_begin
       | _ -> assert false)
    | _ -> assert false
  and visit_param (_, t) req_begin = add_sizeof_type all_data t req_begin
  and visit_header_node (_, init, _) req_begin = visit_init init req_begin
  and visit_top_input (_, _, t) req_begin = add_sizeof_type all_data t req_begin
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
    |> idmap_fold_values
         (fun state amount ->
           alloc_amount_empty () |> visit_state state |> alloc_amount_union amount)
         xfrp_smodule.smodule_states
  in
  let filedata = Idmap.find entry_file all_data in
  let main = Idmap.find "Main" filedata.xfrp_all in
  match main with
  | XFRPModule def ->
    alloc_amount_empty ()
    |> List.fold_right visit_top_input def.module_in
    |> visit_module entry_file def
  | XFRPSModule def ->
    alloc_amount_empty ()
    |> List.fold_right visit_top_input def.smodule_in
    |> visit_smodule entry_file def
  | _ -> assert false
;;

let get_free_table all_data node_to_type lifetime =
  let update_free_table clock t table =
    match Intmap.find_opt clock table with
    | Some amount ->
      let free_amount = add_sizeof_type all_data t amount in
      Intmap.add clock free_amount table
    | None ->
      let free_amount = get_sizeof_type all_data t in
      Intmap.add clock free_amount table
  in
  Intmap.empty
  |> Idmap.fold
       (fun id clock_opt free_table ->
         let t = Idmap.find id node_to_type in
         match clock_opt with
         | Some clock -> update_free_table clock t free_table
         | None -> free_table)
       lifetime.free_current
  |> Idmap.fold
       (fun id clock free_table ->
         let t = Idmap.find id node_to_type in
         update_free_table clock t free_table)
       lifetime.free_last
;;

let get_module_free_table all_data xfrp_module lifetime =
  let node_to_type =
    Idmap.empty
    |> List.fold_right
         (fun (id, _, t) table -> Idmap.add id t table)
         (xfrp_module.module_in @ xfrp_module.module_out)
    |> idmap_fold_values
         (fun node table -> Idmap.add node.node_id node.node_type table)
         xfrp_module.module_nodes
    |> idmap_fold_values
         (fun newnode table ->
           List.fold_left
             (fun table (_, id, t) -> Idmap.add id t table)
             table
             newnode.newnode_binds)
         xfrp_module.module_newnodes
  in
  get_free_table all_data node_to_type lifetime
;;

let get_state_free_table all_data xfrp_smodule state_id lifetime =
  let state = Idmap.find state_id xfrp_smodule.smodule_states in
  let _, tstate = state.state_switch in
  let node_to_type =
    Idmap.empty
    |> List.fold_right
         (fun (id, _, t) table -> Idmap.add id t table)
         (xfrp_smodule.smodule_in @ xfrp_smodule.smodule_out)
    |> idmap_fold_values
         (fun node table -> Idmap.add node.node_id node.node_type table)
         state.state_nodes
    |> idmap_fold_values
         (fun newnode table ->
           List.fold_left
             (fun table (_, id, t) -> Idmap.add id t table)
             table
             newnode.newnode_binds)
         state.state_newnodes
    |> Idmap.add "state" tstate
  in
  get_free_table all_data node_to_type lifetime
;;

let calc_alloc_amount all_data metainfo =
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
    current, req_amount
  in
  let rec visit_local_const current const req_amount =
    update_req_amount current const.const_body req_amount
  and visit_init current init_expr req_amount =
    match init_expr with
    | Some expr -> update_req_amount current expr req_amount
    | None -> req_amount
  and visit_node_init current node req_amount =
    visit_init current node.node_init req_amount
  and visit_node timestamp free_table node (now, current, req_amount) =
    let req_amount = update_req_amount current node.node_body req_amount in
    let current =
      current |> add_sizeof_type all_data node.node_type |> free_noderef free_table now
    in
    let now = Idmap.find node.node_id timestamp in
    now, current, req_amount
  and visit_newnode timestamp free_table newnode (now, current, req_amount) =
    let req_amount =
      List.fold_right
        (update_req_amount current)
        (List.rev newnode.newnode_margs)
        req_amount
    in
    let current, req_amount =
      List.fold_right
        (fun expr (current, req_amount) ->
          let _, texpr = expr in
          let req_amount = update_req_amount current expr req_amount in
          let current = add_sizeof_type all_data texpr current in
          current, req_amount)
        (List.rev newnode.newnode_inputs)
        (current, req_amount)
    in
    let now = now + 1 in
    let current = free_noderef free_table now current in
    let current, req_amount =
      match newnode.newnode_module with
      | id, ModuleCons (file, _, _, _) ->
        let filedata = Idmap.find file all_data in
        (match Idmap.find id filedata.xfrp_all with
         | XFRPModule m -> visit_module file m (current, req_amount)
         | XFRPSModule sm -> visit_smodule file sm (current, req_amount)
         | _ -> assert false)
      | _ -> assert false
    in
    let now = Idmap.find newnode.newnode_id timestamp in
    now, current, req_amount
  and visit_header_node current (_, init, _) req_amount =
    visit_init current init req_amount
  and visit_module file xfrp_module (current, req_amount) =
    let req_amount =
      req_amount
      |> List.fold_right (visit_header_node current) xfrp_module.module_in
      |> List.fold_right (visit_header_node current) xfrp_module.module_out
      |> idmap_fold_values (visit_local_const current) xfrp_module.module_consts
      |> idmap_fold_values (visit_node_init current) xfrp_module.module_nodes
    in
    let module_info =
      let module_id = xfrp_module.module_id in
      match Hashtbl.find metainfo.moduledata (file, module_id) with
      | ModuleInfo info -> info
      | _ -> assert false
    in
    let lifetime = module_info.module_lifetime in
    let timestamp = lifetime.timestamp in
    let free_table = get_module_free_table all_data xfrp_module lifetime in
    let _, current, req_amount =
      List.fold_left
        (fun (now, current, req_amount) id ->
          match Idmap.find id xfrp_module.module_all with
          | MNode node -> visit_node timestamp free_table node (now, current, req_amount)
          | MNewnode def ->
            visit_newnode timestamp free_table def (now, current, req_amount)
          | _ -> assert false)
        (2, current, req_amount)
        xfrp_module.module_update_ord
    in
    let clockperiod = module_info.module_clockperiod in
    let current = free_noderef free_table clockperiod current in
    current, req_amount
  and visit_state timestamp free_table state (current, req_amount) =
    let req_amount =
      req_amount
      |> idmap_fold_values (visit_local_const current) state.state_consts
      |> idmap_fold_values (visit_node_init current) state.state_nodes
    in
    let _, current, req_amount =
      List.fold_left
        (fun (now, current, req_amount) id ->
          match Idmap.find id state.state_all with
          | SNode node -> visit_node timestamp free_table node (now, current, req_amount)
          | SNewnode def ->
            visit_newnode timestamp free_table def (now, current, req_amount)
          | _ -> assert false)
        (2, current, req_amount)
        state.state_update_ord
    in
    let req_amount = update_req_amount current state.state_switch req_amount in
    let _, tstate = state.state_switch in
    let now = Idmap.find "state" timestamp in
    let current =
      current |> add_sizeof_type all_data tstate |> free_noderef free_table now
    in
    current, req_amount
  and visit_smodule file xfrp_smodule (current, req_amount) =
    let req_amount =
      req_amount
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_in
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_out
      |> List.fold_right (visit_header_node current) xfrp_smodule.smodule_shared
      |> update_req_amount current xfrp_smodule.smodule_init
      |> idmap_fold_values (visit_local_const current) xfrp_smodule.smodule_consts
    in
    let smodule_info =
      let smodule_id = xfrp_smodule.smodule_id in
      match Hashtbl.find metainfo.moduledata (file, smodule_id) with
      | SModuleInfo info -> info
      | _ -> assert false
    in
    let state_lifetime = smodule_info.state_lifetime in
    let clockperiod = smodule_info.smodule_clockperiod in
    idmap_fold_values
      (fun state (next, req_amount) ->
        let lifetime = Idmap.find state.state_id state_lifetime in
        let timestamp = lifetime.timestamp in
        let free_table =
          get_state_free_table all_data xfrp_smodule state.state_id lifetime
        in
        let next', req_amount =
          visit_state timestamp free_table state (current, req_amount)
        in
        let next' = free_noderef free_table clockperiod next' in
        let next = alloc_amount_union next next' in
        next, req_amount)
      xfrp_smodule.smodule_states
      (alloc_amount_empty (), req_amount)
  in
  let current, req_amount =
    List.fold_left
      (fun (current, req_amount) (_, const) ->
        visit_global_const const (current, req_amount))
      (alloc_amount_empty (), alloc_amount_empty ())
      metainfo.all_elements.all_consts
  in
  let entry_file = metainfo.entry_file in
  let entry_filedata = Idmap.find entry_file all_data in
  let current = calc_req_begin all_data entry_file |> alloc_amount_sum current in
  match Idmap.find "Main" entry_filedata.xfrp_all with
  | XFRPModule m ->
    let _, req_amount = visit_module entry_file m (current, req_amount) in
    { metainfo with alloc_amount = req_amount }
  | XFRPSModule sm ->
    let _, req_amount = visit_smodule entry_file sm (current, req_amount) in
    { metainfo with alloc_amount = req_amount }
  | _ -> assert false
;;
