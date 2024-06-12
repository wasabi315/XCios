open Extension.Format
open Syntax
open Type
open CodegenUtil
open MetaInfo

let gen_newnode_field' ppf newnode_id =
  let len = String.length newnode_id in
  let number_str = String.sub newnode_id 1 (len - 1) in
  fprintf ppf "newnode%s" number_str
;;

let gen_life_node_current lifetime node_id ppf () =
  match Idmap.find node_id lifetime.free_current with
  | Some clock -> fprintf ppf "entry + %d" clock
  | None -> fprintf ppf "entry + 1 + period"
;;

let gen_iterbody_const metainfo gen_prefix gen_address gen_init ppf const =
  let const_id = const.const_id in
  let const_type = const.const_type in
  let gen_update_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "if (%a) {@;<0 2>" gen_init ();
    fprintf ppf "@[<h>init_%a_%a(memory);@]@," gen_prefix () pp_print_string const_id;
    fprintf ppf "}";
    fprintf ppf "@]"
  in
  let gen_address ppf () = gen_address ppf const in
  let gen_life ppf () = fprintf ppf "clock + period" in
  let gen_mark_opt = get_mark_writer metainfo const_type gen_address gen_life in
  (gen_update gen_update_body gen_mark_opt None) ppf ()
;;

let gen_iterbody_module_const metainfo file module_id ppf const =
  let gen_prefix ppf () = gen_global_modulename ppf (file, module_id) in
  let gen_address ppf const = fprintf ppf "memory->%s" const.const_id in
  let gen_init ppf () = fprintf ppf "memory->init" in
  gen_iterbody_const metainfo gen_prefix gen_address gen_init ppf const
;;

let gen_iterbody_state_const metainfo file module_id state_id ppf const =
  let gen_prefix ppf () = gen_global_statename ppf (file, module_id, state_id) in
  let gen_address ppf const =
    fprintf ppf "memory->statebody.%s.%s" state_id const.const_id
  in
  let gen_init ppf () = fprintf ppf "memory->statebody.%s.init" state_id in
  gen_iterbody_const metainfo gen_prefix gen_address gen_init ppf const
;;

let gen_iterbody_header_init metainfo file module_id ppf (node_id, node_type) =
  let gen_prefix ppf () = gen_global_modulename ppf (file, module_id) in
  let gen_update_body ppf () =
    fprintf ppf "@[<h>header_init_%a_%a(memory);@]" gen_prefix () pp_print_string node_id
  in
  let gen_address ppf () = fprintf ppf "memory->%s[!current_side]" node_id in
  let gen_life ppf () = fprintf ppf "entry + 2" in
  let gen_mark_opt = get_mark_writer metainfo node_type gen_address gen_life in
  fprintf ppf "@[<v>";
  fprintf ppf "if (memory->init) {@;<0 2>";
  fprintf ppf "@[<v>%a@]@," (gen_update gen_update_body gen_mark_opt None) ();
  fprintf ppf "}";
  fprintf ppf "@]"
;;

type iterbody_genereator =
  { iterbody_lifetime : lifetime
  ; iterbody_gen_prefix : writer
  ; iterbody_gen_init : writer
  ; iterbody_gen_node_curr_address : (nattr * string * Type.t) printer
  ; iterbody_gen_node_last_address : (nattr * string) printer
  }

let get_module_iterbody_generator metainfo file module_id =
  let lifetime =
    let module_info =
      match Hashtbl.find metainfo.moduledata (file, module_id) with
      | ModuleInfo info -> info
      | _ -> assert false
    in
    module_info.module_lifetime
  in
  let gen_prefix ppf () = gen_global_modulename ppf (file, module_id) in
  { iterbody_lifetime = lifetime
  ; iterbody_gen_prefix = gen_prefix
  ; iterbody_gen_init = gen_module_init
  ; iterbody_gen_node_curr_address = gen_module_node_curr_address
  ; iterbody_gen_node_last_address = gen_module_node_last_address
  }
;;

let get_state_iterbody_generator metainfo file module_id state_id =
  let lifetime =
    let smodule_info =
      match Hashtbl.find metainfo.moduledata (file, module_id) with
      | SModuleInfo info -> info
      | _ -> assert false
    in
    Idmap.find state_id smodule_info.state_lifetime
  in
  let gen_prefix ppf () = gen_global_statename ppf (file, module_id, state_id) in
  { iterbody_lifetime = lifetime
  ; iterbody_gen_prefix = gen_prefix
  ; iterbody_gen_init = gen_state_init state_id
  ; iterbody_gen_node_curr_address = gen_state_node_curr_address state_id
  ; iterbody_gen_node_last_address = gen_state_node_last_address state_id
  }
;;

let gen_iterbody_initlast metainfo generator ppf node =
  let node_attr = node.node_attr in
  let node_id = node.node_id in
  let node_type = node.node_type in
  let lifetime = generator.iterbody_lifetime in
  let gen_prefix = generator.iterbody_gen_prefix in
  let gen_init = generator.iterbody_gen_init in
  let gen_node_last_address = generator.iterbody_gen_node_last_address in
  let gen_update_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "if (%a) {@;<0 2>" gen_init ();
    fprintf ppf "@[<h>init_%a_%a(memory);@]@," gen_prefix () pp_print_string node_id;
    fprintf ppf "}";
    fprintf ppf "@]"
  in
  let gen_address ppf () = gen_node_last_address ppf (node_attr, node_id) in
  let gen_life ppf () =
    fprintf ppf "entry + %d" (Idmap.find node_id lifetime.free_last)
  in
  let gen_mark_opt = get_mark_writer metainfo node_type gen_address gen_life in
  (gen_update gen_update_body gen_mark_opt None) ppf ()
;;

let gen_module_iterbody_initlast metainfo file module_id ppf node =
  let generator = get_module_iterbody_generator metainfo file module_id in
  (gen_iterbody_initlast metainfo generator) ppf node
;;

let gen_state_iterbody_initlast metainfo file module_id state_id ppf node =
  let generator = get_state_iterbody_generator metainfo file module_id state_id in
  (gen_iterbody_initlast metainfo generator) ppf node
;;

let gen_iterbody_node metainfo generator ppf node =
  let node_attr = node.node_attr in
  let node_id = node.node_id in
  let node_type = node.node_type in
  let lifetime = generator.iterbody_lifetime in
  let gen_prefix = generator.iterbody_gen_prefix in
  let gen_node_curr_address = generator.iterbody_gen_node_curr_address in
  let gen_update_body ppf () =
    fprintf ppf "update_%a_%a(memory);" gen_prefix () pp_print_string node_id
  in
  let gen_address ppf () = gen_node_curr_address ppf (node_attr, node_id, node_type) in
  let gen_life = gen_life_node_current lifetime node_id in
  let gen_mark_opt =
    match node_type, get_mark_writer metainfo node_type gen_address gen_life with
    | TMode (file, mode_id, _), Some writer ->
      let writer ppf () =
        let gen_head ppf () =
          fprintf
            ppf
            "if (%a_is_accessible(memory->%s->mode[current_side]))"
            gen_mode_name
            (file, mode_id)
            node_id
        in
        gen_codeblock gen_head writer ppf ()
      in
      Some writer
    | _, writer -> writer
  in
  let gen_tick ppf () =
    fprintf ppf "clock = entry + %d;" (Idmap.find node_id lifetime.timestamp)
  in
  (gen_update gen_update_body gen_mark_opt (Some gen_tick)) ppf ()
;;

let gen_module_iterbody_node metainfo file module_id ppf node =
  let generator = get_module_iterbody_generator metainfo file module_id in
  (gen_iterbody_node metainfo generator) ppf node
;;

let gen_state_iterbody_node metainfo file module_id state_id ppf node =
  let generator = get_state_iterbody_generator metainfo file module_id state_id in
  (gen_iterbody_node metainfo generator) ppf node
;;

let gen_iterbody_newnode metainfo generator ppf newnode =
  let lifetime = generator.iterbody_lifetime in
  let gen_prefix = generator.iterbody_gen_prefix in
  let gen_node_curr_address = generator.iterbody_gen_node_curr_address in
  let gen_update_body ppf () =
    fprintf ppf "update_%a_%a(memory);" gen_prefix () gen_newnode_field newnode
  in
  let get_bind_mark_writer (nattr, node_id, t) =
    let gen_address ppf () = gen_node_curr_address ppf (nattr, node_id, t) in
    let gen_life = gen_life_node_current lifetime node_id in
    match t, get_mark_writer metainfo t gen_address gen_life with
    | TMode (file, mode_id, _), Some writer ->
      let writer ppf () =
        let gen_head ppf () =
          fprintf
            ppf
            "if (%a_is_accessible(memory->%s->mode[current_side]))"
            gen_mode_name
            (file, mode_id)
            node_id
        in
        gen_codeblock gen_head writer ppf ()
      in
      Some writer
    | _, writer -> writer
  in
  let gen_marks =
    List.fold_left
      (fun writers -> function
        | nattr, (NBDef node_id | NBPass node_id), t ->
          let mark_writer = get_bind_mark_writer (nattr, node_id, t) in
          (match mark_writer with
           | Some writer -> writer :: writers
           | None -> writers))
      []
      newnode.newnode_binds
    |> List.rev
  in
  let gen_mark_opt =
    match gen_marks with
    | [] -> None
    | writers ->
      let gen_mark ppf () = exec_all_writers () ppf writers in
      Some gen_mark
  in
  let gen_tick ppf () =
    fprintf ppf "clock = entry + %d;" (Idmap.find newnode.newnode_id lifetime.timestamp)
  in
  (gen_update gen_update_body gen_mark_opt (Some gen_tick)) ppf ()
;;

let gen_module_iterbody_newnode metainfo file module_id ppf newnode =
  let generator = get_module_iterbody_generator metainfo file module_id in
  (gen_iterbody_newnode metainfo generator) ppf newnode
;;

let gen_state_iterbody_newnode metainfo file module_id state_id ppf newnode =
  let generator = get_state_iterbody_generator metainfo file module_id state_id in
  (gen_iterbody_newnode metainfo generator) ppf newnode
;;

let get_init_header_nodes header_nodes =
  List.fold_left
    (fun ids (id, init, t) ->
      match init with
      | Some _ -> (id, t) :: ids
      | None -> ids)
    []
    header_nodes
  |> List.rev
;;

let get_init_nodedefs nodes =
  idmap_fold_values
    (fun node ids ->
      match node.node_init with
      | Some _ -> node :: ids
      | None -> ids)
    nodes
    []
;;

let get_input_remark_writers metainfo lifetime input_nodes =
  List.fold_left
    (fun writers (node_id, _, node_type) ->
      let gen_address ppf () =
        match node_type with
        | TMode _ -> fprintf ppf "memory->%s->value" node_id
        | _ -> fprintf ppf "memory->%s[current_side]" node_id
      in
      let gen_life ppf () = gen_life_node_current lifetime node_id ppf () in
      let mark_writer_opt =
        match node_type, get_mark_writer metainfo node_type gen_address gen_life with
        | Type.TMode (file, mode_id, _), Some writer ->
          let writer ppf () =
            let gen_head ppf () =
              fprintf
                ppf
                "if (%a_is_accessible(memory->%s->mode[current_side]))"
                gen_mode_name
                (file, mode_id)
                node_id
            in
            gen_codeblock gen_head writer ppf ()
          in
          Some writer
        | _, writer -> writer
      in
      match mark_writer_opt with
      | Some writer -> writer :: writers
      | None -> writers)
    []
    input_nodes
  |> List.rev
;;

let get_init_remark_writers metainfo lifetime init_header_nodes init_nodedefs =
  let remove_ids =
    init_nodedefs |> List.map (fun node -> node.node_id) |> Idset.of_list
  in
  let remark_nodes =
    List.filter (fun (id, _) -> not (Idset.mem id remove_ids)) init_header_nodes
  in
  List.fold_left
    (fun writers (node_id, node_type) ->
      let gen_address ppf () = fprintf ppf "memory->%s[!current_side]" node_id in
      let gen_life ppf () =
        fprintf ppf "entry + %d" (Idmap.find node_id lifetime.free_last)
      in
      let mark_writer_opt = get_mark_writer metainfo node_type gen_address gen_life in
      match mark_writer_opt with
      | Some writer -> writer :: writers
      | None -> writers)
    []
    remark_nodes
  |> List.rev
;;

let gen_body_module_newnode_io_init metainfo file module_id ppf =
  let modeinfo =
    match Hashtbl.find metainfo.moduledata (file, module_id) with
    | ModuleInfo info -> info.module_mode_calc
    | _ -> assert false
  in
  if not (Idmap.for_all (fun _ modeinfo -> modeinfo.child_modev = []) modeinfo)
  then (
    fprintf ppf "@,@[<v>";
    fprintf ppf "@[<v 2>if (memory->init) {";
    modeinfo
    |> Idmap.iter (fun io_node_id modeinfo ->
      modeinfo.child_modev
      |> List.iter (fun (_, newnode_id, io_node_id') ->
        fprintf
          ppf
          "@,memory->%a.%a = memory->%a;"
          gen_newnode_field'
          newnode_id
          pp_identifier
          io_node_id'
          pp_identifier
          io_node_id));
    fprintf ppf "@]@,}";
    fprintf ppf "@]")
;;

let define_module_update_fun metainfo (file, xfrp_module) fun_writers =
  let module_id = xfrp_module.module_id in
  let gen_funname ppf () =
    fprintf ppf "static void update_%a" gen_global_modulename (file, module_id)
  in
  let gen_prototype ppf () =
    fprintf ppf "%a(%a*);" gen_funname () gen_module_memory_type (file, module_id)
  in
  let gen_definition ppf () =
    let gen_head ppf () =
      fprintf ppf "%a(%a* memory)" gen_funname () gen_module_memory_type (file, module_id)
    in
    let consts = idmap_value_list xfrp_module.module_consts in
    let header_nodes = xfrp_module.module_in @ xfrp_module.module_out in
    let init_header_nodes = get_init_header_nodes header_nodes in
    let module_nodes = xfrp_module.module_nodes in
    let init_nodedefs = get_init_nodedefs module_nodes in
    let lifetime =
      let module_info =
        match Hashtbl.find metainfo.moduledata (file, module_id) with
        | ModuleInfo info -> info
        | _ -> assert false
      in
      module_info.module_lifetime
    in
    let input_remark_writers =
      get_input_remark_writers metainfo lifetime xfrp_module.module_in
    in
    let init_remark_writers =
      get_init_remark_writers metainfo lifetime init_header_nodes init_nodedefs
    in
    let gen_body_const ppf consts =
      let gen_iterbody_const = gen_iterbody_module_const metainfo file module_id in
      (pp_print_list gen_iterbody_const) ppf consts
    in
    let gen_body_header_init ppf init_header_nodes =
      let gen_iterbody_header_init = gen_iterbody_header_init metainfo file module_id in
      (pp_print_list gen_iterbody_header_init) ppf init_header_nodes
    in
    let gen_body_init_last ppf init_nodedefs =
      let gen_iterbody_initlast = gen_module_iterbody_initlast metainfo file module_id in
      (pp_print_list gen_iterbody_initlast) ppf init_nodedefs
    in
    let gen_body_main ppf () =
      let gen_iterbody_node = gen_module_iterbody_node metainfo file module_id in
      let gen_iterbody_newnode = gen_module_iterbody_newnode metainfo file module_id in
      let gen_single ppf id =
        match Idmap.find id xfrp_module.module_all with
        | MNode node -> gen_iterbody_node ppf node
        | MNewnode newnode -> gen_iterbody_newnode ppf newnode
        | _ -> assert false
      in
      (pp_print_list gen_single) ppf xfrp_module.module_update_ord
    in
    let gen_body ppf () =
      fprintf ppf "@[<v>";
      fprintf ppf "int entry = clock;";
      gen_body_module_newnode_io_init metainfo file module_id ppf;
      if consts = [] then () else fprintf ppf "@,%a" gen_body_const consts;
      if init_header_nodes = []
      then ()
      else fprintf ppf "@,%a" gen_body_header_init init_header_nodes;
      fprintf ppf "@,clock = entry + 1;";
      if input_remark_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) input_remark_writers;
      if init_remark_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) init_remark_writers;
      if init_nodedefs = []
      then ()
      else fprintf ppf "@,%a" gen_body_init_last init_nodedefs;
      fprintf ppf "@,clock = entry + 2;";
      fprintf ppf "@,%a" gen_body_main ();
      fprintf ppf "@,memory->init = 0;";
      fprintf ppf "@]"
    in
    (gen_codeblock gen_head gen_body) ppf ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;

let gen_body_state_newnode_io_init metainfo file module_id state_id ppf =
  let modeinfo =
    match Hashtbl.find metainfo.moduledata (file, module_id) with
    | SModuleInfo info -> Idmap.find state_id info.state_mode_calc
    | _ -> assert false
  in
  if not (Idmap.for_all (fun _ modeinfo -> modeinfo.child_modev = []) modeinfo)
  then (
    fprintf ppf "@,@[<v>";
    fprintf ppf "@[<v 2>if (memory->statebody.%a.init) {" pp_identifier state_id;
    modeinfo
    |> Idmap.iter (fun io_node_id modeinfo ->
      modeinfo.child_modev
      |> List.iter (fun (_, newnode_id, io_node_id') ->
        fprintf
          ppf
          "@,memory->statebody.%a.%a.%a = memory->%a;"
          pp_identifier
          state_id
          gen_newnode_field'
          newnode_id
          pp_identifier
          io_node_id'
          pp_identifier
          io_node_id));
    fprintf ppf "@]@,}";
    fprintf ppf "@]")
;;

let define_smodule_update_fun metainfo (file, xfrp_smodule) fun_writers =
  let module_id = xfrp_smodule.smodule_id in
  let gen_funname ppf () =
    fprintf ppf "static void update_%a" gen_global_modulename (file, module_id)
  in
  let gen_prototype ppf () =
    fprintf ppf "%a(%a*);" gen_funname () gen_module_memory_type (file, module_id)
  in
  let gen_definition ppf () =
    let gen_head ppf () =
      fprintf ppf "%a(%a* memory)" gen_funname () gen_module_memory_type (file, module_id)
    in
    let tstate = TState (file, module_id) in
    let module_consts = idmap_value_list xfrp_smodule.smodule_consts in
    let header_nodes =
      xfrp_smodule.smodule_in @ xfrp_smodule.smodule_out @ xfrp_smodule.smodule_shared
    in
    let init_header_nodes = get_init_header_nodes header_nodes in
    let states = idmap_value_list xfrp_smodule.smodule_states in
    let gen_body_module_const ppf consts =
      let gen_iterbody_const = gen_iterbody_module_const metainfo file module_id in
      (pp_print_list gen_iterbody_const) ppf consts
    in
    let gen_body_header_init ppf init_header_nodes =
      let gen_iterbody_header_init = gen_iterbody_header_init metainfo file module_id in
      (pp_print_list gen_iterbody_header_init) ppf init_header_nodes
    in
    let gen_body_header_init_state ppf () =
      let gen_update_body ppf () =
        fprintf
          ppf
          "@[<h>header_init_%a_state(memory);@]"
          gen_global_modulename
          (file, module_id)
      in
      let gen_address ppf () = fprintf ppf "memory->state" in
      let gen_life ppf () = fprintf ppf "entry + 2" in
      let gen_mark_opt = get_mark_writer metainfo tstate gen_address gen_life in
      fprintf ppf "@[<v>";
      fprintf ppf "if (memory->init) {@;<0 2>";
      fprintf ppf "@[<v>%a@]@," (gen_update gen_update_body gen_mark_opt None) ();
      fprintf ppf "}";
      fprintf ppf "@]"
    in
    let gen_body_state ppf state =
      let state_id = state.state_id in
      let state_consts = idmap_value_list state.state_consts in
      let state_nodes = state.state_nodes in
      let init_nodedefs = get_init_nodedefs state_nodes in
      let lifetime =
        let smodule_info =
          match Hashtbl.find metainfo.moduledata (file, module_id) with
          | SModuleInfo info -> info
          | _ -> assert false
        in
        Idmap.find state_id smodule_info.state_lifetime
      in
      let input_remark_writers =
        get_input_remark_writers metainfo lifetime xfrp_smodule.smodule_in
      in
      let init_remark_writers =
        get_init_remark_writers metainfo lifetime init_header_nodes init_nodedefs
      in
      let gen_state_body_state_const ppf state_consts =
        let gen_iterbody_const =
          gen_iterbody_state_const metainfo file module_id state_id
        in
        (pp_print_list gen_iterbody_const) ppf state_consts
      in
      let gen_state_body_state_remark ppf () =
        let life = Idmap.find "state" lifetime.free_last in
        let gen_address ppf () = fprintf ppf "memory->state" in
        let gen_life ppf () = fprintf ppf "entry + %d" life in
        match get_mark_writer metainfo tstate gen_address gen_life with
        | Some writer -> writer ppf ()
        | None -> assert false
      in
      let gen_state_body_init_last ppf init_nodedefs =
        let gen_iterbody_initlast =
          gen_state_iterbody_initlast metainfo file module_id state_id
        in
        (pp_print_list gen_iterbody_initlast) ppf init_nodedefs
      in
      let gen_state_body_main ppf () =
        let gen_iterbody_node =
          gen_state_iterbody_node metainfo file module_id state_id
        in
        let gen_iterbody_newnode =
          gen_state_iterbody_newnode metainfo file module_id state_id
        in
        let gen_single ppf id =
          match Idmap.find id state.state_all with
          | SNode node -> gen_iterbody_node ppf node
          | SNewnode newnode -> gen_iterbody_newnode ppf newnode
          | _ -> assert false
        in
        (pp_print_list gen_single) ppf state.state_update_ord
      in
      let gen_state_body_switch ppf () =
        let gen_update_body ppf () =
          fprintf
            ppf
            "update_%a_state(memory);"
            gen_global_statename
            (file, module_id, state_id)
        in
        let gen_address ppf () = fprintf ppf "memory->state" in
        let gen_life ppf () = fprintf ppf "entry + clock + 1" in
        let gen_mark_opt = get_mark_writer metainfo tstate gen_address gen_life in
        let gen_tick ppf () =
          fprintf ppf "clock = entry + %d;" (Idmap.find "state" lifetime.timestamp)
        in
        (gen_update gen_update_body gen_mark_opt (Some gen_tick)) ppf ()
      in
      let gen_state_body_submodule_free ppf newnode =
        match newnode.newnode_module with
        | module_id, ModuleCons (file, _, _, _) ->
          fprintf
            ppf
            "free_%a(&(memory->statebody.%a.%a));"
            gen_global_modulename
            (file, module_id)
            pp_print_string
            state_id
            gen_newnode_field
            newnode
        | _ -> assert false
      in
      fprintf ppf "@[<v>";
      fprintf ppf "if (memory->state->fresh) {@;<0 2>";
      fprintf ppf "memory->statebody.%s.init = 1;@," state_id;
      fprintf ppf "}";
      fprintf ppf "@,memory->state->fresh = 0;";
      gen_body_state_newnode_io_init metainfo file module_id state_id ppf;
      if input_remark_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) input_remark_writers;
      if init_remark_writers = []
      then ()
      else fprintf ppf "@,%a" (exec_all_writers ()) init_remark_writers;
      fprintf ppf "@,%a" gen_state_body_state_remark ();
      if state_consts = []
      then ()
      else fprintf ppf "@,%a" gen_state_body_state_const state_consts;
      if init_nodedefs = []
      then ()
      else fprintf ppf "@,%a" gen_state_body_init_last init_nodedefs;
      fprintf ppf "@,clock = entry + 2;";
      fprintf ppf "@,%a" gen_state_body_main ();
      fprintf ppf "@,%a" gen_state_body_switch ();
      fprintf ppf "@,memory->statebody.%s.init = 0;" state_id;
      if Idmap.is_empty state.state_newnodes
      then ()
      else (
        let newnodes = idmap_value_list state.state_newnodes in
        fprintf ppf "@,if (memory->state->fresh) {@;<0 2>";
        fprintf ppf "@[<v>%a@]@," (pp_print_list gen_state_body_submodule_free) newnodes;
        fprintf ppf "}");
      fprintf ppf "@]"
    in
    let gen_body_state_branch ppf () =
      match states with
      | [] -> assert false
      | [ state ] -> gen_body_state ppf state
      | states ->
        fprintf ppf "@[<v 2>switch (memory->state->tag) {";
        List.iter
          (fun state ->
            fprintf
              ppf
              "@,@[<v 2>case %a: {@,"
              gen_tstate_tag_val
              ((file, module_id), state.state_id);
            fprintf ppf "@[<v>%a@]" gen_body_state state;
            fprintf ppf "@,break;@]@,}")
          states;
        fprintf ppf "@]@,}"
    in
    let gen_body ppf () =
      fprintf ppf "@[<v>";
      fprintf ppf "int entry = clock;";
      if module_consts = []
      then ()
      else fprintf ppf "@,%a" gen_body_module_const module_consts;
      if init_header_nodes = []
      then ()
      else fprintf ppf "@,%a" gen_body_header_init init_header_nodes;
      fprintf ppf "@,%a" gen_body_header_init_state ();
      fprintf ppf "@,clock = entry + 1;";
      fprintf ppf "@,%a" gen_body_state_branch ();
      fprintf ppf "@,memory->init = 0;";
      fprintf ppf "@]"
    in
    (gen_codeblock gen_head gen_body) ppf ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;
