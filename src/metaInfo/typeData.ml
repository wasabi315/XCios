open Syntax
open Type
open Dependency
open MetaInfo
open Extension

let calc_typedata all_data file_ord metainfo =

  let visit_tstate typedata file module_name =
    let tstate = TState (file, module_name) in
    let filedata = Idmap.find file all_data in
    let xfrp_smodule = Idmap.find module_name filedata.xfrp_smodules in
    let num_states = Idmap.cardinal xfrp_smodule.smodule_states in
    let () =
      if num_states = 1 then
        Hashset.add typedata.singleton_types tstate
      else ()
    in
    let (tag_table, _) =
      idmap_fold_values (fun state (tag_table, new_tag) ->
          (Idmap.add state.state_id new_tag tag_table, new_tag + 1)
        ) xfrp_smodule.smodule_states (Idmap.empty, 0)
    in
    let param_ids_table =
      idmap_fold_values (fun state table ->
          let (param_ids, _) = List.split state.state_params in
          Idmap.add state.state_id param_ids table
        ) xfrp_smodule.smodule_states Idmap.empty
    in
    Hashtbl.add typedata.cons_tag tstate tag_table;
    Hashtbl.add typedata.tstate_param_ids tstate param_ids_table
  in

  let visit_tid typedata file type_name =
    let tid = TId (file, type_name) in
    let filedata = Idmap.find file all_data in
    let typedef = Idmap.find type_name filedata.xfrp_types in
    let is_enum =
      Idmap.for_all (fun _ tvalue -> tvalue = TUnit) typedef.type_conses
    in
    let () =
      if is_enum then Hashset.add typedata.enum_types tid else ()
    in
    let num_conses = Idmap.cardinal typedef.type_conses in
    let () =
      if num_conses = 1 then Hashset.add typedata.singleton_types tid else ()
    in
    let (tag_table, _) =
      Idmap.fold (fun id _ (tag_table, new_tag) ->
          (Idmap.add id new_tag tag_table, new_tag + 1)
        ) typedef.type_conses (Idmap.empty, 0)
    in
    Hashtbl.add typedata.cons_tag tid tag_table
  in

  let visit_ttuple typedata ts =
    let ttuple = TTuple ts in
    Hashset.add typedata.singleton_types ttuple
  in

  let get_nonenum_tid_defs metainfo =

    let visit_file nonenum_tid_defs file =
      let filedata = Idmap.find file all_data in
      let type_ord = tsort_types filedata.xfrp_types in
      List.fold_left (fun nonenum_tid_defs type_id ->
          let tid = TId (file, type_id) in
          let typedef = Idmap.find type_id filedata.xfrp_types in
          let is_used = Hashtbl.mem metainfo.alloc_amount tid in
          let is_enum = Hashset.mem metainfo.typedata.enum_types tid in
          if is_used && not is_enum then
            (file, typedef) :: nonenum_tid_defs
          else nonenum_tid_defs
        ) nonenum_tid_defs type_ord
    in

    List.fold_left visit_file [] file_ord |> List.rev
  in

  let get_tuple_types metainfo =
    Hashtbl.fold (fun t _ targets ->
        match t with
        | TTuple ts -> ts :: targets
        | TState _ | TId _ -> targets
        | _  -> assert false
      ) metainfo.alloc_amount []
  in

  let get_tstate_defs metainfo =
    List.fold_left (fun targets (file, module_or_smodule) ->
        match module_or_smodule with
        | XFRPModule _ -> targets
        | XFRPSModule sm -> (file, sm) :: targets
        | _ -> assert false
      ) [] metainfo.all_elements.all_modules
    |> List.rev
  in

  let () =
      Hashtbl.iter (fun t _ ->
          match t with
          | TState (file, module_name) ->
             visit_tstate metainfo.typedata file module_name
          | TId (file, type_name) ->
             visit_tid metainfo.typedata file type_name
          | TTuple ts ->
             visit_ttuple metainfo.typedata ts
          | _ -> assert false
        ) metainfo.alloc_amount;
  in
  let nonenum_tid_defs = get_nonenum_tid_defs metainfo in
  let tuple_types = get_tuple_types metainfo in
  let tstate_defs = get_tstate_defs metainfo in
  let typedata =
    {
      metainfo.typedata with nonenum_tid_defs = nonenum_tid_defs;
                             tuple_types = tuple_types;
                             tstate_defs = tstate_defs;
    }
  in
  { metainfo with typedata = typedata }
