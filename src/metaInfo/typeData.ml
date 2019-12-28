open Syntax
open Type
open MetaInfo
open Extension

let calc_typedata all_data metainfo =
   
  let visit_tstate typedata file module_name =
    let tstate = TState (file, module_name) in
    let filedata = Idmap.find file all_data in
    let xfrp_smodule = Idmap.find module_name filedata.xfrp_smodules in
    let is_enum =
      Idmap.for_all (fun _ state ->
          state.state_params = []
        ) xfrp_smodule.smodule_states
    in
    let () =
      if is_enum then Hashset.add typedata.enum_types tstate else ()
    in
    let num_states = Idmap.cardinal xfrp_smodule.smodule_states in
    let () = 
      if num_states = 1 then
        Hashset.add typedata.singleton_types tstate
      else ()
    in
    let (id_table, _) =
      idmap_fold_values (fun state (id_table, new_id) ->
          (Idmap.add state.state_id new_id id_table, new_id + 1)
        ) xfrp_smodule.smodule_states (Idmap.empty, 0)
    in
    Hashtbl.add typedata.cons_id tstate id_table
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
    let (id_table, _) = 
      Idmap.fold (fun id _ (id_table, new_id) ->
          (Idmap.add id new_id id_table, new_id + 1)
        ) typedef.type_conses (Idmap.empty, 0)
    in
    Hashtbl.add typedata.cons_id tid id_table
  in
    
  let visit_ttuple typedata ts =
    let ttuple = TTuple ts in
    Hashset.add typedata.singleton_types ttuple
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
      ) metainfo.alloc_amount
  in
  metainfo
    
