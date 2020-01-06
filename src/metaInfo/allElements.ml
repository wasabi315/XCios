open Syntax
open Dependency
open MetaInfo

let get_all_elements all_data file_ord used_materials metainfo =

  let all_modules =

     let visit_file all_modules file =
       let filedata = Idmap.find file all_data in
       let module_ord =
         tsort_modules filedata.xfrp_modules filedata.xfrp_smodules
       in
       List.fold_left (fun all_modules module_id ->
           match Idmap.find module_id filedata.xfrp_all with
           | XFRPModule m ->
              let global_name = conc_id [file; "module" ;module_id] in
              if Idset.mem global_name used_materials then
                (file, XFRPModule m) :: all_modules
              else all_modules
           | XFRPSModule sm ->
              let global_name = conc_id [file; "smodule" ;module_id] in
              if Idset.mem global_name used_materials then
                (file, XFRPSModule sm) :: all_modules
              else all_modules
           | _ -> assert false
         ) all_modules module_ord
     in

     List.fold_left visit_file [] file_ord |> List.rev
  in

  let (all_consts, all_funs) =

    let visit_file (all_consts, all_funs) file =
      let filedata = Idmap.find file all_data in
      let material_ord =
        tsort_materials filedata.xfrp_consts filedata.xfrp_funs
      in
      List.fold_left (fun (all_consts, all_funs) material_id ->
          match Idmap.find material_id filedata.xfrp_all with
          | XFRPConst c ->
             let global_name = conc_id [file; "const" ;material_id] in
             if Idset.mem global_name used_materials then
               ((file, c) :: all_consts, all_funs)
             else (all_consts, all_funs)
          | XFRPFun f ->
             let global_name = conc_id [file; "fun" ;material_id] in
             if Idset.mem global_name used_materials then
               (all_consts, (file, f) :: all_funs)
             else (all_consts, all_funs)
          | _ -> assert false
        ) (all_consts, all_funs) material_ord
    in

    let (all_consts, all_funs) =
      List.fold_left visit_file ([], []) file_ord
    in
    let all_consts = List.rev all_consts in
    let all_funs = List.rev all_funs in
    (all_consts, all_funs)
  in

  let all_elements =
    {
      all_modules = all_modules;
      all_consts = all_consts;
      all_funs = all_funs;
    }
  in
  { metainfo with all_elements = all_elements }
