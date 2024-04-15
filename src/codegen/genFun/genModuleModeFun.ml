open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo

let gen_newnode_field ppf newnode_id =
  let len = String.length newnode_id in
  let number_str = String.sub newnode_id 1 (len - 1) in
  fprintf ppf "newnode%s" number_str
;;

let gen_funname ppf (modul, node_id) =
  fprintf ppf "%a_calc_mode_%a" gen_global_modulename modul pp_identifier node_id
;;

let gen_mode_calc ppf mode_calc =
  let gen_child_mode_calc ppf (child_module_id, newnode_id, io_node_id) =
    fprintf
      ppf
      "%a(&memory->%a)"
      gen_funname
      (child_module_id, io_node_id)
      gen_newnode_field
      newnode_id
  in
  let gen_mode_calc =
    let gen_self ppf () =
      fprintf
        ppf
        "%a::%a"
        gen_mode_name
        mode_calc.mode_type
        pp_identifier
        mode_calc.self_modev
    in
    List.fold_right
      (fun child_mode_calc printer ppf () ->
        fprintf ppf "MAX(%a,@ %a)" gen_child_mode_calc child_mode_calc printer ())
      mode_calc.child_modev
      gen_self
  in
  fprintf ppf "@,@[<hov>return %a;@]" gen_mode_calc ()
;;

let define_module_mode_calc_fun metainfo (file, modul) fun_writers =
  let global_module_id = file, modul.module_id in
  let info =
    match Hashtbl.find metainfo.moduledata global_module_id with
    | ModuleInfo info -> info
    | _ -> assert false
  in
  let define_single node_id mode_calc fun_writers =
    let gen_header ppf () =
      fprintf
        ppf
        "static enum %a %a(%a* memory)"
        gen_mode_name
        mode_calc.mode_type
        gen_funname
        (global_module_id, node_id)
        gen_module_memory_type
        global_module_id
    in
    let gen_prototype ppf () = fprintf ppf "%a;" gen_header () in
    let gen_definition ppf () =
      gen_codeblock gen_header (fun ppf () -> gen_mode_calc ppf mode_calc) ppf ()
    in
    (gen_prototype, gen_definition) :: fun_writers
  in
  Idmap.fold define_single info.module_mode_calc fun_writers
;;

let define_smodule_mode_calc_fun metainfo (file, modul) fun_writers =
  let global_module_id = file, modul.smodule_id in
  let info =
    match Hashtbl.find metainfo.moduledata global_module_id with
    | SModuleInfo info -> info
    | _ -> assert false
  in
  let tstate = Type.TState (file, modul.smodule_id) in
  let tag_table = Hashtbl.find metainfo.typedata.cons_tag tstate in
  (* transposing nested maps *)
  let mode_calcs =
    Idmap.fold
      (fun state_id mode_calcs acc ->
        Idmap.fold
          (fun node_id mode_calc acc ->
            let table =
              match Idmap.find_opt node_id acc with
              | Some table -> table
              | None -> Idmap.empty
            in
            let table = Idmap.add state_id mode_calc table in
            Idmap.add node_id table acc)
          mode_calcs
          acc)
      info.state_mode_calc
      Idmap.empty
  in
  printf "%a" (pp_idmap (pp_idmap pp_mode_calc)) mode_calcs;
  let define_single node_id mode_calcs fun_writers =
    if Idmap.is_empty mode_calcs
    then fun_writers
    else (
      let gen_header ppf () =
        fprintf
          ppf
          "static enum %a %a(%a* memory)"
          gen_mode_name
          (snd (Idmap.choose mode_calcs)).mode_type
          gen_funname
          (global_module_id, node_id)
          gen_module_memory_type
          global_module_id
      in
      let gen_prototype ppf () = fprintf ppf "%a;" gen_header () in
      let gen_definition ppf () =
        let init_state_id =
          match modul.smodule_init with
          | EVariant ((id, _), _), _ -> id
          | _ -> assert false
        in
        let init_mode_calc = Idmap.find init_state_id mode_calcs in
        let gen_body ppf () =
          fprintf ppf "@[<v>";
          fprintf ppf "@[<v 2>if (memory->init) {";
          gen_mode_calc ppf init_mode_calc;
          fprintf ppf "@]@,}";
          Idmap.iter
            (fun state_id mode_calc ->
              fprintf
                ppf
                "@,@[<v 2>if (memory->state->tag == %d) {"
                (Idmap.find state_id tag_table);
              gen_mode_calc ppf mode_calc;
              fprintf ppf "@]@,}")
            mode_calcs;
          fprintf ppf "@]"
        in
        gen_codeblock gen_header gen_body ppf ()
      in
      (gen_prototype, gen_definition) :: fun_writers)
  in
  Idmap.fold define_single mode_calcs fun_writers
;;
