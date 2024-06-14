open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo

let get_newnode_filed newnode_id =
  let len = String.length newnode_id in
  let number_str = String.sub newnode_id 1 (len - 1) in
  sprintf "newnode%s" number_str
;;

let gen_mode_calc pp_loc ppf mode_calc =
  let gen_child_mode_calc ppf (child_module_id, newnode_id, io_node_id) =
    fprintf
      ppf
      "%a(%a)"
      gen_mode_calc_fun_name
      (child_module_id, io_node_id)
      pp_loc
      (get_newnode_filed newnode_id)
  in
  let gen_mode_calc =
    let calcs =
      List.map
        (fun child_calc ppf () -> gen_child_mode_calc ppf child_calc)
        mode_calc.child_modev
    in
    let calc, calcs =
      match mode_calc.self_modev, calcs with
      | None, [] -> assert false
      | None, calc :: calcs -> calc, calcs
      | Some (modev, _), calcs ->
        (fun ppf () -> gen_modev_name ppf (mode_calc.mode_type, modev)), calcs
    in
    List.fold_left (fun ps p ppf () -> fprintf ppf "MAX(%a,@ %a)" p () ps ()) calc calcs
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
        gen_mode_calc_fun_name
        (global_module_id, node_id)
        gen_module_memory_type
        global_module_id
    in
    let gen_prototype ppf () = fprintf ppf "%a;" gen_header () in
    let gen_body ppf () =
      fprintf ppf "@[<v>@[<v 2>if (memory->init) {";
      fprintf
        ppf
        "@,return %a;"
        gen_modev_name
        (mode_calc.mode_type, fst (Option.get mode_calc.init_modev));
      fprintf ppf "@]@,}";
      gen_mode_calc (fun ppf -> fprintf ppf "&memory->%s") ppf mode_calc;
      fprintf ppf "@]"
    in
    let gen_definition ppf () = gen_codeblock gen_header gen_body ppf () in
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
  let define_single node_id mode_calcs fun_writers =
    if Idmap.is_empty mode_calcs
    then fun_writers
    else (
      let mode_type = (snd (Idmap.choose mode_calcs)).mode_type in
      let gen_header ppf () =
        fprintf
          ppf
          "static enum %a %a(%a* memory)"
          gen_mode_name
          mode_type
          gen_mode_calc_fun_name
          (global_module_id, node_id)
          gen_module_memory_type
          global_module_id
      in
      let gen_prototype ppf () = fprintf ppf "%a;" gen_header () in
      let gen_definition ppf () =
        let gen_body ppf () =
          fprintf ppf "@[<v>";
          fprintf ppf "@[<v 2>if (memory->init) {";
          fprintf
            ppf
            "@,return %a;"
            gen_modev_name
            (mode_type, fst (snd (Idmap.find node_id info.smodule_init_modev)));
          fprintf ppf "@]@,}";
          fprintf ppf "@,@[<v 2>switch (memory->state->tag) {";
          Idmap.iter
            (fun state_id mode_calc ->
              fprintf
                ppf
                "@,@[<v 2>case %a: {"
                gen_tstate_tag_val
                ((file, modul.smodule_id), state_id);
              if mode_calc.child_modev <> []
              then (
                fprintf ppf "@,@[<v 2>if (memory->state->fresh) {";
                fprintf
                  ppf
                  "@,return %a;"
                  gen_modev_name
                  (mode_type, fst (Option.get mode_calc.init_modev));
                fprintf ppf "@]@,}");
              gen_mode_calc
                (fun ppf -> fprintf ppf "&memory->statebody.%a.%s" pp_identifier state_id)
                ppf
                mode_calc;
              fprintf ppf "@,break;@]@,}")
            mode_calcs;
          fprintf ppf "@]@,}";
          fprintf ppf "@]"
        in
        gen_codeblock gen_header gen_body ppf ()
      in
      (gen_prototype, gen_definition) :: fun_writers)
  in
  Idmap.fold define_single mode_calcs fun_writers
;;
