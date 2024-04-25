open Extension
open Extension.Format
open Syntax
open CodegenUtil
open MetaInfo

let gen_hook_name ppf (node_id, mode_id, from, to_) =
  fprintf
    ppf
    "hook_%a_%a_to_%a"
    pp_identifier
    node_id
    gen_modev_name
    (mode_id, from)
    gen_modev_name
    (mode_id, to_)
;;

let define_refresh_mark_fun metainfo fun_writers =
  let gen_funname ppf () = fprintf ppf "static void refresh_mark" in
  let gen_prototype ppf () = fprintf ppf "%a();" gen_funname () in
  let gen_definition ppf () =
    let gen_head ppf () = fprintf ppf "%a()" gen_funname () in
    let gen_body_loop ppf typename =
      let memory_var = conc_id [ "memory"; typename ] in
      let size_var = conc_id [ "size"; typename ] in
      fprintf ppf "@[<v>";
      fprintf ppf "for (i = 0; i < %s; ++i) {@;<0 2>" size_var;
      fprintf ppf "@[<v>";
      fprintf ppf "if (%s[i].mark < period) %s[i].mark = 0;" memory_var memory_var;
      fprintf ppf "@,else %s[i].mark -= period;" memory_var;
      fprintf ppf "@]@,";
      fprintf ppf "}";
      fprintf ppf "@]"
    in
    let gen_body_loop_tid ppf (file, typedef) =
      let typename = asprintf "%a" gen_tid_typename (file, typedef.type_id) in
      gen_body_loop ppf typename
    in
    let gen_body_loop_ttuple ppf types =
      let typename = asprintf "%a" gen_ttuple_typename types in
      gen_body_loop ppf typename
    in
    let gen_body_loop_tstate ppf (file, xfrp_smodule) =
      let typename = asprintf "%a" gen_tstate_typename (file, xfrp_smodule.smodule_id) in
      gen_body_loop ppf typename
    in
    let gen_body ppf () =
      let nonenum_tid_defs = metainfo.typedata.nonenum_tid_defs in
      let tuple_types = metainfo.typedata.tuple_types in
      let tstate_defs = metainfo.typedata.tstate_defs in
      fprintf ppf "@[<v>";
      fprintf ppf "int i;";
      if nonenum_tid_defs = []
      then ()
      else fprintf ppf "@,%a" (pp_print_list gen_body_loop_tid) nonenum_tid_defs;
      if tuple_types = []
      then ()
      else fprintf ppf "@,%a" (pp_print_list gen_body_loop_ttuple) tuple_types;
      if tstate_defs = []
      then ()
      else fprintf ppf "@,%a" (pp_print_list gen_body_loop_tstate) tstate_defs;
      fprintf ppf "@]"
    in
    (gen_codeblock gen_head gen_body) ppf ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;

let add_extern_prototype metainfo prototype_writers =
  let _, in_sig, out_sig =
    let entry_file = metainfo.entry_file in
    get_module_sig metainfo entry_file "Main"
  in
  let gen_input_prototype (id, t) ppf () =
    fprintf
      ppf
      "@[<h>extern %a input_%a();@]"
      (gen_value_type metainfo)
      t
      pp_identifier
      id
  in
  let gen_output_prototype (id, t) ppf () =
    fprintf
      ppf
      "@[<h>extern void output_%a(%a);@]"
      pp_identifier
      id
      (gen_value_type metainfo)
      t
  in
  let gen_hook_prototypes = function
    | id, Type.TMode (file, mode_id, _) ->
      let global_mode_id = file, mode_id in
      let _, modedef =
        List.find
          (fun (file', def) -> file = file' && def.mode_id = mode_id)
          metainfo.typedata.modes
      in
      let all_transitions = List.pairs (modedef.mode_vals @ modedef.mode_acc_vals) in
      all_transitions
      |> List.map (fun (from, to_) ppf () ->
        fprintf
          ppf
          "@[<h>extern void %a();@]"
          gen_hook_name
          (id, global_mode_id, from, to_))
    | _ -> []
  in
  prototype_writers
  |> List.append (List.map gen_input_prototype in_sig)
  |> List.append (List.map gen_output_prototype out_sig)
  |> List.append (List.concat_map gen_hook_prototypes (in_sig @ out_sig))
;;

let gen_activate_fun ppf metainfo =
  let entry_file = metainfo.entry_file in
  let all_consts = metainfo.all_elements.all_consts in
  let param_sig, in_sig, out_sig = get_module_sig metainfo entry_file "Main" in
  let gen_head_arg ppf () =
    (pp_print_list
       (fun ppf (id, t) ->
         fprintf ppf "%a %a" (gen_value_type metainfo) t pp_print_string id)
       ~pp_sep:pp_print_commaspace)
      ppf
      param_sig
  in
  let gen_head ppf () = fprintf ppf "void activate(@[<h>%a@])" gen_head_arg () in
  let gen_body_const_init ppf (file, const) =
    let global_name = asprintf "%a" gen_global_constname (file, const.const_id) in
    let gen_body ppf () = fprintf ppf "init_%s();" global_name in
    let gen_address ppf () = pp_print_string ppf global_name in
    let gen_life ppf () = fprintf ppf "clock + period" in
    let gen_mark_opt = get_mark_writer metainfo const.const_type gen_address gen_life in
    (gen_update gen_body gen_mark_opt None) ppf ()
  in
  let const_remark_writers =
    List.fold_left
      (fun writers (file, const) ->
        let gen_address ppf () = gen_global_constname ppf (file, const.const_id) in
        let gen_life ppf () = fprintf ppf "clock + period" in
        let gen_mark_opt =
          get_mark_writer metainfo const.const_type gen_address gen_life
        in
        match gen_mark_opt with
        | Some writer -> writer :: writers
        | None -> writers)
      []
      all_consts
    |> List.rev
  in
  let gen_io_node_init ppf io_sig =
    let gen_single = function
      | id, Type.TMode (file, mode_id, _) ->
        let _, modedef =
          List.find
            (fun (file', def) -> file = file' && def.mode_id = mode_id)
            metainfo.typedata.modes
        in
        let smallest_modev =
          match modedef.mode_vals @ modedef.mode_acc_vals with
          | [] -> assert false
          | modev :: _ -> modev
        in
        fprintf
          ppf
          "@,%a.mode[!current_side] = %a;"
          pp_identifier
          id
          gen_modev_name
          ((file, mode_id), smallest_modev);
        fprintf ppf "@,memory.%a = &%a;" pp_identifier id pp_identifier id
      | _ -> ()
    in
    List.iter gen_single io_sig
  in
  let gen_mode_calc ppf io_sig =
    let gen_single = function
      | id, Type.TMode _ ->
        fprintf
          ppf
          "@,%a.mode[current_side] = %a(&memory);"
          pp_identifier
          id
          gen_mode_calc_fun_name
          ((entry_file, "Main"), id)
      | _ -> ()
    in
    List.iter gen_single io_sig
  in
  let gen_hook_calls ppf io_sig =
    let gen_single = function
      | id, Type.TMode (file, mode_id, _) ->
        let global_mode_id = file, mode_id in
        let _, modedef =
          List.find
            (fun (file', def) -> file = file' && def.mode_id = mode_id)
            metainfo.typedata.modes
        in
        let all_transitions = List.pairs (modedef.mode_vals @ modedef.mode_acc_vals) in
        all_transitions
        |> List.iter (fun (from, to_) ->
          fprintf
            ppf
            "@,@[<v 2>if (%a.mode[!current_side] == %a && %a.mode[current_side] == %a) {"
            pp_identifier
            id
            gen_modev_name
            (global_mode_id, from)
            pp_identifier
            id
            gen_modev_name
            (global_mode_id, to_);
          fprintf ppf "@,%a();" gen_hook_name (id, global_mode_id, from, to_);
          fprintf ppf "@]@,}")
      | _ -> ()
    in
    List.iter gen_single io_sig
  in
  let gen_body_input ppf () =
    let gen_single = function
      | id, Type.TMode (file, mode, _) ->
        fprintf
          ppf
          "@,if (%a_is_accessible(%a.mode[current_side])) {@;<0 2>"
          gen_mode_name
          (file, mode)
          pp_identifier
          id;
        fprintf ppf "%a.value = input_%a();@," pp_identifier id pp_identifier id;
        fprintf ppf "}"
      | id, _ ->
        fprintf
          ppf
          "@,memory.%a[current_side] = input_%a();"
          pp_identifier
          id
          pp_identifier
          id
    in
    List.iter gen_single in_sig
  in
  let gen_body_output ppf () =
    let gen_single = function
      | id, Type.TMode (file, mode, _) ->
        fprintf
          ppf
          "@,if (%a_is_accessible(%a.mode[current_side])) {@;<0 2>"
          gen_mode_name
          (file, mode)
          pp_identifier
          id;
        fprintf ppf "output_%a(%a.value);@," pp_identifier id pp_identifier id;
        fprintf ppf "}"
      | id, _ ->
        fprintf
          ppf
          "@,output_%a(memory.%a[current_side]);"
          pp_identifier
          id
          pp_identifier
          id
    in
    List.iter gen_single out_sig
  in
  let io_sig = in_sig @ out_sig in
  let gen_body_loop ppf () =
    fprintf ppf "clock = 0;";
    if const_remark_writers = []
    then ()
    else fprintf ppf "@,%a" (exec_all_writers ()) const_remark_writers;
    fprintf ppf "@,clock = 1;";
    gen_mode_calc ppf io_sig;
    gen_hook_calls ppf io_sig;
    fprintf ppf "%a" gen_body_input ();
    fprintf ppf "@,update_%a(&memory);" gen_global_modulename (entry_file, "Main");
    fprintf ppf "%a" gen_body_output ();
    fprintf ppf "@,clock = period;";
    fprintf ppf "@,refresh_mark();";
    fprintf ppf "@,current_side = !current_side;";
    fprintf ppf "@]"
  in
  let gen_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "current_side = 0;";
    fprintf ppf "@,clock = 0;";
    if param_sig = []
    then ()
    else (
      let gen_sig_init ppf (id, _) = fprintf ppf "memory->%s = %s;" id id in
      fprintf ppf "@,%a" (pp_print_list gen_sig_init) param_sig);
    if all_consts = []
    then ()
    else fprintf ppf "@,%a" (pp_print_list gen_body_const_init) all_consts;
    gen_io_node_init ppf io_sig;
    fprintf ppf "@,memory.init = 1;";
    fprintf ppf "@,while (1) {@;<0 2>";
    fprintf ppf "@[<v>%a@]@," gen_body_loop ();
    fprintf ppf "}";
    fprintf ppf "@]"
  in
  (gen_codeblock gen_head gen_body) ppf ()
;;
