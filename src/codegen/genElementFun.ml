open Extension.Format
open Syntax
open CodegenUtil
open GenExpr
open MetaInfo

let gen_body_expr body_writers gen_lastline ppf () =
  fprintf ppf "@[<v>";
  if body_writers = [] then () else
    fprintf ppf "%a@," (exec_all_writers ()) body_writers;
  fprintf ppf "%a" gen_lastline ();
  fprintf ppf "@]"

let define_global_const_fun metainfo (file, constdef) fun_writers =
  let constname =
    asprintf "%a" gen_global_constname (file, constdef.const_id)
  in

  let gen_funname ppf () =
    fprintf ppf "static void init_%s" constname
  in

  let gen_prototype ppf () =
    fprintf ppf "%a();" gen_funname ()
  in

  let gen_definition ppf () =
    let codegen_ctx = CTXGlobalConst in
    let (body_writers, gen_expr) =
      get_expr_generator metainfo codegen_ctx constdef.const_body
    in
    let gen_body_lastline ppf () =
      fprintf ppf "@[<hv 2>%a =@ @[%a@];@]"
        pp_print_string constname gen_expr ()
    in
    gen_codeblock
      (fun ppf () ->
        fprintf ppf "%a()" gen_funname ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf ()
  in

  (gen_prototype, gen_definition) :: fun_writers

let define_global_fun metainfo (file, fundef) fun_writers =

  let gen_funname ppf () =
    fprintf ppf "static %a %a"
      (gen_value_type metainfo) fundef.fun_rettype
      gen_global_funname (file, fundef.fun_id)
  in

  let gen_prototype ppf () =
    let param_printer =
      pp_print_list (gen_value_type metainfo) ~pp_sep:pp_print_commaspace
    in
    let (_, paramtypes) = List.split fundef.fun_params in
    fprintf ppf "%a(@[<h>%a@])"
      gen_funname () param_printer paramtypes
  in

  let gen_definition_params ppf () =
    (pp_print_list (fun ppf (id, t) ->
         fprintf ppf "@[<h>%a %a@]"
           (gen_value_type metainfo) t pp_print_string id
       ) ~pp_sep:pp_print_commaspace) ppf fundef.fun_params
  in

  let gen_definition ppf () =
    let codegen_ctx = CTXGlobalConst in
    let (body_writers, gen_expr) =
      get_expr_generator metainfo codegen_ctx fundef.fun_body
    in
    let gen_body_lastline ppf () =
      fprintf ppf "@[<h>return @[%a@];@]" gen_expr ()
    in
    gen_codeblock
      (fun ppf () ->
        fprintf ppf "%a(@[<h>%a@])"
          gen_funname () gen_definition_params ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf ()
  in

  (gen_prototype, gen_definition) :: fun_writers

type updatefun_generator =
  {
    updatefun_ctx : codegen_ctx;
    updatefun_body : expression;
    updatefun_gen_funname : writer;
    updatefun_gen_memorytype : writer;
    updatefun_gen_address : writer;
  }

let define_updatefun metainfo generator fun_writers =
  let fundef_ctx = generator.updatefun_ctx in
  let body_expr = generator.updatefun_body in
  let gen_funname = generator.updatefun_gen_funname in
  let gen_memorytype = generator.updatefun_gen_memorytype in
  let gen_address = generator.updatefun_gen_address in
  let (body_writers, gen_expr) =
    get_expr_generator metainfo fundef_ctx body_expr
  in

  let gen_prototype ppf () =
    fprintf ppf "%a(%a*);"
      gen_funname () gen_memorytype ()
  in

  let gen_body_lastline ppf () =
    fprintf ppf "@[<2>%a =@ @[%a@];@]" gen_address () gen_expr ()
  in

  let gen_definition ppf () =
    gen_codeblock
      (fun ppf () ->
        fprintf ppf "%a(@[<h>%a* memory@])"
          gen_funname () gen_memorytype ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf ()
  in

  (gen_prototype, gen_definition) :: fun_writers

type newnodefun_generator =
  {
    newnodefun_newnode : newnode;
    newnodefun_gen_instance_address : writer;
    newnodefun_gen_globalname : writer;
    newnodefun_gen_memorytype : writer;
    newnodefun_gen_bind_address : (nattr * string) printer;
    newnodefun_ctx_param : codegen_ctx;
    newnodefun_ctx_input : codegen_ctx;
  }

let define_newnode_fun metainfo generator fun_writers =
  let newnode = generator.newnodefun_newnode in
  let gen_instance_address = generator.newnodefun_gen_instance_address in
  let gen_globalname = generator.newnodefun_gen_globalname in
  let gen_memorytype = generator.newnodefun_gen_memorytype in
  let gen_bind_address = generator.newnodefun_gen_bind_address in
  let ctx_param = generator.newnodefun_ctx_param in
  let ctx_input = generator.newnodefun_ctx_input in
  let (file, module_id) =
    match newnode.newnode_module with
    | (module_id, ModuleCons(file, _, _, _)) -> (file, module_id)
    | _ -> assert false
  in
  let (param_sig, in_sig, out_sig) =
    match Hashtbl.find metainfo.moduledata (file, module_id) with
    | ModuleInfo info ->
       (info.module_param_sig, info.module_in_sig, info.module_out_sig)
    | SModuleInfo info ->
       (info.smodule_param_sig, info.smodule_in_sig, info.smodule_out_sig)
  in
  let params =
    List.map2 (fun (id, t) expr -> (id, t, expr))
      param_sig newnode.newnode_margs
  in
  let inputs =
    List.map2 (fun (id, t) expr -> (id, t, expr))
      in_sig newnode.newnode_inputs
  in
  let outputs =
    List.map2 (fun (from_id, _) (attr, to_id, t) ->
        (from_id, attr, to_id, t)
      ) out_sig newnode.newnode_binds
  in

  let gen_param_address param_id ppf () =
    fprintf ppf "%a.%a"
      gen_instance_address () pp_print_string param_id
  in

  let gen_input_address input_id ppf () =
    fprintf ppf "%a.%a[current_side]"
      gen_instance_address () pp_print_string input_id
  in

  let define_param_fun (param_id, _, expr) fun_writers =
    let gen_funname ppf () =
      fprintf ppf "static void param_%a_%a"
        gen_globalname () pp_print_string param_id
    in
    let generator =
      {
        updatefun_ctx = ctx_param;
        updatefun_body = expr;
        updatefun_gen_funname = gen_funname;
        updatefun_gen_memorytype = gen_memorytype;
        updatefun_gen_address = gen_param_address param_id;
      }
    in
    define_updatefun metainfo generator fun_writers
  in

  let define_input_fun (input_id, _, expr) fun_writers =
    let gen_funname ppf () =
      fprintf ppf "static void input_%a_%a"
        gen_globalname () pp_print_string input_id
    in
    let generator =
      {
        updatefun_ctx = ctx_input;
        updatefun_body = expr;
        updatefun_gen_funname = gen_funname;
        updatefun_gen_memorytype = gen_memorytype;
        updatefun_gen_address = gen_input_address input_id;
      }
    in
    define_updatefun metainfo generator fun_writers
  in

  let define_updatefun fun_writers =
    let gen_funname ppf () =
      fprintf ppf "static void update_%a" gen_globalname ()
    in

    let gen_prototype ppf () =
      fprintf ppf "%a(%a*);" gen_funname () gen_memorytype ()
    in

    let gen_definition ppf () =
      let gen_head ppf () =
        fprintf ppf "%a(%a* memory)" gen_funname () gen_memorytype()
      in

      let gen_body_param ppf params =
        let gen_single ppf (param_id, t, _) =
          let gen_body ppf () =
            fprintf ppf "@[<v>";
            fprintf ppf "if (memory->init) {@;<0 2>";
            fprintf ppf "@[<h>param_%a_%a(memory);@]@,"
              gen_globalname () pp_print_string param_id;
            fprintf ppf "}";
            fprintf ppf "@]"
          in
          let gen_mark ppf () =
            fprintf ppf "clock + period"
          in
          let generator =
            {
              update_gen_body = gen_body;
              update_target_type = t;
              update_gen_address = gen_param_address param_id;
              update_gen_mark = gen_mark;
              update_gen_clock = None;
            }
          in
          (gen_update metainfo generator) ppf ()
        in
        (pp_print_list gen_single) ppf params
      in

      let gen_body_input ppf inputs =
        let gen_single ppf (input_id, t, _) =
          let gen_body ppf () =
            fprintf ppf "@[<h>input_%a_%a(memory);@]"
              gen_globalname () pp_print_string input_id;
          in
          let gen_mark ppf () =
            fprintf ppf "clock + 2"
          in
          let generator =
            {
              update_gen_body = gen_body;
              update_target_type = t;
              update_gen_address = gen_input_address input_id;
              update_gen_mark = gen_mark;
              update_gen_clock = None;
            }
          in
          (gen_update metainfo generator) ppf ()
        in
        (pp_print_list gen_single) ppf inputs
      in

      let gen_body_output ppf outputs =
        let gen_single ppf (from_id, nattr, to_id, _) =
          fprintf ppf "%a[current_side] = %a.%a[current_side];"
            gen_bind_address (nattr, to_id)
            gen_instance_address ()
            pp_print_string from_id
        in
        (pp_print_list gen_single) ppf outputs
      in

      let gen_body ppf () =
        fprintf ppf "@[<v>";
        if params = [] then () else
          fprintf ppf "%a@," gen_body_param params;
        if inputs = [] then () else
          fprintf ppf "%a@," gen_body_input inputs;
        fprintf ppf "update_%a(&(%a));"
          gen_global_modulename (file, module_id)
          gen_instance_address ();
        if outputs = [] then () else
          fprintf ppf "@,%a" gen_body_output outputs;
        fprintf ppf "@]"
      in

      (gen_codeblock gen_head gen_body) ppf ()
    in

    (gen_prototype, gen_definition) :: fun_writers
  in

  fun_writers
  |> List.fold_right define_param_fun (List.rev params)
  |> List.fold_right define_input_fun (List.rev inputs)
  |> define_updatefun

let define_state_fun metainfo file module_id state fun_writers =
  let state_id = state.state_id in
  let global_statename =
    asprintf "%a" gen_global_statename (file, module_id, state_id)
  in

  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, module_id)
  in

  let gen_node_address ppf (nattr, node_id) =
    match nattr with
    | InputNode -> assert false
    | SharedNode | OutputNode ->
       fprintf ppf "memory->%s" node_id
    | NormalNode ->
       fprintf ppf "memory->statebody.%s.%s"
         state_id node_id
  in

  let define_state_const_fun const fun_writers =

    let gen_funname ppf () =
      fprintf ppf "static void init_%s_%s"
        global_statename const.const_id
    in

    let gen_address ppf () =
      fprintf ppf "memory->%s" const.const_id
    in

    let generator =
      {
        updatefun_ctx = CTXStateConst state_id;
        updatefun_body = const.const_body;
        updatefun_gen_funname = gen_funname;
        updatefun_gen_memorytype = gen_memorytype;
        updatefun_gen_address = gen_address;
      }
    in
    define_updatefun metainfo generator fun_writers
  in

  let define_state_node_fun node fun_writers =

    let define_node_init_fun fun_writers =
      match node.node_init with
      | None -> fun_writers
      | Some expr ->
         let gen_funname ppf () =
           fprintf ppf "static void init_%s_%s"
             global_statename node.node_id
         in
         let gen_address ppf () =
           fprintf ppf "%a[!current_side]"
             gen_node_address (node.node_attr, node.node_id)
         in
         let generator =
           {
             updatefun_ctx = CTXStateConst state_id;
             updatefun_body = expr;
             updatefun_gen_funname = gen_funname;
             updatefun_gen_memorytype = gen_memorytype;
             updatefun_gen_address = gen_address;
           }
         in
         define_updatefun metainfo generator fun_writers
    in

    let define_node_update_fun fun_writers =
      let gen_funname ppf () =
        fprintf ppf "static void update_%s_%s"
          global_statename node.node_id
      in
      let gen_address ppf () =
        fprintf ppf "%a[current_side]"
          gen_node_address (node.node_attr, node.node_id)
      in
      let ctx = CTXStateNode (state_id, node.node_attr, node.node_id) in
      let generator =
        {
          updatefun_ctx = ctx;
          updatefun_body = node.node_body;
          updatefun_gen_funname = gen_funname;
          updatefun_gen_memorytype = gen_memorytype;
          updatefun_gen_address = gen_address;
        }
      in
      define_updatefun metainfo generator fun_writers
    in

    fun_writers |> define_node_init_fun |> define_node_update_fun
  in

  let define_state_newnode_fun newnode fun_writers =
    let instance_id = asprintf "%a" gen_newnode_field newnode in
    let gen_instance_address ppf () =
      fprintf ppf "memory->statebody.%s.%s" state_id instance_id
    in
    let gen_globalname ppf () =
      fprintf ppf "%s_%s" global_statename instance_id
    in
    let generator =
      {
        newnodefun_newnode = newnode;
        newnodefun_gen_instance_address = gen_instance_address;
        newnodefun_gen_globalname = gen_globalname;
        newnodefun_gen_memorytype = gen_memorytype;
        newnodefun_gen_bind_address = gen_node_address;
        newnodefun_ctx_param = CTXStateConst state_id;
        newnodefun_ctx_input = CTXStateNewnodeIn state_id;
      }
    in
    define_newnode_fun metainfo generator fun_writers
  in

  fun_writers
  |> idmap_fold_values define_state_const_fun state.state_consts
  |> idmap_fold_values define_state_node_fun state.state_nodes
  |> idmap_fold_values define_state_newnode_fun state.state_newnodes

let define_module_const_fun metainfo file module_id const fun_writers =
  let global_modulename =
    asprintf "%a" gen_global_modulename (file, module_id)
  in

  let gen_funname ppf () =
    fprintf ppf "static void init_%s_%s"
      global_modulename const.const_id
  in

  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, module_id)
  in

  let gen_address ppf () =
    fprintf ppf "memory->%s" const.const_id
  in

  let generator =
    {
      updatefun_ctx = CTXModuleConst;
      updatefun_body = const.const_body;
      updatefun_gen_funname = gen_funname;
      updatefun_gen_memorytype = gen_memorytype;
      updatefun_gen_address = gen_address;
    }
  in
  define_updatefun metainfo generator fun_writers

let define_header_init_fun metainfo file module_id (node_id, init, _) fun_writers =
  match init with
  | None -> fun_writers
  | Some expr ->
     let global_modulename =
       asprintf "%a" gen_global_modulename (file, module_id)
     in

     let gen_funname ppf () =
       fprintf ppf "static void header_init_%s_%s"
         global_modulename node_id
     in

     let gen_memorytype ppf () =
       gen_module_memory_type ppf (file, module_id)
     in

     let gen_address ppf () =
       fprintf ppf "memory->%s[!current_side]" node_id
     in

     let generator =
       {
         updatefun_ctx = CTXModuleConst;
         updatefun_body = expr;
         updatefun_gen_funname = gen_funname;
         updatefun_gen_memorytype = gen_memorytype;
         updatefun_gen_address = gen_address;
       }
     in
     define_updatefun metainfo generator fun_writers

let define_module_fun metainfo file xfrp_module fun_writers =
  let module_id = xfrp_module.module_id in
  let global_modulename =
    asprintf "%a" gen_global_modulename (file, module_id)
  in

  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, module_id)
  in

  let define_module_node_fun node fun_writers =

    let define_node_init_fun fun_writers =
      match node.node_init with
      | None -> fun_writers
      | Some expr ->
         let gen_funname ppf () =
           fprintf ppf "static void init_%s_%s"
             global_modulename node.node_id
         in
         let gen_address ppf () =
           fprintf ppf "memory->%s[!current_side]" node.node_id
         in
         let generator =
           {
             updatefun_ctx = CTXModuleConst;
             updatefun_body = expr;
             updatefun_gen_funname = gen_funname;
             updatefun_gen_memorytype = gen_memorytype;
             updatefun_gen_address = gen_address;
           }
         in
         define_updatefun metainfo generator fun_writers
    in

    let define_node_update_fun fun_writers =
      let gen_funname ppf () =
        fprintf ppf "static void update_%s_%s"
          global_modulename node.node_id
      in
      let gen_address ppf () =
        fprintf ppf "memory->%s[current_side]" node.node_id
      in
      let generator =
        {
          updatefun_ctx = CTXModuleNode (node.node_attr, node.node_id);
          updatefun_body = node.node_body;
          updatefun_gen_funname = gen_funname;
          updatefun_gen_memorytype = gen_memorytype;
          updatefun_gen_address = gen_address;
        }
      in
      define_updatefun metainfo generator fun_writers
    in

    fun_writers |> define_node_init_fun |> define_node_update_fun
  in

  let define_module_newnode_fun newnode fun_writers =
    let instance_id = asprintf "%a" gen_newnode_field newnode in
    let gen_instance_address ppf () =
      fprintf ppf "memory->%s" instance_id
    in
    let gen_globalname ppf () =
      fprintf ppf "%s_%s" global_modulename instance_id
    in
    let gen_bind_address ppf (_, node_id) =
      fprintf ppf "memory->%s" node_id
    in
    let generator =
      {
        newnodefun_newnode = newnode;
        newnodefun_gen_instance_address = gen_instance_address;
        newnodefun_gen_globalname = gen_globalname;
        newnodefun_gen_memorytype = gen_memorytype;
        newnodefun_gen_bind_address = gen_bind_address;
        newnodefun_ctx_param = CTXModuleConst;
        newnodefun_ctx_input = CTXModuleNewnodeIn;
      }
    in
    define_newnode_fun metainfo generator fun_writers
  in

  fun_writers
  |> List.fold_right
       (define_header_init_fun metainfo file module_id)
       (List.rev xfrp_module.module_in)
  |> List.fold_right
       (define_header_init_fun metainfo file module_id)
       (List.rev xfrp_module.module_out)
  |> idmap_fold_values
       (define_module_const_fun metainfo file module_id)
       xfrp_module.module_consts
  |> idmap_fold_values define_module_node_fun xfrp_module.module_nodes
  |> idmap_fold_values define_module_newnode_fun xfrp_module.module_newnodes

let define_smoule_fun metainfo file xfrp_smodule fun_writers =
  let module_id = xfrp_smodule.smodule_id in
  fun_writers
  |> List.fold_right
       (define_header_init_fun metainfo file module_id)
       (List.rev xfrp_smodule.smodule_in)
  |> List.fold_right
       (define_header_init_fun metainfo file module_id)
       (List.rev xfrp_smodule.smodule_out)
  |> List.fold_right
       (define_header_init_fun metainfo file module_id)
       (List.rev xfrp_smodule.smodule_shared)
  |> idmap_fold_values
       (define_module_const_fun metainfo file module_id)
       xfrp_smodule.smodule_consts
  |> idmap_fold_values
       (define_state_fun metainfo file module_id)
       xfrp_smodule.smodule_states

let define_element_fun metainfo fun_writers =
  let all_consts = metainfo.all_elements.all_consts in
  let all_funs = metainfo.all_elements.all_funs in
  let all_modules = metainfo.all_elements.all_modules in
  fun_writers
  |> List.fold_right
       (define_global_const_fun metainfo)
       (List.rev all_consts)
  |> List.fold_right
       (define_global_fun metainfo)
       (List.rev all_funs)
  |> List.fold_right (fun (file, module_or_smodule) fun_writers ->
         match module_or_smodule with
         | XFRPModule m ->
            define_module_fun metainfo file m fun_writers
         | XFRPSModule sm ->
            define_smoule_fun metainfo file sm fun_writers
         | _ -> assert false
       ) (List.rev all_modules)
