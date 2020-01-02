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
    fundef_ctx : codegen_ctx;
    body_expr : expression;
    gen_funname : writer;
    gen_memorytype : writer;
    gen_address : writer;
  }

let define_updatefun metainfo generator fun_writers =
  let fundef_ctx = generator.fundef_ctx in
  let body_expr = generator.body_expr in
  let gen_funname = generator.gen_funname in
  let gen_memorytype = generator.gen_memorytype in
  let gen_address = generator.gen_address in
  let (body_writers, gen_expr) =
    get_expr_generator metainfo fundef_ctx body_expr
  in

  let gen_prototype ppf () =
    fprintf ppf "%a(%a);"
      gen_funname () gen_memorytype ()
  in

  let gen_body_lastline ppf () =
    fprintf ppf "@[<2>%a =@ @[%a@];@]" gen_address () gen_expr ()
  in

  let gen_definition ppf () =
    gen_codeblock
      (fun ppf () ->
        fprintf ppf "%a(@[<h>%a memory@])"
          gen_funname () gen_memorytype ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf ()
  in

  (gen_prototype, gen_definition) :: fun_writers

let define_state_fun metainfo file module_id state fun_writers =
  let state_id = state.state_id in
  let global_statename =
    asprintf "%a" gen_global_statename (file, module_id, state_id)
  in

  let define_state_const_fun const fun_writers =

    let gen_funname ppf () =
      fprintf ppf "static void init_%s_%s"
        global_statename const.const_id
    in

    let gen_memorytype ppf () =
      gen_module_memory_type ppf (file, module_id)
    in

    let gen_address ppf () =
      fprintf ppf "memory->%s" const.const_id
    in

    let generator =
      {
        fundef_ctx = CTXStateConst state_id;
        body_expr = const.const_body;
        gen_funname = gen_funname;
        gen_memorytype = gen_memorytype;
        gen_address = gen_address;
      }
    in
    define_updatefun metainfo generator fun_writers
  in

  let define_state_node_fun node fun_writers =

    let gen_memorytype ppf () =
      gen_module_memory_type ppf (file, module_id)
    in

    let gen_node_address ppf () =
      match node.node_attr with
      | InputNode -> assert false
      | SharedNode | OutputNode ->
         fprintf ppf "memory->%s" node.node_id
      | NormalNode ->
         fprintf ppf "memory->statebody.%s.%s"
           state_id node.node_id
    in

    let define_node_init_fun fun_writers =
      match node.node_init with
      | None -> fun_writers
      | Some expr ->
         let gen_funname ppf () =
           fprintf ppf "static void init_%s_%s"
             global_statename node.node_id
         in
         let gen_address ppf () =
           fprintf ppf "%a[!current_side]" gen_node_address ()
         in
         let generator =
           {
             fundef_ctx = CTXStateConst state_id;
             body_expr = expr;
             gen_funname = gen_funname;
             gen_memorytype = gen_memorytype;
             gen_address = gen_address;
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
        fprintf ppf "%a[current_side]" gen_node_address ()
      in
      let ctx = CTXStateNode (state_id, node.node_attr, node.node_id) in
      let generator =
        {
          fundef_ctx = ctx;
          body_expr = node.node_body;
          gen_funname = gen_funname;
          gen_memorytype = gen_memorytype;
          gen_address = gen_address;
        }
      in
      define_updatefun metainfo generator fun_writers
    in

    fun_writers |> define_node_init_fun |> define_node_update_fun
  in

  fun_writers
  |> idmap_fold_values define_state_const_fun state.state_consts
  |> idmap_fold_values define_state_node_fun state.state_nodes

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
      fundef_ctx = CTXModuleConst;
      body_expr = const.const_body;
      gen_funname = gen_funname;
      gen_memorytype = gen_memorytype;
      gen_address = gen_address;
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
         fundef_ctx = CTXModuleConst;
         body_expr = expr;
         gen_funname = gen_funname;
         gen_memorytype = gen_memorytype;
         gen_address = gen_address;
       }
     in
     define_updatefun metainfo generator fun_writers

let define_module_node_fun metainfo file module_id node fun_writers =
  let global_modulename =
    asprintf "%a" gen_global_modulename (file, module_id)
  in

  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, module_id)
  in

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
           fundef_ctx = CTXModuleConst;
           body_expr = expr;
           gen_funname = gen_funname;
           gen_memorytype = gen_memorytype;
           gen_address = gen_address;
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
        fundef_ctx = CTXModuleNode (node.node_attr, node.node_id);
        body_expr = node.node_body;
        gen_funname = gen_funname;
        gen_memorytype = gen_memorytype;
        gen_address = gen_address;
      }
    in
    define_updatefun metainfo generator fun_writers
  in

  fun_writers |> define_node_init_fun |> define_node_update_fun


let define_module_fun metainfo file xfrp_module fun_writers =
  let module_id = xfrp_module.module_id in
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
  |> idmap_fold_values
       (define_module_node_fun metainfo file module_id)
       xfrp_module.module_nodes

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
