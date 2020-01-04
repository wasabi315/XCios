open Extension.Format
open Syntax
open CodegenUtil
open GenExpr
open GenNewnodeFun

let define_state_fun metainfo file module_id state fun_writers =
  let state_id = state.state_id in
  let global_statename =
    asprintf "%a" gen_global_statename (file, module_id, state_id)
  in

  let gen_memorytype ppf () =
    gen_module_memory_type ppf (file, module_id)
  in

  let define_state_const_fun const fun_writers =

    let gen_funname ppf () =
      fprintf ppf "static void init_%s_%s"
        global_statename const.const_id
    in

    let gen_address ppf () =
      fprintf ppf "memory->statebody.%s.%s" state_id const.const_id
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
             (gen_state_node_address state_id) (node.node_attr, node.node_id)
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
          (gen_state_node_address state_id) (node.node_attr, node.node_id)
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
    let gen_instance_name ppf () =
      fprintf ppf "%s_%s" global_statename instance_id
    in
    let generator =
      {
        newnodefun_newnode = newnode;
        newnodefun_gen_instance_address = gen_instance_address;
        newnodefun_gen_instance_name = gen_instance_name;
        newnodefun_gen_memorytype = gen_memorytype;
        newnodefun_gen_init = gen_state_init state_id;
        newnodefun_gen_bind_address = gen_state_node_address state_id;
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
