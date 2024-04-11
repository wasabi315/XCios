open Extension.Format
open Syntax
open CodegenUtil
open GenExpr
open GenNewnodeFun
open GenStateFun

let define_module_const_fun metainfo file module_id const fun_writers =
  let global_modulename = asprintf "%a" gen_global_modulename (file, module_id) in
  let gen_funname ppf () =
    fprintf ppf "static void init_%s_%s" global_modulename const.const_id
  in
  let gen_memorytype ppf () = gen_module_memory_type ppf (file, module_id) in
  let gen_address ppf () = fprintf ppf "memory->%s" const.const_id in
  let generator =
    { updatefun_ctx = CTXModuleConst
    ; updatefun_body = const.const_body
    ; updatefun_gen_funname = gen_funname
    ; updatefun_gen_memorytype = gen_memorytype
    ; updatefun_gen_address = gen_address
    }
  in
  define_updatefun metainfo generator fun_writers
;;

let define_header_init_fun metainfo file module_id (node_id, init, _) fun_writers =
  match init with
  | None -> fun_writers
  | Some expr ->
    let global_modulename = asprintf "%a" gen_global_modulename (file, module_id) in
    let gen_funname ppf () =
      fprintf ppf "static void header_init_%s_%s" global_modulename node_id
    in
    let gen_memorytype ppf () = gen_module_memory_type ppf (file, module_id) in
    let gen_address ppf () = fprintf ppf "memory->%s[!current_side]" node_id in
    let generator =
      { updatefun_ctx = CTXModuleConst
      ; updatefun_body = expr
      ; updatefun_gen_funname = gen_funname
      ; updatefun_gen_memorytype = gen_memorytype
      ; updatefun_gen_address = gen_address
      }
    in
    define_updatefun metainfo generator fun_writers
;;

let define_module_elem_fun metainfo (file, xfrp_module) fun_writers =
  let module_id = xfrp_module.module_id in
  let global_modulename = asprintf "%a" gen_global_modulename (file, module_id) in
  let gen_memorytype ppf () = gen_module_memory_type ppf (file, module_id) in
  let define_module_node_fun node fun_writers =
    let define_node_init_fun fun_writers =
      match node.node_init with
      | None -> fun_writers
      | Some expr ->
        let gen_funname ppf () =
          fprintf ppf "static void init_%s_%s" global_modulename node.node_id
        in
        let gen_address ppf () =
          gen_module_node_last_address ppf (node.node_attr, node.node_id)
        in
        let generator =
          { updatefun_ctx = CTXModuleConst
          ; updatefun_body = expr
          ; updatefun_gen_funname = gen_funname
          ; updatefun_gen_memorytype = gen_memorytype
          ; updatefun_gen_address = gen_address
          }
        in
        define_updatefun metainfo generator fun_writers
    in
    let define_node_update_fun fun_writers =
      let gen_funname ppf () =
        fprintf ppf "static void update_%s_%s" global_modulename node.node_id
      in
      let gen_address ppf () =
        gen_module_node_curr_address ppf (node.node_attr, node.node_id, node.node_type)
      in
      let generator =
        { updatefun_ctx = CTXModuleNode (node.node_attr, node.node_id)
        ; updatefun_body = node.node_body
        ; updatefun_gen_funname = gen_funname
        ; updatefun_gen_memorytype = gen_memorytype
        ; updatefun_gen_address = gen_address
        }
      in
      define_updatefun metainfo generator fun_writers
    in
    fun_writers |> define_node_init_fun |> define_node_update_fun
  in
  let define_module_newnode_fun newnode fun_writers =
    let instance_id = asprintf "%a" gen_newnode_field newnode in
    let gen_instance_address ppf () = fprintf ppf "memory->%s" instance_id in
    let gen_instance_name ppf () = fprintf ppf "%s_%s" global_modulename instance_id in
    let generator =
      { newnodefun_newnode = newnode
      ; newnodefun_gen_instance_address = gen_instance_address
      ; newnodefun_gen_instance_name = gen_instance_name
      ; newnodefun_gen_memorytype = gen_memorytype
      ; newnodefun_gen_init = gen_module_init
      ; newnodefun_gen_bind_address = gen_module_node_curr_address
      ; newnodefun_ctx_param = CTXModuleConst
      ; newnodefun_ctx_input = CTXModuleNewnodeIn
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
;;

let define_smodule_elem_fun metainfo (file, xfrp_smodule) fun_writers =
  let module_id = xfrp_smodule.smodule_id in
  let global_modulename = asprintf "%a" gen_global_modulename (file, module_id) in
  let define_smodule_state_init_fun fun_writers =
    let gen_funname ppf () =
      fprintf ppf "static void header_init_%s_state" global_modulename
    in
    let gen_memorytype ppf () = gen_module_memory_type ppf (file, module_id) in
    let gen_address ppf () = fprintf ppf "memory->state" in
    let generator =
      { updatefun_ctx = CTXModuleConst
      ; updatefun_body = xfrp_smodule.smodule_init
      ; updatefun_gen_funname = gen_funname
      ; updatefun_gen_memorytype = gen_memorytype
      ; updatefun_gen_address = gen_address
      }
    in
    define_updatefun metainfo generator fun_writers
  in
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
  |> define_smodule_state_init_fun
  |> idmap_fold_values
       (define_module_const_fun metainfo file module_id)
       xfrp_smodule.smodule_consts
  |> idmap_fold_values
       (define_state_fun metainfo file module_id)
       xfrp_smodule.smodule_states
;;
