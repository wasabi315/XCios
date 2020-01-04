open Extension.Format
open Syntax
open CodegenUtil
open GenExpr
open MetaInfo

type newnodefun_generator =
  {
    newnodefun_newnode : newnode;
    newnodefun_gen_instance_address : writer;
    newnodefun_gen_instance_name : writer;
    newnodefun_gen_memorytype : writer;
    newnodefun_gen_init : writer;
    newnodefun_gen_bind_address : (nattr * string) printer;
    newnodefun_ctx_param : codegen_ctx;
    newnodefun_ctx_input : codegen_ctx;
  }

let define_newnode_fun metainfo generator fun_writers =
  let newnode = generator.newnodefun_newnode in
  let gen_instance_address = generator.newnodefun_gen_instance_address in
  let gen_instance_name = generator.newnodefun_gen_instance_name in
  let gen_memorytype = generator.newnodefun_gen_memorytype in
  let gen_init = generator.newnodefun_gen_init in
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
        gen_instance_name () pp_print_string param_id
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
        gen_instance_name () pp_print_string input_id
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
      fprintf ppf "static void update_%a" gen_instance_name ()
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
            fprintf ppf "if (%a) {@;<0 2>" gen_init ();
            fprintf ppf "@[<h>param_%a_%a(memory);@]@,"
              gen_instance_name () pp_print_string param_id;
            fprintf ppf "}";
            fprintf ppf "@]"
          in
          let gen_life ppf () =
            fprintf ppf "clock + period"
          in
          let gen_address ppf () =
            (gen_param_address param_id) ppf ()
          in
          let gen_mark_opt =
            get_mark_writer metainfo t gen_address gen_life
          in
          (gen_update gen_body gen_mark_opt None) ppf ()
        in
        (pp_print_list gen_single) ppf params
      in

      let gen_body_input ppf inputs =
        let gen_single ppf (input_id, t, _) =
          let gen_body ppf () =
            fprintf ppf "@[<h>input_%a_%a(memory);@]"
              gen_instance_name () pp_print_string input_id;
          in
          let gen_address ppf () =
            (gen_input_address input_id) ppf ()
          in
          let gen_life ppf () =
            fprintf ppf "clock + 2"
          in
          let gen_mark_opt =
            get_mark_writer metainfo t gen_address gen_life
          in
          (gen_update gen_body gen_mark_opt None) ppf ()
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

