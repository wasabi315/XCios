open Extension
open Extension.Format
open Syntax
open Type
open CodegenUtil
open MetaInfo

let gen_consdef_body gen_core typename ppf () =
  let memory_var = conc_id ["memory"; typename] in
  let counter_var = conc_id ["counter"; typename] in
  let size_var = conc_id ["size"; typename] in

  let gen_alloc_loop_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "%s++;" counter_var;
    fprintf ppf "@,%s %%= %s;" counter_var size_var;
    fprintf ppf "@,%a"
      (gen_codeblock
         (fun ppf () ->
           fprintf ppf "@[<h>if (%s[%s].mark < clock)@]" memory_var counter_var)
         (fun ppf () ->
           fprintf ppf "@[<h>x = %s + %s; break;@]" memory_var counter_var))
      ();
    fprintf ppf "@]"
  in

  fprintf ppf "@[<v>";
  fprintf ppf "struct %s* x;" typename;
  fprintf ppf "@,%a"
    (gen_codeblock
       (fun ppf () -> fprintf ppf "@[<h>while (1)@]")
       gen_alloc_loop_body)
    ();
  fprintf ppf "@,x->mark = 0;";
  fprintf ppf "@,%a" gen_core ();
  fprintf ppf "@,return x;";
  fprintf ppf "@]"

let define_tid_conses metainfo (file, typedef) fun_writers =
  let type_id = typedef.type_id in
  let tid = TId (file, type_id) in

  let define_single_cons cons_id vtype fun_writers =

    let gen_funname ppf () =
      fprintf ppf "static %a %a"
        (gen_value_type metainfo) tid
        gen_tid_consname (file, type_id, cons_id)
    in

    let gen_prototype ppf () =
      let gen_prototype_params ppf () =
        if vtype = TUnit then () else (gen_value_type metainfo) ppf vtype
      in
      fprintf ppf "@[<h>%a(%a);@]"
        gen_funname () gen_prototype_params ()
    in

    let gen_definition_head ppf () =
      let gen_definition_params ppf () =
        if vtype = TUnit then () else
          fprintf ppf "%a value" (gen_value_type metainfo) vtype
      in
      fprintf ppf "@[<h>%a(%a)@]"
        gen_funname () gen_definition_params ()
    in

    let gen_definition_body_core ppf () =
      let typedata = metainfo.typedata in
      let is_singleton = Hashset.mem typedata.singleton_types tid in
      let writers = [] in
      let writers =
        if is_singleton then writers else
          begin
            let tag =
              Hashtbl.find typedata.cons_tag tid |> Idmap.find cons_id
            in
            let writer ppf () =
              fprintf ppf "x->tag = %d;" tag
            in
            writer :: writers
          end
      in
      let writers =
        if vtype = TUnit then writers else
          let writer ppf () =
            fprintf ppf "x->value.%s = value;" cons_id
          in
          writer :: writers
      in
      let writers = List.rev writers in
      fprintf ppf "@[<v>%a@]" (exec_all_writers ()) writers
    in

    let gen_definition_body ppf () =
      let typename = asprintf "%a" gen_tid_typename (file, type_id) in
      (gen_consdef_body gen_definition_body_core typename) ppf ()
    in

    let gen_definition ppf () =
      (gen_codeblock gen_definition_head gen_definition_body) ppf ()
    in

    (gen_prototype, gen_definition) :: fun_writers
  in

  Idmap.fold define_single_cons typedef.type_conses fun_writers

let define_ttuple_cons metainfo types fun_writers =
  let ttuple = TTuple types in
  let types_with_position = List.mapi (fun pos t -> (t, pos)) types in

  let gen_funname ppf () =
    fprintf ppf "static %a %a"
      (gen_value_type metainfo) ttuple
      gen_ttuple_consname types
  in

  let gen_prototype_params ppf () =
    pp_print_list (gen_value_type metainfo) ppf types
      ~pp_sep:pp_print_commaspace
  in

  let gen_prototype ppf () =
    fprintf ppf "@[<h>%a(%a);@]"
      gen_funname () gen_prototype_params ()
  in

  let gen_definition_params ppf () =
    pp_print_list (fun ppf (t, pos) ->
        fprintf ppf "%a member%a"
          (gen_value_type metainfo) t pp_print_int pos
      ) ppf types_with_position
      ~pp_sep:pp_print_commaspace
  in

  let gen_definition_head ppf () =
    fprintf ppf "@[<h>%a(%a)@]"
      gen_funname () gen_definition_params ()
  in

  let gen_definition_body_core ppf () =
    fprintf ppf "@[<v>";
    pp_print_list (fun ppf (_, pos) ->
        fprintf ppf "x->member%d = member%d;" pos pos
      ) ppf types_with_position;
    fprintf ppf "@]"
  in

  let gen_definition_body ppf () =
    let typename = asprintf "%a" gen_ttuple_typename types in
    (gen_consdef_body gen_definition_body_core typename) ppf ()
  in

  let gen_definition ppf () =
    (gen_codeblock gen_definition_head gen_definition_body) ppf ()
  in

  (gen_prototype, gen_definition) :: fun_writers

let define_tstate_conses metainfo (file, xfrp_smodule) fun_writers =
  let module_id = xfrp_smodule.smodule_id in
  let tstate = TState (file, module_id) in

  let define_single_cons state fun_writers =
    let state_id = state.state_id in
    let state_params = state.state_params in

    let gen_funname ppf () =
      fprintf ppf "static %a %a"
        (gen_value_type metainfo) tstate
        gen_tstate_consname (file, module_id, state_id)
    in

    let gen_prototype_params ppf () =
      pp_print_list (fun ppf (_, t) ->
          (gen_value_type metainfo) ppf t
        ) ppf state_params
        ~pp_sep:pp_print_commaspace
    in

    let gen_prototype ppf () =
      fprintf ppf "@[<h>%a(%a);@]"
        gen_funname () gen_prototype_params ()
    in

    let gen_definition_params ppf () =
      pp_print_list (fun ppf (id, t) ->
          fprintf ppf "%a %a"
            (gen_value_type metainfo) t pp_print_string id
        ) ppf state_params
    in

    let gen_definition_head ppf () =
      fprintf ppf "@[<h>static %a %a(%a)@]"
        (gen_value_type metainfo) tstate
        gen_tstate_consname (file, module_id, state_id)
        gen_definition_params ()
    in

    let gen_definition_body_core ppf () =
      let typedata = metainfo.typedata in
      let is_singleton = Hashset.mem typedata.singleton_types tstate in
      fprintf ppf "@[<v>";
      fprintf ppf "x->fresh = 1;";
      if is_singleton then () else
        begin
          let tag =
            Hashtbl.find typedata.cons_tag tstate
            |> Idmap.find state_id
          in
          fprintf ppf "@,x->tag = %d;" tag
        end;
      if state_params = [] then () else
        begin
          let gen_param_assign ppf (param_id, _) =
            fprintf ppf "x->params.%s.%s = %s;" state_id param_id param_id
          in
          fprintf ppf "@,%a" (pp_print_list gen_param_assign) state_params
        end;
      fprintf ppf "@]"
    in

    let gen_definition_body ppf () =
      let typename = asprintf "%a" gen_tstate_typename (file, module_id) in
      (gen_consdef_body gen_definition_body_core typename) ppf ()
    in

    let gen_definition ppf () =
      (gen_codeblock gen_definition_head gen_definition_body) ppf ()
    in

    (gen_prototype, gen_definition) :: fun_writers
  in

  let states = xfrp_smodule.smodule_states in
  idmap_fold_values define_single_cons states fun_writers


let define_gcfun typename gen_recmark_opt gen_recfree_opt fun_writers =

  let gen_funname_mark ppf () =
    fprintf ppf "static void mark_%s" typename
  in

  let gen_markfun_prototype ppf () =
    fprintf ppf "%a(struct %a*, int);"
      gen_funname_mark () pp_print_string typename
  in

  let gen_markfun_definition ppf () =

    let gen_markfun_definition_body ppf () =
      fprintf ppf "@[<v>";
      fprintf ppf "if (mark > x->mark) { x->mark = mark; }";
      (pp_opt
         (fun ppf writer -> fprintf ppf "@,%a" writer ())
         pp_none) ppf gen_recmark_opt;
      fprintf ppf "@]"
    in

    (gen_codeblock
       (fun ppf () ->
         fprintf ppf "@[<h>%a(struct %a* x, int mark)@]"
           gen_funname_mark () pp_print_string typename)
       gen_markfun_definition_body) ppf ()
  in

  let gen_funname_free ppf () =
    fprintf ppf "static void free_%s" typename
  in

  let gen_freefun_prototype ppf () =
    fprintf ppf "%a(struct %a*);"
      gen_funname_free () pp_print_string typename
  in

  let gen_freefun_definition ppf () =

    let gen_freefun_definition_body ppf () =
      fprintf ppf "@[<v>";
      fprintf ppf "x->mark = 0;";
      (pp_opt
         (fun ppf writer -> fprintf ppf "@,%a" writer ())
         pp_none) ppf gen_recfree_opt;
      fprintf ppf "@]"
    in

    (gen_codeblock
       (fun ppf () ->
         fprintf ppf "@[<h>%a(struct %a* x)@]"
           gen_funname_free () pp_print_string typename)
       gen_freefun_definition_body) ppf ()
  in

  fun_writers
  |> List.cons (gen_markfun_prototype, gen_markfun_definition)
  |> List.cons (gen_freefun_prototype, gen_freefun_definition)

let define_tid_gcfun metainfo (file, typedef) fun_writers =
  let type_id = typedef.type_id in
  let tid = TId (file, type_id) in
  let typename = asprintf "%a" gen_tid_typename (file, type_id) in
  let enum_types = metainfo.typedata.enum_types in
  let singleton_types = metainfo.typedata.singleton_types in
  let tag_table = Hashtbl.find metainfo.typedata.cons_tag tid in

  let reccall_branchs =
    Idmap.fold (fun cons_id vtype branchs ->
        let tag = Idmap.find cons_id tag_table in
        match vtype with
        | TBool | TInt | TFloat | TUnit -> branchs
        | TId (file, type_id) ->
           if Hashset.mem enum_types vtype then branchs else
             let vtypename = asprintf "%a" gen_tid_typename (file, type_id) in
             (tag, cons_id, vtypename) :: branchs
        | TTuple types ->
           let vtypename = asprintf "%a" gen_ttuple_typename types in
           (tag, cons_id, vtypename) :: branchs
        | _ -> assert false
      ) typedef.type_conses []
    |> List.rev
  in

  let gen_funcall_mark ppf (cons_id, vtypename) =
    fprintf ppf "mark_%s(x->value.%s, mark);" vtypename cons_id
  in

  let gen_funcall_free ppf (cons_id, vtypename) =
    fprintf ppf "free_%s(x->value.%s);" vtypename cons_id
  in

  let (gen_recmark_opt, gen_recfree_opt) =
    if reccall_branchs = [] then
      (None, None)
    else if Hashset.mem singleton_types tid then
      let (cons_id, vtypename) =
        match reccall_branchs with
        | [(_, cons_id, vtypename)] -> (cons_id, vtypename)
        | _ -> assert false
      in
      let gen_recmark ppf () =
        gen_funcall_mark ppf (cons_id, vtypename)
      in
      let gen_recfree ppf () =
        gen_funcall_free ppf (cons_id, vtypename)
      in
      (Some gen_recmark, Some gen_recfree)
    else
      let gen_reccall gen_funcall ppf () =
        fprintf ppf "@[<v>";
        fprintf ppf "switch (x->tag) {@,";
        pp_print_list (fun ppf (tag, cons_id, vtypename) ->
            fprintf ppf "@[<v 2>case %a:@,%a@]"
              pp_print_int tag gen_funcall (cons_id, vtypename)
          ) ppf reccall_branchs;
        fprintf ppf "@,}";
        fprintf ppf "@]"
      in
      let gen_recmark ppf () =
        (gen_reccall gen_funcall_mark) ppf ()
      in
      let gen_recfree ppf () =
        (gen_reccall gen_funcall_free) ppf ()
      in
      (Some gen_recmark, Some gen_recfree)
  in

  define_gcfun typename gen_recmark_opt gen_recfree_opt fun_writers

let define_ttuple_gcfun metainfo types fun_writers =
  let typename = asprintf "%a" gen_ttuple_typename types in
  let types_with_position = List.mapi (fun pos t -> (t, pos)) types in
  let enum_types = metainfo.typedata.enum_types in

  let reccalls =
    List.fold_right (fun (memtype, pos) reccalls ->
        match memtype with
        | TBool | TInt | TFloat | TUnit -> reccalls
        | TId (file, type_id) ->
           if Hashset.mem enum_types memtype then reccalls else
             let memtypename =
               asprintf "%a" gen_tid_typename (file, type_id)
             in
             (memtypename, pos) :: reccalls
        | TTuple types ->
           let memtypename =
             asprintf "%a" gen_ttuple_typename types
           in
           (memtypename, pos) :: reccalls
        | _ -> assert false
      ) types_with_position []
    |> List.rev
  in

  let gen_funcall_mark ppf (memtypename, pos) =
    fprintf ppf "mark_%s(x->member%d, mark);" memtypename pos
  in

  let gen_funcall_free ppf (memtypename, pos) =
    fprintf ppf "free_%s(x->member%d);" memtypename pos
  in

  let (gen_recmark_opt, gen_recfree_opt) =
    if reccalls = [] then
      (None, None)
    else
      let gen_recmark ppf () =
        pp_print_list gen_funcall_mark ppf reccalls
      in
      let gen_recfree ppf () =
        pp_print_list gen_funcall_free ppf reccalls
      in
      (Some gen_recmark, Some gen_recfree)
  in

  define_gcfun typename gen_recmark_opt gen_recfree_opt fun_writers

let define_tstate_gcfun metainfo (file, xfrp_smodule) fun_writers =
  let module_id = xfrp_smodule.smodule_id in
  let tstate = TState (file, module_id) in
  let typename = asprintf "%a" gen_tstate_typename (file, module_id) in
  let enum_types = metainfo.typedata.enum_types in
  let singleton_types = metainfo.typedata.singleton_types in
  let tag_table = Hashtbl.find metainfo.typedata.cons_tag tstate in

  let get_state_reccalls state =
    let state_id = state.state_id in
    List.fold_right (fun (pid, ptype) reccalls ->
        match ptype with
        | TBool | TInt | TFloat | TUnit -> reccalls
        | TId (file, type_id) ->
           if Hashset.mem enum_types ptype then reccalls else
             let ptypename =
               asprintf "%a" gen_tid_typename (file, type_id)
             in
             (state_id, pid, ptypename) :: reccalls
        | TTuple types ->
           let ptypename =
             asprintf "%a" gen_ttuple_typename types
           in
           (state_id, pid, ptypename) :: reccalls
        | _ -> assert false
      ) state.state_params []
  in

  let reccall_branchs =
    idmap_fold_values (fun state branchs ->
        let tag = Idmap.find state.state_id tag_table in
        let reccalls = get_state_reccalls state in
        if reccalls = [] then branchs else
          (tag, reccalls) :: branchs
      ) xfrp_smodule.smodule_states []
  in

  let gen_funcall_mark ppf (state_id, pid, ptypename) =
    fprintf ppf "mark_%s(x->params->%s->%s, mark);"
      ptypename state_id pid
  in

  let gen_funcall_free ppf (state_id, pid, ptypename) =
    fprintf ppf "free_%s(x->params->%s->%s, mark);"
      ptypename state_id pid
  in

  let (gen_recmark_opt, gen_recfree_opt) =
    if reccall_branchs = [] then
      (None, None)
    else if Hashset.mem singleton_types tstate then
      let reccalls =
        match reccall_branchs with
        | [(_, reccalls)] -> reccalls
        | _ -> assert false
      in
      let gen_recmark ppf () =
        pp_print_list gen_funcall_mark ppf reccalls
      in
      let gen_recfree ppf () =
        pp_print_list gen_funcall_free ppf reccalls
      in
      (Some gen_recmark, Some gen_recfree)
    else
      let gen_reccall gen_funcall ppf () =
        fprintf ppf "@[<v>";
        fprintf ppf "switch (x->tag) {@,";
        pp_print_list (fun ppf (tag, reccalls) ->
            fprintf ppf "@[<v 2>case %a:@,@[<v>%a@]@]"
              pp_print_int tag
              (pp_print_list gen_funcall) reccalls
          ) ppf reccall_branchs;
        fprintf ppf "@,}";
        fprintf ppf "@]"
      in
      let gen_recmark ppf () =
        (gen_reccall gen_funcall_mark) ppf ()
      in
      let gen_recfree ppf () =
        (gen_reccall gen_funcall_free) ppf ()
      in
      (Some gen_recmark, Some gen_recfree)
  in

  define_gcfun typename gen_recmark_opt gen_recfree_opt fun_writers

let define_tid_fun metainfo (file, typedef) fun_writers =
  fun_writers
  |> define_tid_conses metainfo (file, typedef)
  |> define_tid_gcfun metainfo (file, typedef)

let define_ttuple_fun metainfo types fun_writers =
  fun_writers
  |> define_ttuple_cons metainfo types
  |> define_ttuple_gcfun metainfo types

let define_tstate_fun metainfo (file, xfrp_smodule) fun_writers =
  fun_writers
  |> define_tstate_conses metainfo (file, xfrp_smodule)
  |> define_tstate_gcfun metainfo (file, xfrp_smodule)

let define_type_fun metainfo fun_writers=
  let nonenum_tid_defs = metainfo.typedata.nonenum_tid_defs in
  let tuple_types = metainfo.typedata.tuple_types in
  let tstate_defs = metainfo.typedata.tstate_defs in
  fun_writers
  |> List.fold_right (define_tid_fun metainfo)
       (List.rev nonenum_tid_defs)
  |> List.fold_right (define_ttuple_fun metainfo)
       (List.rev tuple_types)
  |> List.fold_right (define_tstate_fun metainfo)
       (List.rev tstate_defs)

