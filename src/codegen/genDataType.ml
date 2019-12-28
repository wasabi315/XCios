open Extension
open Extension.Format
open Syntax
open Type
open MetaInfo
open CodegenUtil

let gen_tstate all_data metainfo ppf (file, module_name) =
  let typedata = metainfo.typedata in
  let tstate = TState (file, module_name) in
  let xfrp_smodule =
    let filedata = Idmap.find file all_data in
    Idmap.find module_name filedata.xfrp_smodules
  in

  let gen_param_struct ppf state =

    let gen_param_field ppf (id, t) =
      fprintf ppf "@[<h>%a %a;@]" (gen_ctype metainfo) t pp_print_string id
    in

    let gen_param_struct_body ppf () =
      fprintf ppf "@[<v>";
      (pp_print_list gen_param_field) ppf state.state_params;
      fprintf ppf "@]"
    in

    (gen_anonymous_struct gen_param_struct_body state.state_id) ppf ()
  in


  let gen_param_union ppf states =

    let states_with_params =
      idmap_value_list states
      |> List.filter (fun state -> state.state_params != [])
    in

    let gen_param_union_body ppf () =
      fprintf ppf "@[<v>";
      (pp_print_list gen_param_struct) ppf states_with_params;
      fprintf ppf "@]"
    in

    (gen_anonymous_union gen_param_union_body "params") ppf ()
  in

  let gen_tstate_head ppf () =
    fprintf ppf "struct %a" gen_tstate_typename (file, module_name)
  in

  let gen_tstate_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    if Hashset.mem typedata.singleton_types tstate then () else
      fprintf ppf "@,@[<h>int cons_id;@]";
    fprintf ppf "@,"; gen_param_union ppf xfrp_smodule.smodule_states;
    fprintf ppf "@]"
  in

  (gen_codeblock gen_tstate_head gen_tstate_body) ppf ()

let gen_tid all_data metainfo ppf (file, type_name) =
  let typedata = metainfo.typedata in
  let tid = TId (file, type_name) in
  let typedef =
    let filedata = Idmap.find file all_data in
    Idmap.find type_name filedata.xfrp_types
  in

  let gen_value_union ppf conses =

    let gen_union_field ppf (c, vtype) =
      fprintf ppf "@[<h>%a %a;@]" (gen_ctype metainfo) vtype pp_print_string c
    in

    let gen_value_union_body ppf () =
      let conses_with_value =
        Idmap.bindings conses
        |> List.filter (fun (_, vtype) -> vtype != TUnit)
      in
      fprintf ppf "@[<v>";
      (pp_print_list gen_union_field) ppf conses_with_value;
      fprintf ppf "@]"
    in

    (gen_anonymous_union gen_value_union_body "value") ppf ()
  in

  let gen_tid_head ppf () =
    fprintf ppf "struct %a" gen_tid_typename (file, type_name)
  in

  let gen_tid_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    if Hashset.mem typedata.singleton_types tid then () else
      fprintf ppf "@,@[<h>int cons_id;@]";
    fprintf ppf "@,"; gen_value_union ppf typedef.type_conses;
    fprintf ppf "@]"
  in

  (gen_codeblock gen_tid_head gen_tid_body) ppf ()

let gen_ttuple _all_data metainfo ppf types =

  let gen_member_value ppf (t, pos) =
    fprintf ppf "@[<h>%a member%a;@]" (gen_ctype metainfo) t pp_print_int pos
  in

  let gen_ttuple_head ppf () =
    fprintf ppf "struct %a" gen_ttuple_typename types
  in

  let gen_ttuple_body ppf () =
    let types_with_position =
      List.mapi (fun pos t -> (t, pos)) types
    in

    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    fprintf ppf "@,%a" (pp_print_list gen_member_value) types_with_position;
    fprintf ppf "@]"
  in

  (gen_codeblock gen_ttuple_head gen_ttuple_body) ppf ()

let generate ppf (all_data, metainfo) =

  let gen_single_type ppf = function
    | TState (file, module_name) ->
       (gen_tstate all_data metainfo) ppf (file, module_name)
    | TId (file, type_name) ->
       (gen_tid all_data metainfo) ppf (file, type_name)
    | TTuple ts ->
       (gen_ttuple all_data metainfo) ppf ts
    | _ -> assert false
  in

  get_nonenum_types metainfo
  |> (pp_print_list gen_single_type) ppf

