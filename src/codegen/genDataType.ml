open Extension
open Extension.Format
open Syntax
open Type
open MetaInfo
open CodegenUtil

let gen_tid metainfo ppf (file, typedef) =
  let typedata = metainfo.typedata in
  let tid = TId (file, typedef.type_id) in
  let gen_tid_tag_head ppf () =
    fprintf ppf "enum %a" gen_tid_tag_name (file, typedef.type_id)
  in
  let gen_tid_tag_body ppf () =
    let gen_tag_val ppf (c, _) = gen_tid_tag_val ppf ((file, typedef.type_id), c) in
    fprintf ppf "@[<hov>";
    pp_list_comma gen_tag_val ppf (Idmap.bindings typedef.type_conses);
    fprintf ppf "@]"
  in
  let gen_value_union ppf conses =
    let gen_union_field ppf (c, vtype) =
      fprintf ppf "@[<h>%a %a;@]" (gen_value_type metainfo) vtype pp_print_string c
    in
    let gen_value_union_body ppf () =
      let conses_with_value =
        Idmap.bindings conses |> List.filter (fun (_, vtype) -> vtype != TUnit)
      in
      fprintf ppf "@[<v>";
      (pp_print_list gen_union_field) ppf conses_with_value;
      fprintf ppf "@]"
    in
    (gen_anonymous_union gen_value_union_body "value") ppf ()
  in
  let gen_tid_head ppf () =
    fprintf ppf "struct %a" gen_tid_typename (file, typedef.type_id)
  in
  let gen_tid_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    if Hashset.mem typedata.singleton_types tid
    then ()
    else fprintf ppf "@,@[<h>enum %a tag;@]" gen_tid_tag_name (file, typedef.type_id);
    fprintf ppf "@,";
    gen_value_union ppf typedef.type_conses;
    fprintf ppf "@]"
  in
  fprintf ppf "%a;@," (gen_codeblock gen_tid_tag_head gen_tid_tag_body) ();
  fprintf ppf "%a;" (gen_codeblock gen_tid_head gen_tid_body) ()
;;

let gen_ttuple metainfo ppf types =
  let gen_member_value ppf (t, pos) =
    fprintf ppf "@[<h>%a member%a;@]" (gen_value_type metainfo) t pp_print_int pos
  in
  let gen_ttuple_head ppf () = fprintf ppf "struct %a" gen_ttuple_typename types in
  let gen_ttuple_body ppf () =
    let types_with_position = List.mapi (fun pos t -> t, pos) types in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    fprintf ppf "@,%a" (pp_print_list gen_member_value) types_with_position;
    fprintf ppf "@]"
  in
  fprintf ppf "%a;" (gen_codeblock gen_ttuple_head gen_ttuple_body) ()
;;

let gen_with_mode_type metainfo ppf ((file, mode_id, t') as t) =
  let gen_header ppf () = fprintf ppf "struct %a" (gen_with_mode_type metainfo) t in
  let gen_body ppf () =
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>enum %a mode[2];@]" gen_mode_name (file, mode_id);
    fprintf ppf "@,%a value;" (gen_value_type metainfo) t';
    fprintf ppf "@]"
  in
  fprintf ppf "%a;" (gen_codeblock gen_header gen_body) ()
;;

let gen_tstate metainfo ppf (file, xfrp_smodule) =
  let typedata = metainfo.typedata in
  let tstate = TState (file, xfrp_smodule.smodule_id) in
  let gen_tstate_tag_head ppf () =
    fprintf ppf "enum %a" gen_tstate_tag_name (file, xfrp_smodule.smodule_id)
  in
  let gen_tstate_tag_body ppf () =
    let gen_tag_val ppf (c, _) =
      gen_tstate_tag_val ppf ((file, xfrp_smodule.smodule_id), c)
    in
    fprintf ppf "@[<hov>";
    pp_list_comma gen_tag_val ppf (Idmap.bindings xfrp_smodule.smodule_states);
    fprintf ppf "@]"
  in
  let gen_param_struct ppf state =
    let gen_param_field ppf (id, t) =
      fprintf ppf "@[<h>%a %a;@]" (gen_value_type metainfo) t pp_print_string id
    in
    let gen_param_struct_body ppf () =
      fprintf ppf "@[<v>";
      (pp_print_list gen_param_field) ppf state.state_params;
      fprintf ppf "@]"
    in
    (gen_anonymous_struct gen_param_struct_body state.state_id) ppf ()
  in
  let gen_param_union ppf states_with_params =
    let gen_param_union_body ppf () =
      fprintf ppf "@[<v>";
      (pp_print_list gen_param_struct) ppf states_with_params;
      fprintf ppf "@]"
    in
    (gen_anonymous_union gen_param_union_body "params") ppf ()
  in
  let gen_tstate_head ppf () =
    fprintf ppf "struct %a" gen_tstate_typename (file, xfrp_smodule.smodule_id)
  in
  let gen_tstate_body ppf () =
    let states_with_params =
      idmap_value_list xfrp_smodule.smodule_states
      |> List.filter (fun state -> state.state_params != [])
    in
    fprintf ppf "@[<v>";
    fprintf ppf "@[<h>int mark;@]";
    fprintf ppf "@,@[<h>int fresh;@]";
    if Hashset.mem typedata.singleton_types tstate
    then ()
    else
      fprintf
        ppf
        "@,@[<h>enum %a tag;@]"
        gen_tstate_tag_name
        (file, xfrp_smodule.smodule_id);
    if states_with_params = []
    then ()
    else fprintf ppf "@,%a" gen_param_union states_with_params;
    fprintf ppf "@]"
  in
  fprintf ppf "%a;@," (gen_codeblock gen_tstate_tag_head gen_tstate_tag_body) ();
  fprintf ppf "%a;" (gen_codeblock gen_tstate_head gen_tstate_body) ()
;;

let generate ppf metainfo =
  let types_with_mode = metainfo.typedata.types_with_mode in
  let tstate_defs = metainfo.typedata.tstate_defs in
  let print_all printer = pp_print_list printer ~pp_sep:pp_print_cut2 in
  fprintf ppf "struct XfrpUnit xfrpUnit = {};@,@,";
  if types_with_mode = []
  then ()
  else fprintf ppf "%a@,@," (print_all (gen_with_mode_type metainfo)) types_with_mode;
  if tstate_defs = []
  then ()
  else fprintf ppf "%a" (print_all (gen_tstate metainfo)) tstate_defs;
  fprintf ppf "@]"
;;

let generate_header ppf metainfo =
  let nonenum_tid_defs = metainfo.typedata.nonenum_tid_defs in
  let tuple_types = metainfo.typedata.tuple_types in
  let print_all printer = pp_print_list printer ~pp_sep:pp_print_cut2 in
  fprintf ppf "@[<v>";
  fprintf ppf "struct XfrpUnit {};@,@,";
  if nonenum_tid_defs = []
  then ()
  else fprintf ppf "%a@,@," (print_all (gen_tid metainfo)) nonenum_tid_defs;
  if tuple_types = []
  then ()
  else fprintf ppf "%a" (print_all (gen_ttuple metainfo)) tuple_types;
  fprintf ppf "@]"
;;
