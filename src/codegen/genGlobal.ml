open Extension.Format
open Syntax
open Type
open MetaInfo
open CodegenUtil

let gen_type_globals ppf metainfo =
  let gen_single typename array_size ppf () =
    fprintf ppf "@[<h>struct %s memory_%s[%d];@]" typename typename array_size;
    fprintf ppf "@,@[<h>int size_%s = %d;@]" typename array_size;
    fprintf ppf "@,@[<h>int counter_%s = 0;@]" typename
  in
  let gen_tid ppf (file, typedef) =
    let type_id = typedef.type_id in
    let tid = TId (file, type_id) in
    let typename = asprintf "%a" gen_tid_typename (file, type_id) in
    let array_size = Hashtbl.find metainfo.alloc_amount tid in
    (gen_single typename array_size) ppf ()
  in
  let gen_ttuple ppf types =
    let ttuple = TTuple types in
    let typename = asprintf "%a" gen_ttuple_typename types in
    let array_size = Hashtbl.find metainfo.alloc_amount ttuple in
    (gen_single typename array_size) ppf ()
  in
  let gen_tstate ppf (file, xfrp_smodule) =
    let module_id = xfrp_smodule.smodule_id in
    let tstate = TState (file, module_id) in
    let typename = asprintf "%a" gen_tstate_typename (file, module_id) in
    let array_size = Hashtbl.find metainfo.alloc_amount tstate in
    (gen_single typename array_size) ppf ()
  in
  let nonenum_tid_defs = metainfo.typedata.nonenum_tid_defs in
  let tuple_types = metainfo.typedata.tuple_types in
  let tstate_defs = metainfo.typedata.tstate_defs in
  let print_all printer = pp_print_list printer ~pp_sep:pp_print_cut2 in
  if nonenum_tid_defs = []
  then ()
  else fprintf ppf "@,@,%a" (print_all gen_tid) nonenum_tid_defs;
  if tuple_types = [] then () else fprintf ppf "@,@,%a" (print_all gen_ttuple) tuple_types;
  if tstate_defs = [] then () else fprintf ppf "@,@,%a" (print_all gen_tstate) tstate_defs
;;

let gen_global_consts ppf metainfo =
  let gen_single ppf (file, const) =
    fprintf
      ppf
      "@[<h>%a %a;@]"
      (gen_value_type metainfo)
      const.const_type
      gen_global_constname
      (file, const.const_id)
  in
  let all_consts = metainfo.all_elements.all_consts in
  if all_consts = [] then () else fprintf ppf "@,%a" (pp_print_list gen_single) all_consts
;;

let gen_io_nodes ppf metainfo in_out_sig =
  let gen_single = function
    | id, TMode (file, mode, t) ->
      fprintf
        ppf
        "@,struct %a %a;"
        (gen_with_mode_type metainfo)
        (file, mode, t)
        pp_identifier
        id
    | _ -> ()
  in
  List.iter gen_single in_out_sig
;;

let generate ppf metainfo =
  let entry_file = metainfo.entry_file in
  let toplevel_clockperiod, in_sig, out_sig =
    match Hashtbl.find metainfo.moduledata (entry_file, "Main") with
    | ModuleInfo info -> info.module_clockperiod, info.module_in_sig, info.module_out_sig
    | SModuleInfo info ->
      info.smodule_clockperiod, info.smodule_in_sig, info.smodule_out_sig
  in
  let iter_period = toplevel_clockperiod + 1 in
  (* for global const *)
  fprintf ppf "@[<v>";
  fprintf ppf "@[<h>int clock;@]";
  fprintf ppf "@,@[<h>int period = %d;@]" iter_period;
  fprintf ppf "@,@[<h>int current_side;@]";
  gen_global_consts ppf metainfo;
  gen_type_globals ppf metainfo;
  fprintf ppf "@,";
  gen_io_nodes ppf metainfo (in_sig @ out_sig);
  fprintf ppf "@,@,@[<h>%a memory;@]" gen_module_memory_type (entry_file, "Main");
  fprintf ppf "@]"
;;
