open Syntax
open Extension
open Extension.Format

module Intmap = Map.Make (struct
    type t = int

    let compare = compare
  end)

let pp_intmap pp_contents ppf intmap =
  let pp_binds ppf (i, x) = fprintf ppf "%a : %a" pp_print_int i pp_contents x in
  pp_list_comma pp_binds ppf (Intmap.to_seq intmap |> List.of_seq)
;;

type timetable = Idset.t Intmap.t

let to_timetable int_idmap =
  let update id time revmap =
    Intmap.update
      time
      (function
       | Some s -> Some (Idset.add id s)
       | None -> Some (Idset.singleton id))
      revmap
  in
  Idmap.fold update int_idmap Intmap.empty
;;

type all_elements =
  { all_modules : (string * xfrp_elem) list
  ; all_consts : (string * constdef) list
  ; all_funs : (string * fundef) list
  }

let pp_all_elements ppf all_elements =
  let pp_all_modules_elem ppf (file, module_or_smodule) =
    match module_or_smodule with
    | XFRPModule m -> fprintf ppf "%s:%s" file m.module_id
    | XFRPSModule sm -> fprintf ppf "%s:%s" file sm.smodule_id
    | _ -> assert false
  in
  let pp_all_consts_elem ppf (file, constdef) =
    fprintf ppf "%s:%s" file constdef.const_id
  in
  let pp_all_funs_elem ppf (file, fundef) = fprintf ppf "%s:%s" file fundef.fun_id in
  let get_list_printer pp_elem = pp_print_list pp_elem ~pp_sep:pp_print_commaspace in
  let all_modules = all_elements.all_modules in
  let all_consts = all_elements.all_consts in
  let all_funs = all_elements.all_funs in
  fprintf ppf "@[<v>";
  fprintf
    ppf
    "@[<hv>all_modules: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_modules_elem)
    all_modules;
  fprintf
    ppf
    "@,@[<hv>all_consts: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_consts_elem)
    all_consts;
  fprintf
    ppf
    "@,@[<hv>all_funs: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_funs_elem)
    all_funs;
  fprintf ppf "@]"
;;

type lifetime =
  { timestamp : int Idmap.t
  ; free_current : int option Idmap.t
  ; free_last : int Idmap.t
  }

let pp_lifetime ppf lifetime =
  let pp_free_current_elem ppf elem =
    (pp_opt pp_print_int (fun ppf () -> pp_print_string ppf "not freed")) ppf elem
  in
  let pp_timetable_row ppf ids = fprintf ppf "@[<hov>%a@]" pp_idset ids in
  fprintf ppf "@[<v>";
  fprintf ppf "timestamp:@;<0 2>";
  fprintf ppf "@[<v>%a@]@;" (pp_intmap pp_timetable_row) (to_timetable lifetime.timestamp);
  fprintf ppf "curref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" (pp_idmap pp_free_current_elem) lifetime.free_current;
  fprintf ppf "lastref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]" (pp_idmap pp_print_int) lifetime.free_last;
  fprintf ppf "@]"
;;

let pp_signature ppf signature =
  (pp_print_list
     (fun ppf (id, t) -> fprintf ppf "%a : %a" pp_print_string id Type.pp_t t)
     ~pp_sep:pp_print_commaspace)
    ppf
    signature
;;

type mode_calc =
  { mode_type : string * identifier (* file * mode_id *)
  ; self_modev : identifier (* mode value specified by mode annotation *)
  ; child_modev : ((string * identifier) * identifier * identifier) list
      (* (instantiated module_id * newnode_id * io_node_name) list *)
  }

let pp_mode_calc ppf modec =
  let pp_child_modev_elem ppf ((file, module_id), newnode_id, io_name) =
    fprintf ppf "%s(%s:%s).%s" newnode_id file module_id io_name
  in
  fprintf ppf "@[<v>";
  fprintf ppf "mode_type: %s:%s" (fst modec.mode_type) (snd modec.mode_type);
  fprintf ppf "@,self_modev: %s" modec.self_modev;
  fprintf ppf "@,@[<hov 2>child_modev: ";
  fprintf ppf "@,%a@]" (pp_list_comma pp_child_modev_elem) modec.child_modev;
  fprintf ppf "@]"
;;

type module_info =
  { module_clockperiod : int
  ; module_param_sig : (identifier * Type.t) list
  ; module_in_sig : (identifier * Type.t) list
  ; module_out_sig : (identifier * Type.t) list
  ; module_lifetime : lifetime
  ; module_mode_calc : mode_calc Idmap.t
  }

let pp_module_info ppf module_info =
  fprintf ppf "@[<v>";
  fprintf ppf "clockperiod: %a" pp_print_int module_info.module_clockperiod;
  fprintf ppf "@,param_sig: @[<h>%a@]" pp_signature module_info.module_param_sig;
  fprintf ppf "@,in_sig: @[<h>%a@]" pp_signature module_info.module_in_sig;
  fprintf ppf "@,out_sig: @[<h>%a@]" pp_signature module_info.module_out_sig;
  fprintf ppf "@,life_time:@;<0 2>%a" pp_lifetime module_info.module_lifetime;
  fprintf ppf "@,mode_calc:@;<0 2>%a" (pp_idmap pp_mode_calc) module_info.module_mode_calc;
  fprintf ppf "@]"
;;

type smodule_info =
  { smodule_clockperiod : int
  ; smodule_param_sig : (identifier * Type.t) list
  ; smodule_in_sig : (identifier * Type.t) list
  ; smodule_out_sig : (identifier * Type.t) list
  ; state_lifetime : lifetime Idmap.t
  ; state_mode_calc : mode_calc Idmap.t Idmap.t
  }

let pp_smodule_info ppf smodule_info =
  fprintf ppf "@[<v>";
  fprintf ppf "clockperiod: %a" pp_print_int smodule_info.smodule_clockperiod;
  fprintf ppf "@,param_sig: @[<h>%a@]" pp_signature smodule_info.smodule_param_sig;
  fprintf ppf "@,in_sig: @[<h>%a@]" pp_signature smodule_info.smodule_in_sig;
  fprintf ppf "@,out_sig: @[<h>%a@]" pp_signature smodule_info.smodule_out_sig;
  fprintf
    ppf
    "@,life_time:@;<0 2>@[<v>%a@]"
    (pp_idmap pp_lifetime)
    smodule_info.state_lifetime;
  fprintf
    ppf
    "@,state_mode_calc:@;<0 2>@[<v>%a@]"
    (pp_idmap (pp_idmap pp_mode_calc))
    smodule_info.state_mode_calc;
  fprintf ppf "@]"
;;

type moduledata_elem =
  | ModuleInfo of module_info
  | SModuleInfo of smodule_info

let pp_moduledata_elem ppf = function
  | ModuleInfo info -> fprintf ppf "@[<v 2>Module:@,%a@]" pp_module_info info
  | SModuleInfo info -> fprintf ppf "@[<v 2>SModule:@,%a@]" pp_smodule_info info
;;

type alloc_amount = (Type.t, int) Hashtbl.t

let pp_alloc_amount ppf alloc_amount =
  let pp_binds ppf (t, size) = fprintf ppf "%a -> %a" Type.pp_t t pp_print_int size in
  pp_print_hashtbl pp_binds ppf alloc_amount ~pp_sep:pp_print_commaspace
;;

type typedata =
  { enum_types : Type.t Hashset.t
  ; singleton_types : Type.t Hashset.t
  ; cons_tag : (Type.t, int Idmap.t) Hashtbl.t
  ; nonenum_tid_defs : (string * typedef) list
  ; tuple_types : Type.t list list
  ; tstate_defs : (string * xfrp_smodule) list
  ; tstate_param_ids : (Type.t, string list Idmap.t) Hashtbl.t
  ; modes : (string * modedef) list
  }

let pp_typedata ppf typedata =
  let pp_typeset ppf typeset =
    (pp_print_hashset Type.pp_t ~pp_sep:pp_print_commaspace) ppf typeset
  in
  let pp_cons_tag ppf cons_tag =
    let pp_single_map ppf (t, m) =
      fprintf ppf "%a -> @[<v>%a@]" Type.pp_t t (pp_idmap pp_print_int) m
    in
    (pp_print_hashtbl pp_single_map) ppf cons_tag
  in
  let list_printer pp_elem = pp_print_list pp_elem ~pp_sep:pp_print_commaspace in
  let pp_nonenum_tid_defs ppf nonenum_tid_defs =
    let pp_elem ppf (file, typedef) = fprintf ppf "%s:%s" file typedef.type_id in
    (list_printer pp_elem) ppf nonenum_tid_defs
  in
  let pp_tuple_types ppf tuple_types =
    let pp_elem ppf types = fprintf ppf "@[<h>(%a)@]" (list_printer Type.pp_t) types in
    (list_printer pp_elem) ppf tuple_types
  in
  let pp_tstate_defs ppf tstate_defs =
    let pp_elem ppf (file, xfrp_smodule) =
      fprintf ppf "%s:%s" file xfrp_smodule.smodule_id
    in
    (list_printer pp_elem) ppf tstate_defs
  in
  let pp_tstate_param_ids ppf tstate_param_ids =
    let pp_params ppf param_ids =
      fprintf ppf "@[<h>(%a)@]" (list_printer pp_print_string) param_ids
    in
    let pp_elem ppf (tstate, param_ids_table) =
      fprintf ppf "%a -> @[<v>%a@]" Type.pp_t tstate (pp_idmap pp_params) param_ids_table
    in
    (pp_print_hashtbl pp_elem) ppf tstate_param_ids
  in
  let pp_modes ppf modes =
    let pp_mode ppf (file, modedef) = fprintf ppf "%s:%a@ " file pp_modedef modedef in
    pp_list_comma pp_mode ppf modes
  in
  fprintf ppf "@[<v>";
  fprintf ppf "enum_types:";
  fprintf ppf "@;<0 2>@[<hov> %a @]" pp_typeset typedata.enum_types;
  fprintf ppf "@,singleton_types:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_typeset typedata.singleton_types;
  fprintf ppf "@,cons_tag:";
  fprintf ppf "@;<0 2>@[<v>%a@]" pp_cons_tag typedata.cons_tag;
  fprintf ppf "@,nonenum_tid_defs:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_nonenum_tid_defs typedata.nonenum_tid_defs;
  fprintf ppf "@,tuple_types:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_tuple_types typedata.tuple_types;
  fprintf ppf "@,tstate_defs:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_tstate_defs typedata.tstate_defs;
  fprintf ppf "@,tstate_param_ids:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_tstate_param_ids typedata.tstate_param_ids;
  fprintf ppf "@,modes:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_modes typedata.modes;
  fprintf ppf "@]"
;;

type metainfo =
  { entry_file : string
  ; all_elements : all_elements
  ; moduledata : (string * string, moduledata_elem) Hashtbl.t
  ; alloc_amount : alloc_amount
  ; typedata : typedata
  }

let pp_metainfo ppf metainfo =
  let pp_moduledata ppf moduledata =
    pp_print_hashtbl
      (fun ppf ((file, module_id), elem) ->
        fprintf
          ppf
          "%a:%a -> @[<v>%a@]"
          pp_print_string
          file
          pp_print_string
          module_id
          pp_moduledata_elem
          elem)
      ppf
      moduledata
  in
  fprintf ppf "@[<v>";
  fprintf ppf "entry_file: %s" metainfo.entry_file;
  fprintf ppf "@,all_elements:@;<0 2>@[%a@]" pp_all_elements metainfo.all_elements;
  fprintf ppf "@,moduledata:@;<0 2>@[<v>%a@]" pp_moduledata metainfo.moduledata;
  fprintf ppf "@,alloc_amount:@;<0 2>@[%a@]" pp_alloc_amount metainfo.alloc_amount;
  fprintf ppf "@,typedata:@;<0 2>@[%a@]" pp_typedata metainfo.typedata;
  fprintf ppf "@]"
;;

let all_elements_empty = { all_modules = []; all_consts = []; all_funs = [] }
let alloc_amount_empty () = Hashtbl.create 20

let typedata_empty () =
  { enum_types = Hashset.create 20
  ; singleton_types = Hashset.create 20
  ; cons_tag = Hashtbl.create 20
  ; nonenum_tid_defs = []
  ; tuple_types = []
  ; tstate_defs = []
  ; tstate_param_ids = Hashtbl.create 20
  ; modes = []
  }
;;

let metainfo_empty entry_file =
  { entry_file
  ; all_elements = all_elements_empty
  ; moduledata = Hashtbl.create 20
  ; alloc_amount = alloc_amount_empty ()
  ; typedata = typedata_empty ()
  }
;;
