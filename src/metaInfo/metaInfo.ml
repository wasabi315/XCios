open Syntax
open Extension
open Extension.Format

module Intmap = Map.Make(struct type t = int let compare = compare end)

let pp_intmap pp_contents ppf intmap =
  let pp_binds ppf (i, x) =
    fprintf ppf "%a : %a" pp_print_int i pp_contents x
  in
  pp_list_comma pp_binds ppf (Intmap.to_seq intmap |> List.of_seq)

type timetable = Idset.t Intmap.t
type clockinfo = int Idmap.t

let to_timetable clockinfo =
  let update id time revmap =
    Intmap.update time (function
        | Some s -> Some (Idset.add id s)
        | None -> Some (Idset.singleton id)
      ) revmap
  in
  Idmap.fold update clockinfo Intmap.empty

type all_elements =
  {
    all_modules : (string * xfrp_elem) list;
    all_consts : (string * constdef) list;
    all_funs : (string * fundef) list;
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

  let pp_all_funs_elem ppf (file, fundef) =
    fprintf ppf "%s:%s" file fundef.fun_id
  in

  let get_list_printer pp_elem =
    pp_print_list pp_elem ~pp_sep:pp_print_commaspace
  in

  let all_modules = all_elements.all_modules in
  let all_consts = all_elements.all_consts in
  let all_funs = all_elements.all_funs in
  fprintf ppf "@[<v>";
  fprintf ppf "@[<hv>all_modules: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_modules_elem) all_modules;
  fprintf ppf "@,@[<hv>all_consts: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_consts_elem) all_consts;
  fprintf ppf "@,@[<hv>all_funs: {@;<0 2>@[<hov>%a@]@;<0 0>}@]"
    (get_list_printer pp_all_funs_elem) all_funs;
  fprintf ppf "@]"

let all_elements_empty =
  { all_modules = []; all_consts = []; all_funs = [] }

type nodelife =
  {
    curref_life  : clockinfo;
    lastref_life : clockinfo;
  }

let pp_nodelife ppf nodelife =
  fprintf ppf "@[<v>curref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" (pp_idmap pp_print_int) nodelife.curref_life;
  fprintf ppf "lastref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]@]" (pp_idmap pp_print_int) nodelife.lastref_life

let nodelife_empty = { curref_life = Idmap.empty; lastref_life = Idmap.empty }

type lifetime =
  {
    clockperiod : int;
    timestamp : int Idmap.t;
    nodelifes : nodelife Idmap.t;
  }

let pp_lifetime ppf lifetime =
  let pp_timetable_row ppf ids =
    fprintf ppf "@[<hov>%a@]" pp_idset ids
  in
  fprintf ppf "@[<v>clockperiod: %a@;" pp_print_int lifetime.clockperiod;
  fprintf ppf "timestamp:@;<0 2>";
  fprintf ppf "@[<v>%a@]@;"
    (pp_intmap pp_timetable_row) (to_timetable lifetime.timestamp);
  fprintf ppf "nodelifes:@;<0 2>";
  fprintf ppf "@[<v>%a@]@]" (pp_idmap pp_nodelife) lifetime.nodelifes

let lifetime_empty =
  {
    clockperiod = 0;
    timestamp = Idmap.empty;
    nodelifes = Idmap.empty
  }

type alloc_amount = (Type.t, int) Hashtbl.t

let pp_alloc_amount ppf alloc_amount =
  let pp_binds ppf (t, size) =
    fprintf ppf "%a -> %a" Type.pp_t t pp_print_int size
  in
  pp_print_hashtbl pp_binds ppf alloc_amount ~pp_sep:pp_print_commaspace

let alloc_amount_empty () =
  Hashtbl.create 20

let alloc_amount_singleton t =
  let amount = alloc_amount_empty () in
  Hashtbl.add t 1 amount; amount

let merge_alloc_amount f amount1 amount2 =
  let amount2 = Hashtbl.copy amount2 in
  Hashtbl.fold (fun t val1 amount2 ->
      match Hashtbl.find_opt amount2 t with
      | Some(val2) -> Hashtbl.replace amount2 t (f val1 val2); amount2
      | None -> Hashtbl.add amount2 t val1; amount2
    ) amount1 amount2

let alloc_amount_union amount1 amount2 =
  merge_alloc_amount max amount1 amount2

let alloc_amount_sum amount1 amount2 =
  merge_alloc_amount (+) amount1 amount2

exception AllocAmountDiffError
let alloc_amount_diff amount1 amount2 =
  let amount1 = Hashtbl.copy amount1 in
  Hashtbl.fold (fun t val2 amount1 ->
      match Hashtbl.find_opt amount1 t with
      | Some val1 ->
         let sub = val1 - val2 in
         if sub < 0 then raise AllocAmountDiffError else
           Hashtbl.replace amount1 t sub; amount1
      | None -> raise AllocAmountDiffError
    ) amount2 amount1

type typedata =
  {
    enum_types : Type.t Hashset.t;
    singleton_types : Type.t Hashset.t;
    cons_tag : (Type.t, int Idmap.t) Hashtbl.t;
    nonenum_tid_defs : (string * typedef) list;
    tuple_types : (Type.t list) list;
    nonenum_tstate_defs : (string * xfrp_smodule) list;
  }

let typedata_empty () =
  {
    enum_types = Hashset.create 20;
    singleton_types = Hashset.create 20;
    cons_tag = Hashtbl.create 20;
    nonenum_tid_defs = [];
    tuple_types = [];
    nonenum_tstate_defs = [];
  }

let pp_typedata ppf typedata =

  let pp_typeset ppf typeset  =
    (pp_print_hashset Type.pp_t ~pp_sep:pp_print_commaspace) ppf typeset
  in

  let pp_cons_tag ppf cons_tag =
    let pp_single_map ppf (t, m) =
      fprintf ppf "%a -> @[<v>%a@]" Type.pp_t t (pp_idmap pp_print_int) m
    in
    (pp_print_hashtbl pp_single_map) ppf cons_tag
  in

  let list_printer pp_elem =
    pp_print_list pp_elem ~pp_sep:pp_print_commaspace
  in

  let pp_nonenum_tid_defs ppf nonenum_tid_defs =
    let pp_elem ppf (file, typedef) =
      fprintf ppf "%s:%s" file typedef.type_id
    in
    (list_printer pp_elem) ppf nonenum_tid_defs
  in

  let pp_tuple_types ppf tuple_types =
    let pp_elem ppf types =
      fprintf ppf "@[<h>(%a)@]" (list_printer Type.pp_t) types
    in
    (list_printer pp_elem) ppf tuple_types
  in

  let pp_nonenum_tstate_defs ppf nonenum_tstate_defs =
    let pp_elem ppf (file, xfrp_smodule) =
      fprintf ppf "%s:%s" file xfrp_smodule.smodule_id
    in
    (list_printer pp_elem) ppf nonenum_tstate_defs
  in

  fprintf ppf "@[<v>";
  fprintf ppf "enum_types:";
  fprintf ppf "@;<0 2>@[<hov> %a @]" pp_typeset typedata.enum_types;
  fprintf ppf "@,singleton_types:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_typeset typedata.singleton_types;
  fprintf ppf "@,cons_tag:";
  fprintf ppf "@;<0 2>@[<v>%a@]" pp_cons_tag typedata.cons_tag;
  fprintf ppf "@,nonenum_tid_defs:";
  fprintf ppf "@;<0 2>@[<hov>%a@]"
    pp_nonenum_tid_defs typedata.nonenum_tid_defs;
  fprintf ppf "@,tuple_types:";
  fprintf ppf "@;<0 2>@[<hov>%a@]" pp_tuple_types typedata.tuple_types;
  fprintf ppf "@,nonenum_tstate_defs:";
  fprintf ppf "@;<0 2>@[<hov>%a@]"
    pp_nonenum_tstate_defs typedata.nonenum_tstate_defs;
  fprintf ppf "@]"

type metainfo =
  {
    all_elements : all_elements;
    lifetime : lifetime;
    alloc_amount : alloc_amount;
    typedata : typedata;
  }
let pp_metainfo ppf metainfo =
  fprintf ppf "@[<v 2>metainfo:@;";
  fprintf ppf "@[<v>all_elements: {@;<0 2>";
  fprintf ppf "%a@;" pp_all_elements metainfo.all_elements;
  fprintf ppf "}@]";
  fprintf ppf "@[<v>lifetime: {@;<0 2>";
  fprintf ppf "%a@;" pp_lifetime metainfo.lifetime;
  fprintf ppf "}@]@;";
  fprintf ppf "@[<v>alloc_amount: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" pp_alloc_amount metainfo.alloc_amount;
  fprintf ppf "}@]";
  fprintf ppf "@[<v>typedata: {@;<0 2>";
  fprintf ppf "%a@;" pp_typedata metainfo.typedata;
  fprintf ppf "}@]";
  fprintf ppf "@]"

let metainfo_empty () =
  {
    all_elements = all_elements_empty;
    lifetime = lifetime_empty;
    alloc_amount = alloc_amount_empty ();
    typedata = typedata_empty ();
  }
