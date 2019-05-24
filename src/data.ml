(* A formatted program data *)
open Syntax
open Extension.Format

let pp_idmap pp_contents ppf idmap =
  fprintf ppf "@[<v>";
  Idmap.iter (fun id x ->
      fprintf ppf "%a -> %a@;" pp_identifier id pp_contents x
    ) idmap;
  fprintf ppf "@]"

type progdata =
  {
    module_id : identifier;
    module_in : (identifier * (literal option) * Type.t) Idmap.t;
    module_out : (identifier * (literal option) * Type.t) Idmap.t;
    module_use : identifier list;
    module_init : identifier * literal;
    cdefs : constdef Idmap.t;
    tdefs : typedef Idmap.t;
    fdefs : fundef Idmap.t;
    sdefs : statedef Idmap.t;
  }

let pp_progdata ppf data =
  fprintf ppf "@[<v 1>progdata:@;";
  fprintf ppf "id: %a@;" pp_identifier data.module_id;
  fprintf ppf "in: %a@;" (pp_idmap pp_nodedecl) data.module_in;
  fprintf ppf "out: %a@;" (pp_idmap pp_nodedecl) data.module_out;
  fprintf ppf "use: @[<v>%a@]@;" (pp_list_comma pp_identifier) data.module_use;
  let (c, v) = data.module_init in
  fprintf ppf "init %a %a@;" pp_identifier c pp_literal v;
  fprintf ppf "cdefs: %a@;" (pp_idmap pp_constdef) data.cdefs;
  fprintf ppf "tdefs: %a@;" (pp_idmap pp_typedef) data.tdefs;
  fprintf ppf "fdefs: %a@;" (pp_idmap pp_fundef) data.fdefs;
  fprintf ppf "sdefs: %a@;" (pp_idmap pp_statedef) data.sdefs;
  fprintf ppf "@]"

(* convert list to Idmap.t *)
let list_to_idmap (lst : 'a list) (id_f : 'a -> identifier) =
  List.fold_left (fun m x -> Idmap.add (id_f x) x m) Idmap.empty lst

(* separate module_defs *)
let separate_mdef defs =
  List.fold_left (fun (cs, ts, fs, ns) def ->
      match def with
      | MConstDef(d) -> (d::cs, ts, fs, ns)
      | MTypeDef(d) -> (cs, d::ts, fs, ns)
      | MFunDef(d) -> (cs, ts, d::fs, ns)
      | MNodeDef(d) -> (cs, ts, fs, d::ns)
    ) ([], [], [], []) defs

(* convert XfrpModule to progdata *)
let module_to_data m =
  let (cdefs, tdefs, fdefs, ndefs) = separate_mdef m.module_defs in
  let state =
    {
      state_id = m.module_id;
      state_params = [];
      nodes = ndefs;
      switch = (ERetain, TEmpty)
    }
  in
  {
    module_id = m.module_id;
    module_in = list_to_idmap m.module_in (fun (id, _,  _) -> id);
    module_out = list_to_idmap m.module_out (fun (id, _, _) -> id);
    module_use = m.module_use;
    module_init = (m.module_id, (LUnit, TEmpty));
    cdefs = list_to_idmap cdefs (fun x -> get_id x.const_id);
    tdefs = list_to_idmap tdefs (fun x -> x.type_id);
    fdefs = list_to_idmap fdefs (fun x -> get_id x.fun_id);
    sdefs = list_to_idmap [state] (fun x -> x.state_id);
  }

(* separate smodule_defs *)
let separate_smdef defs =
  List.fold_left (fun (cs, ts, fs, ss) def ->
      match def with
      | SMConstDef(d) -> (d::cs, ts, fs, ss)
      | SMTypeDef(d) -> (cs, d::ts, fs, ss)
      | SMFunDef(d) -> (cs, ts, d::fs, ss)
      | SMStateDef(d) -> (cs, ts, fs, d::ss)
    ) ([], [], [], []) defs

(* convert XfrpSModule to progdata *)
let smodule_to_data m =
  let (cdefs, tdefs, fdefs, sdefs) = separate_smdef m.smodule_defs in
  {
    module_id = m.smodule_id;
    module_in = list_to_idmap m.smodule_in (fun (id, _,  _) -> id);
    module_out = list_to_idmap m.smodule_out (fun (id, _, _) -> id);
    module_use = m.smodule_use;
    module_init = m.smodule_init;
    cdefs = list_to_idmap cdefs (fun x -> get_id x.const_id);
    tdefs = list_to_idmap tdefs (fun x -> x.type_id);
    fdefs = list_to_idmap fdefs (fun x -> get_id x.fun_id);
    sdefs = list_to_idmap sdefs (fun x -> x.state_id);
  }

(* convert AST to progdata *)
let of_progdata = function
  | XfrpModule(d) -> module_to_data d
  | XfrpSModule(d) -> smodule_to_data d
