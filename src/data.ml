(* A formatted program data *)
open Syntax
open Extension.Format
   
module Idmap = Map.Make(Identifier)

let pp_idmap pp_contents ppf idmap =
  fprintf ppf "@[<v>";
  Idmap.iter (fun id x ->
      fprintf ppf "%a -> %a@;" pp_identifier id pp_contents x
    ) idmap;
  fprintf ppf "@]"

type progdata =
  {
    module_id : identifier;
    module_in : (identifier * (literal option) * Type.typespec) Idmap.t;
    module_out : (identifier * (literal option) * Type.typespec) Idmap.t;
    module_use : identifier list;
    module_init : identifier * literal;
    cdef : constdef Idmap.t;
    tdef : typedef Idmap.t;
    fdef : fundef Idmap.t;
    sdef : statedef Idmap.t;
  }

let pp_progdata ppf data =
  fprintf ppf "@[<v 1>progdata:@;";
  fprintf ppf "id: %a@;" pp_identifier data.module_id;
  fprintf ppf "in: %a@;" (pp_idmap pp_nodedecl) data.module_in;
  fprintf ppf "out: %a@;" (pp_idmap pp_nodedecl) data.module_out;
  fprintf ppf "use: @[<v>%a@]@;" (pp_list_comma pp_identifier) data.module_use;
  let (c, v) = data.module_init in
  fprintf ppf "init %a %a@;" pp_identifier c pp_literal v;
  fprintf ppf "cdef: %a@;" (pp_idmap pp_constdef) data.cdef;
  fprintf ppf "tdef: %a@;" (pp_idmap pp_typedef) data.tdef;
  fprintf ppf "fdef: %a@;" (pp_idmap pp_fundef) data.fdef;
  fprintf ppf "sdef: %a@;" (pp_idmap pp_statedef) data.sdef;
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
  let (cdef, tdef, fdef, ndef) = separate_mdef m.module_defs in
  let state =
    {
      state_id = m.module_id; state_params = []; nodes = ndef; switch = ERetain
    }
  in
  {
    module_id = m.module_id;
    module_in = list_to_idmap m.module_in (fun (id, _,  _) -> id);
    module_out = list_to_idmap m.module_out (fun (id, _, _) -> id);
    module_use = m.module_use;
    module_init = (m.module_id, LUnit);
    cdef = list_to_idmap cdef (fun x -> let (id, _) = x.const_id in id);
    tdef = list_to_idmap tdef (fun x -> x.type_id);
    fdef = list_to_idmap fdef (fun x -> let (id, _) = x.fun_id in id);
    sdef = list_to_idmap [state] (fun x -> x.state_id);
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
  let (cdef, tdef, fdef, sdef) = separate_smdef m.smodule_defs in
  {
    module_id = m.smodule_id;
    module_in = list_to_idmap m.smodule_in (fun (id, _,  _) -> id);
    module_out = list_to_idmap m.smodule_out (fun (id, _, _) -> id);
    module_use = m.smodule_use;
    module_init = m.smodule_init;
    cdef = list_to_idmap cdef (fun x -> let (id, _) = x.const_id in id);
    tdef = list_to_idmap tdef (fun x -> x.type_id);
    fdef = list_to_idmap fdef (fun x -> let (id, _) = x.fun_id in id);
    sdef = list_to_idmap sdef (fun x -> x.state_id);
  }

(* convert AST to progdata *)  
let of_progdata = function
  | XfrpModule(d) -> module_to_data d
  | XfrpSModule(d) -> smodule_to_data d
                        
                        
