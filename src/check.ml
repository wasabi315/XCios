open Syntax

(* Check name confliction. *)
let check_dupe (f_id : 'a -> identifier) (elems : 'a list) : unit =
  let _ =
    List.fold_right (fun elem set ->
        let id = f_id elem in
        if Idset.mem id set then
          raise (Env.NameConflict id)
        else Idset.add id set
      ) elems Idset.empty
  in
  ()

let check_dupe_module elems =
  check_dupe (fun elem ->
      match elem with
      | MConst(d) -> d.const_id
      | MNode(d) -> d.node_id
      | MSubmodule(d) -> d.submodule_id
    ) elems
  
let check_dupe_state elems =
  check_dupe (fun elem ->
      match elem with
      | SConst(d) -> d.const_id
      | SNode(d) -> d.node_id
      | SSubmodule(d) -> d.submodule_id
    ) elems

let check_dupe_smodule elems =
  check_dupe (fun elem ->
      match elem with
      | SMConst(d) -> d.const_id
      | SMState(d) -> d.state_id
    ) elems

let check_dupe_file elems =
  check_dupe (fun elem ->
      match elem with
      | XFRPType(d) -> d.type_id
      | XFRPConst(d) -> d.const_id
      | XFRPFun(d) -> d.fun_id
      | XFRPModule(d) -> d.module_id
      | XFRPSModule(d) -> d.smodule_id
    ) elems
