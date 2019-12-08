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
  check_dupe module_elem_id elems
  
let check_dupe_state elems =
  check_dupe state_elem_id elems

let check_dupe_smodule elems =
  check_dupe smodule_elem_id elems

let check_dupe_file elems =
  check_dupe xfrp_elem_id elems
