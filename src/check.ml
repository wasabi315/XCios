open Syntax

exception Error of string
   
(* Check name confliction. *)
let check_dupe (f_id : 'a -> identifier) (elems : 'a list) : unit =
  let _ =
    List.fold_right (fun elem set ->
        let id = f_id elem in
        if Idset.mem id set then
          let msg =
            Format.asprintf "Detect name confliction in %a" pp_identifier id
          in
          raise (Error msg)
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
  
let check_module_attr id = function
  | SharedNode ->
     let msg =
       Format.asprintf "Invalid node attribute for %a(shared)"
         pp_identifier id
     in
     raise (Error msg)
  | _ -> ()
  
let check_module_attr_node (node : node) : unit =
  check_module_attr node.node_id node.node_attr

let check_module_attr_newnode (newnode : newnode) : unit =
  List.iter (fun (attr, id, _) ->
      check_module_attr id attr
    ) newnode.newnode_binds  
  
  
  
