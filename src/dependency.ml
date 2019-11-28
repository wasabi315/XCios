(* dependency analysis *)
open Syntax

type graph = Idset.t Idmap.t

(* make dependency graph *)
let make_graph (dependencies : (identifier * Idset.t) list) : graph =
  let add_edge (dst, srcs) graph =
    let add_edge1 src_adjs =
      match src_adjs with
      | None -> assert false
      | Some(dsts) -> Some(Idset.add dst dsts)
    in
    Idset.fold (fun src g ->
        Idmap.update src add_edge1 g
      ) srcs graph
  in
  let nodes =
    List.map (fun (id, _) -> id) dependencies
    |> Idset.of_list
  in
  let empty_graph =
    Idset.fold (fun n g->
        Idmap.add n Idset.empty g
      ) nodes Idmap.empty
  in
  List.fold_right add_edge dependencies empty_graph

type nodestate = Unvisited | Visiting |Visited
exception Cycle

(* topological sort *)
let tsort (graph : graph) : identifier list =
  let nodes =
    List.map (fun (id, _) -> id) (Idmap.bindings graph)
    |> Idset.of_list
  in
  let init_state =
    Idset.fold (fun id s ->
        Idmap.add id Unvisited s
      )  nodes Idmap.empty
  in
  let rec visit node (st, res)=
    match Idmap.find node st with
    | Unvisited ->
       let st_enter = Idmap.add node Visiting st in
       let adj = Idmap.find node graph in
       let (st', res') = Idset.fold visit adj (st_enter, res) in
       let st_exit = Idmap.add node Visited st' in
       (st_exit, node::res')
    | Visiting -> raise Cycle
    | Visited -> (st, res)
  in
  let (_, res) = Idset.fold visit nodes (init_state, []) in
  res

(*----- collect type ids contained in `targets` -----*)

let find_tids_typedef targets def =
  let rec extract_id = function
    | TBool | TInt | TFloat | TUnit ->
       Idset.empty
    | TId(name) ->
       if Idset.mem name targets then
         Idset.add name res
       else res
    | TTuple(ts) ->
       List.map extract_id ts
       |> List.fold_left Idset.union Idset.empty
    | _ -> assert false
  in
  List.map (fun (_, t) -> extract_id t) def.variant_defs
  |> List.fold_right Idset.union Idset.empty

(*----- collect ids contained in `targets` -----*)

let find_ids_expr targets expr =
  let rec visit_expr (ast, _) (acc : Idset.t) =
    match ast with
    | EUniOp(_, e1) -> visit_expr e1 acc
    | EBinOp(_, e1, e2) -> visit_expr e1 acc |> visit_expr e2
    | EVariant(_, e1) -> visit_expr e1 acc
    | ETuple(es) -> List.fold_right visit_expr es acc
    | EConst(_) | ERetain -> acc
    | EAnnot(_, ALast) -> acc (* ignore @last *)
    | EId(id) | EAnnot(id, _) | EDot(id, _) ->
       if Idset.mem id targets then Idset.add id acc else acc
    | EFuncall(fid, args) ->
       (if Idset.mem fid targets then Idset.add fid acc else acc)
       |> List.fold_right visit_expr args
    | EIf(etest, ethen, eelse) ->
       visit_expr etest acc
       |> visit_expr ethen
       |> visit_expr eelse
    | ELet(binders, body) ->
       List.fold_right (fun { binder_body = e; _ } a ->
           visit_expr e a
         ) binders acc
       |> visit_expr body
    | ECase(e, branchs) ->
       visit_expr e acc
       |> List.fold_right (fun { branch_body = e; _ } a ->
              visit_expr e a
            ) branchs
  in
  visit_expr expr Idset.empty

let find_ids_fundef targets def =
  let param_ids =
    List.map (fun (id, _) -> id) def.fun_params |> Idset.of_list
  in
  find_ids_expr (Idset.diff targets param_ids) def.fun_body

let find_ids_constdef targets def =
  find_names_const targets def.const_body

let find_ids_submodule targets def =
  let all_exprs = def.submodule_margs @ def.submodule_inputs in
  List.fold_right (fun arg s ->
      Idset.union (find_ids_expr targets arg) s
    ) all_exprs Idset.empty

(*----- collect module ids contained in `targets` -----*)

let find_mids_moduledef targets def =
  List.fold_left (fun res elem ->
      match elem with
      | MSubmodule(d) ->
         if Idset.mem d.submodule_module targets then
           Idset.add d.submodule_module res
         else res
      | _ -> res
    ) Idset.empty def.module_elems

let find_mids_smoduledef targets def =
  let add_state_mids state mids =
    List.fold_left (fun mids elem ->
        match elem with
        | SSubmodule(d) ->
           if Idset.mem d.submodule_module targets then
             Idset.add d.submodule_module mids
           else mids
        | _ -> mids
      ) mids state.state_elems
  in
  List.fold_left (fun mids elem ->
      match elem with
      | SMState(d) -> add_state_mids d mids
      | _ -> mids
    ) Idset.empty def.smodule_elems

(* sort type definitions *)
let tsort_types (tdefs : typedef Idmap.t) =
  let targets =
    Idmap.fold (fun id _ s -> Idset.add id s) tdefs Idset.empty
  in
  let tdeps =
    Idmap.fold (fun id tdef deps ->
        (id, (find_tids_typedef targets tdef)) :: deps
      ) tdefs []
  in
  make_graph tdeps |> tsort

(* sort function / constant definitions *)
let tsort_materials (cdefs : constdef Idmap.t) (fdefs : fundef Idmap.t) =
  let targets =
    Idmap.fold (fun id _ s -> Idset.add id s) fdefs Idset.empty
    |> Idmap.fold (fun id _ s -> Idset.add id s) cdefs
  in
  let const_deps =
    Idmap.fold (fun id cdef deps ->
        (id, (find_ids_constdef targets cdef)) :: deps
      ) cdefs []
  in
  let fun_deps =
    Idmap.fold (fun id fdef deps ->
        (id, (find_ids_fundef targets fdef)) :: deps
      ) fdefs []
  in
  make_graph (const_deps @ fun_deps) |> tsort

(* sort constant definitions *)
let tsort_consts (cdefs : constdef Idmap.t) =
  tsort_materials cdefs Idmap.empty

(* sort module / switchmodule definitions *)
let tsort_modules (mdefs : xfrp_module Idmap.t) (smdefs : xfrp_smodule Idmap.t) =
  let targets =
    Idmap.fold (fun id _ s -> Idset.add id s) mdefs Idset.empty
    |> Idmap.fold (fun id _ s -> Idset.add id s) smdefs
  in
  let module_deps =
    Idmap.fold (fun id mdef deps ->
        (id, (find_mids_moduledef targets mdef)) :: deps
      ) mdefs []
  in
  let smodule_deps =
    Idmap.fold (fun id smdef deps ->
        (id, (find_mids_smoduledef targets smdef)) :: deps
      ) smdefs []
  in
  make_graph (module_deps @ smodule_deps) |> tsort

(* calculate state / module update order *)
let get_update_ord  (ns : node Idmap.t) (subms : submodule Idmap.t) =
  let targets =
    Idmap.fold (fun id _ s -> Idset.add id s) ns Idset.empty
    |> Idmap.fold (fun id _ s -> Idset.add id s) subms
  in
  let node_deps =
    Idmap.fold (fun id n deps ->
        (id, (find_ids_expr targets n.node_body) :: deps)
      ) ns []
  in
  let submodule_deps =
    Idmap.fold (fun id subm deps ->
        (id, (find_ids_submodule targets subm)) :: deps
      ) subms []
  in
  make_graph (node_deps @ submodule_deps) |> tsort
