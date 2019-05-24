(* dependency analysis *)
open Syntax

(* collect all dependencies on `targets` in `expr` *)
let collect_dependencies targets expr =
  let rec visit_expr (ast, _) (acc : Idset.t) =
    match ast with
    | EUniOp(_, e1) -> visit_expr e1 acc
    | EBinOp(_, e1, e2) -> visit_expr e1 acc |> visit_expr e2
    | EVariant(_, e1) -> visit_expr e1 acc
    | ETuple(es) -> List.fold_right visit_expr es acc
    | EConst(_) | ERetain -> acc
    | EAnnot(_, ALast) -> acc (* ignore @last *)
    | EId(id) | EAnnot(id, _) ->
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

(* make dependency graph *)
let make_graph (dependencies : (identifier * Idset.t) list) =
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
let tsort graph =
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

(* dependencies of the function definition *)
let dependencies_of_fun targets def =
  let param_ids =
    List.map (fun (id, _) -> id) def.fun_params |> Idset.of_list
  in
  collect_dependencies (Idset.diff targets param_ids) def.fun_body

(* dependencies of the constant definition *)
let dependencies_of_const targets def =
  collect_dependencies targets def.const_body


(* topological sort on function / constant definitions *)
let tsort_const_fun cdefs fdefs =
  let targets =
    Idmap.fold (fun id _ s -> Idset.add id s) fdefs Idset.empty
    |> Idmap.fold (fun id _ s -> Idset.add id s) cdefs
  in
  let const_deps =
    Idmap.fold (fun id def deps ->
        (id, (dependencies_of_const targets def)) :: deps
      ) cdefs []
  in
  let const_and_fun_deps =
    Idmap.fold (fun id def deps ->
        (id, (dependencies_of_fun targets def)) :: deps
      ) fdefs const_deps
  in
  make_graph const_and_fun_deps |> tsort

(* dependencies of the node definition *)
let dependencies_of_node targets def =
  collect_dependencies targets def.node_body

(* dependencies of the node definition *)
let tsort_statenode sdef =
  let targets =
    List.fold_right (fun def s ->
        Idset.add (get_id def.node_id) s
      ) sdef.nodes Idset.empty
  in
  let deps =
    List.map (fun def ->
        ((get_id def.node_id), (dependencies_of_node targets def))
      ) sdef.nodes
  in
  make_graph deps |> tsort
