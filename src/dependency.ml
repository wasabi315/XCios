(* dependency analysis *)
open Syntax

module Graph = Map.Make(Identifier)
module Nodes = Set.Make(Identifier)

(* collect all dependencies on nodes in expr *)             
let collect_dependencies nodes expr = 
  let rec visit_expr expr (acc : Nodes.t) =
    match expr with
    | EUniOp(_, e1) -> visit_expr e1 acc
    | EBinOp(_, e1, e2) -> visit_expr e1 acc |> visit_expr e2 
    | EVariant(_, e1) -> visit_expr e1 acc
    | ETuple(es) -> List.fold_right visit_expr es acc
    | EConst(_) | ERetain -> acc
    | EAnnot(_, ALast) -> acc (* ignore @last *)
    | EId(id) | EAnnot(id, _) ->
       if Nodes.mem id nodes then Nodes.add id acc else acc
    | EFuncall(fid, args) ->
       (if Nodes.mem fid nodes then Nodes.add fid acc else acc)
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
  visit_expr expr Nodes.empty

(* make dependency graph from identifier * expr list *)  
let make_graph id_and_exprs =
  let add_edge dst srcs graph =
    let add_edge1 src_adjs =
      match src_adjs with
      | None -> assert false
      | Some(dsts) -> Some(Nodes.add dst dsts)
    in
    Nodes.fold (fun src g ->
        Graph.update src add_edge1 g
      ) srcs graph
  in
  let nodes =
    List.map (fun (id, _) -> id) id_and_exprs
    |> Nodes.of_list
  in
  Nodes.fold (fun n g->
      Graph.add n Nodes.empty g
    ) nodes Graph.empty
  |> List.fold_right (fun (dst, e) g ->
         add_edge dst (collect_dependencies nodes e) g
       ) id_and_exprs
  
type nodestate = Unvisited | Visiting |Visited 
module TSortState = Map.Make(Identifier)
exception Cycle

(* topological sort on dependency graph of expression *)        
let tsort_dependency id_and_exprs =
  let graph = make_graph id_and_exprs in
  let nodes =
    List.map (fun (id, _) -> id) (Graph.bindings graph)
    |> Nodes.of_list
  in
  let init_state = 
    Nodes.fold (fun id s ->
        TSortState.add id Unvisited s
      )  nodes TSortState.empty
  in
  let rec visit node (st, res)=
    match TSortState.find node st with
    | Unvisited ->
       let st_enter = TSortState.add node Visiting st in
       let adj = Graph.find node graph in
       let (st', res') = Nodes.fold visit adj (st_enter, res) in
       let st_exit = TSortState.add node Visited st' in 
       (st_exit, node::res')
    | Visiting -> raise Cycle
    | Visited -> (st, res)
  in
  let (_, res) = Nodes.fold visit nodes (init_state, []) in
  res
