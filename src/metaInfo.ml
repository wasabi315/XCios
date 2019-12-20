open Syntax
open Extension.Format

type nodelife =
  {
    curref_life  : int Idmap.t;
    lastref_life : int Idmap.t;
  }
  
let pp_nodelife ppf nodelife =
  fprintf ppf "@[<v>curref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" (pp_idmap pp_print_int) nodelife.curref_life;
  fprintf ppf "lastref_life:@;<0 2>";
  fprintf ppf "@[<hov>%a@]@]" (pp_idmap pp_print_int) nodelife.lastref_life

let nodelife_empty = { curref_life = Idmap.empty; lastref_life = Idmap.empty }
                   
type lifetime =
  {
    timestamp : int Idmap.t;
    nodelifes : nodelife Idmap.t;
  }

module Intmap = Map.Make(struct type t = int let compare = compare end)

let pp_intmap pp_contents ppf intmap =
  let pp_binds ppf (i, x) =
    fprintf ppf "%a : %a" pp_print_int i pp_contents x
  in
  pp_list_comma pp_binds ppf (Intmap.to_seq intmap |> List.of_seq)

let rev_timestamp timestamp =
  let update id time revmap =
    Intmap.update time (function
        | Some s -> Some (Idset.add id s)
        | None -> Some (Idset.singleton id)
      ) revmap
  in
  Idmap.fold update timestamp Intmap.empty
  
let pp_lifetime ppf lifetime =
  let pp_timetable_row ppf ids =
    fprintf ppf "@[<hov>%a@]" pp_idset ids
  in
  fprintf ppf "@[<v>timestamp:@;<0 2>";
  fprintf ppf "@[<v>%a@]@;"
    (pp_intmap pp_timetable_row) (rev_timestamp lifetime.timestamp);
  fprintf ppf "nodelifes:@;<0 2>";
  fprintf ppf "@[<v>%a@]@]" (pp_idmap pp_nodelife) lifetime.nodelifes

let lifetime_empty = { timestamp = Idmap.empty; nodelifes = Idmap.empty }

type alloc_amount = (Type.t int) Hashtbl.t

let alloc_amount_empty = (Hashtbl.create 20)

let alloc_amount_singleton t =
  Hashtbl.add t 1 alloc_amount_empty

let merge_alloc_amount f amount1 amount2 =
  Hashtbl.fold (fun t val1 amount2 ->
      match Hashtbl.find_opt amount2 t with
      | Some(val2) -> Hashtbl.replace amount2 t (f val1 val2)
      | None -> Hashtbl.add amount2 t val1
    ) amount1 amount2
  
let alloc_amount_union amount1 amount2 =
  merge_alloc_amount max amount1 amount2

let alloc_amount_sum amount1 amount2 =
  merge_alloc_amount (+) amount1 amount2
                   
type metainfo =
  {
    file_ord : string list;
    used_materials : Idset.t;
    lifetime : lifetime;
  }
let pp_metainfo ppf metainfo =
  fprintf ppf "@[<v 2>metainfo:@;";
  fprintf ppf "@[<v>file_ord: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" (pp_list_comma pp_identifier) metainfo.file_ord;
  fprintf ppf "}@]@;";
  fprintf ppf "@[<v>used_materials: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" pp_idset metainfo.used_materials;
  fprintf ppf "}@]@;";
  fprintf ppf "@[<v>lifetime: {@;<0 2>";
  fprintf ppf "%a@;" pp_lifetime metainfo.lifetime;
  fprintf ppf "}@]@]"

let empty_metainfo =
  {
    file_ord = [];
    used_materials = Idset.empty;
    lifetime = empty_lifetime;
  }
    
