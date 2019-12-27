open Syntax
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
  let binds =
    Hashtbl.fold (fun t size binds ->
        (t, size) :: binds
      ) alloc_amount []
  in
  pp_list_comma pp_binds ppf binds

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

type metainfo =
  {
    file_ord : string list;
    used_materials : Idset.t;
    lifetime : lifetime;
    alloc_amount : alloc_amount;
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
  fprintf ppf "}@]@;";
  fprintf ppf "@[<v>alloc_amount: {@;<0 2>";
  fprintf ppf "@[<hov>%a@]@;" pp_alloc_amount metainfo.alloc_amount;
  fprintf ppf "}@]@]"

let metainfo_empty () =
  {
    file_ord = [];
    used_materials = Idset.empty;
    lifetime = lifetime_empty;
    alloc_amount = alloc_amount_empty ()
  }

