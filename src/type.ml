(* Type definitions for xfrp types *)
open Extension.Format

type t =
  | TBool | TInt | TFloat | TUnit
  | TState of string * string
  | TId of string * string
  | TTuple of t list
  | TVar of tvar ref
  | TEmpty (* dummy for optional typespec *)
and tvar =
  | TVGeneric of int
  | TVFree of int * int (* id + level *)
  | TVBound of t

let rec pp_t ppf = function
  | TBool -> pp_print_string ppf "<type Bool>"
  | TInt -> pp_print_string ppf "<type Int>"
  | TFloat -> pp_print_string ppf "<type Float>"
  | TUnit -> pp_print_string ppf "<type Unit>"
  | TState(_, _) -> pp_print_string ppf "<type State>"
  | TId(file, t) -> fprintf ppf "<type Id(%a:%a)>"
                      pp_print_string file pp_print_string t
  | TTuple(ts) -> fprintf ppf "<type (@[<h>%a@])>"
                    (pp_list_comma pp_t) ts
  | TVar({contents = tvar}) -> fprintf ppf "<typevar %a>" pp_tvar tvar
  | TEmpty -> pp_print_string ppf "<type _>"
and pp_tvar ppf = function
  | TVGeneric(id) -> fprintf ppf "<tvgen %d>" id
  | TVFree(id, lv) -> fprintf ppf "<tvfree %d : level %d>"  id lv
  | TVBound(t) -> fprintf ppf "<tvbound : %a>" pp_t t

let tvar_counter = ref 0

(* generate fresh free variable *)
let gen_tvar_free level =
  tvar_counter := !tvar_counter + 1;
  let tvar = TVFree(!tvar_counter, level) in TVar(ref tvar)

(* generate fresh generic variable *)
let gen_tvar_generic () =
  tvar_counter := !tvar_counter + 1;
  let tvar = TVGeneric(!tvar_counter) in TVar(ref tvar)
