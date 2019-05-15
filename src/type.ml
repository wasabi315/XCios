(* Type definitions for xfrp types *)
open Extension.Format

type t =
  | TBool | TInt | TFloat | TUnit
  | TId of string
  | TTuple of t list
  | TVar of tvar ref
  | TFun of t list * t
and tvar =
  | TVGeneric of int
  | TVFree of int * int (* id + level *)
  | TVBound of t
  | TVDummy (* dummy for optional typespec *)

let rec pp_t ppf = function
  | TBool -> pp_print_string ppf "<type Bool>"
  | TInt -> pp_print_string ppf "<type Int>"
  | TFloat -> pp_print_string ppf "<type Float>"
  | TUnit -> pp_print_string ppf "<type unit>"
  | TId(t) -> fprintf ppf "<type %a>" pp_print_string t
  | TTuple(ts) -> fprintf ppf "<type (@[%a@])>"
                    (pp_list_comma pp_t) ts
  | TVar({contents = tvar}) -> fprintf ppf "<typevar %a>" pp_tvar tvar
  | TFun(params, res_t) -> fprintf ppf "<fun @[(@[%a@])@ -> %a@]>"
                             (pp_list_comma pp_t) params
                             pp_t res_t
and pp_tvar ppf = function
  | TVGeneric(id) -> fprintf ppf "<tvgen %d>" id
  | TVFree(id, lv) -> fprintf ppf "<tvfree %d : level %d>"  id lv
  | TVBound(t) -> fprintf ppf "<tvbound : %a>" pp_t t
  | TVDummy -> pp_print_string ppf "<tvdummy>"

(* generate dummy variable *)
let gen_tvar_dummy () = TVar(ref TVDummy)

let counter = ref 0

(* generate fresh free variable *)
let gen_tvar_free level =
  counter := !counter + 1;
  let tvar = TVFree(level, !counter) in TVar(ref tvar)

(* generate fresh generic variable *)
let gen_tvar_generic () =
  counter := !counter + 1;
  let tvar = TVGeneric(!counter) in TVar(ref tvar)

