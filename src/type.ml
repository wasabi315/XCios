(* Type definitions for xfrp types *)
open Extension.Format

type typespec =
  | TBool | TInt | TFloat | TUnit
  | TId of string
  | TTuple of typespec list
  | TVar of typespec option ref
  | TFun of typespec list * typespec

let rec pp_typespec ppf = function
  | TBool -> pp_print_string ppf "<type Bool>"
  | TInt -> pp_print_string ppf "<type Int>"
  | TFloat -> pp_print_string ppf "<type Float>"
  | TUnit -> pp_print_string ppf "<type unit>"
  | TId(t) -> fprintf ppf "<type %a>" pp_print_string t
  | TTuple(ts) -> fprintf ppf "<type (@[%a@])>"
                    (pp_list_comma pp_typespec) ts
  | TVar({contents = Some(t)}) -> fprintf ppf "<typevar %a>" pp_typespec t
  | TVar({contents = None}) -> pp_print_string ppf "<typevar _>"
  | TFun(params, res_t) -> fprintf ppf "<fun @[(@[%a@])@ -> %a@]>"
                             (pp_list_comma pp_typespec) params
                             pp_typespec res_t

(* generate new type variable *)                         
let gen_tvar () = TVar(ref None)                             
