open Syntax
open Type

exception Error of string

(* Raise type error with given message `msg`. *)
let raise_err msg = raise (Error msg)

(* Raise type error with message. *)
let raise_err_pp fmt = Format.kasprintf (fun msg -> raise (Error msg)) fmt

(* Raise type imcompatible error with `t1` and `t2`. *)
let raise_imcompatible t1 t2 = raise_err_pp "%a and %a is not compatible" pp_t t1 pp_t t2

let raise_inaccessible id modev =
  raise_err_pp
    "%a is inaccessible when its mode is %a"
    pp_identifier
    id
    pp_identifier
    modev
;;

let raise_unknown id = raise_err_pp "Unknown: %a" pp_identifier id
let raise_recursive_type () = raise_err "Recursive type"

let raise_ionode_past_value id =
  raise_err_pp "Past value of %a is not allowed" pp_identifier id
;;

let raise_uninitialized id = raise_err_pp "Node %a is uninitialized" pp_identifier id
