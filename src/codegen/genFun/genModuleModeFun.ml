open Extension.Format
open Syntax
open Type
open CodegenUtil
open MetaInfo

let define_module_mode_calc_fun metainfo (file, modul) fun_writers =
  let newnodes = modul.module_newnodes in
  let mode_annot = modul.module_mode_annot in
  fun_writers
;;

let define_smodule_mode_calc_fun metainfo (file, modul) fun_writers = fun_writers
