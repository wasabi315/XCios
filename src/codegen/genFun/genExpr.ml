open Extension
open Extension.Format
open Syntax
open Type
open MetaInfo
open CodegenUtil

let tmpvar_counter = ref 0

let make_tmpvar_name () =
  tmpvar_counter := !tmpvar_counter + 1;
  let tmpvar_tag = !tmpvar_counter in
  asprintf "_tmpvar%d" tmpvar_tag
;;

type codegen_ctx =
  | CTXGlobalConst
  | CTXModuleConst
  | CTXModuleNode of nattr * string (* attribute, node id *)
  | CTXModuleNewnodeIn
  | CTXStateConst of string (* state_id *)
  | CTXStateNode of string * nattr * string (* state_id, attribute, node_id *)
  | CTXStateNewnodeIn of string (* state_id *)
  | CTXSwitch of string (* state_id *)

let gen_literal ppf = function
  | LTrue -> pp_print_string ppf "1"
  | LFalse -> pp_print_string ppf "0"
  | LInt n -> pp_print_int ppf n
  | LFloat n -> pp_print_float ppf n
  | LUnit -> assert false
;;

let get_pattern_conds_binds metainfo gen_target pattern =
  let enum_types = metainfo.typedata.enum_types in
  let singleton_types = metainfo.typedata.singleton_types in
  let cons_tag = metainfo.typedata.cons_tag in
  let tstate_param_ids = metainfo.typedata.tstate_param_ids in
  let rec rec_f gen_target (ast, tpat) (conds, binds) =
    let f_id id =
      let gen_binds ppf () =
        fprintf
          ppf
          "%a %a = %a;"
          (gen_value_type metainfo)
          tpat
          pp_print_string
          id
          gen_target
          ()
      in
      conds, gen_binds :: binds
    in
    let f_const literal =
      let gen_cond ppf () = fprintf ppf "%a == %a" gen_target () gen_literal literal in
      gen_cond :: conds, binds
    in
    let f_tuple subpats =
      let patterns_with_position = List.mapi (fun pos pattern -> pattern, pos) subpats in
      List.fold_left
        (fun conds_binds (pattern, pos) ->
          let gen_subtarget ppf () =
            fprintf ppf "%a->member%a" gen_target () pp_print_int pos
          in
          rec_f gen_subtarget pattern conds_binds)
        (conds, binds)
        patterns_with_position
    in
    let f_valuecons cons_id subpat =
      let conds =
        if Hashset.mem singleton_types tpat
        then conds
        else (
          let tag = Hashtbl.find cons_tag tpat |> Idmap.find cons_id in
          let gen_cond ppf () =
            if Hashset.mem enum_types tpat
            then fprintf ppf "%a == %a" gen_target () pp_print_int tag
            else fprintf ppf "%a->tag == %a" gen_target () pp_print_int tag
          in
          gen_cond :: conds)
      in
      let _, tsubpat = subpat in
      match tsubpat with
      | TUnit -> conds, binds
      | TBool | TInt | TFloat | TId _ | TTuple _ ->
        let gen_subtarget ppf () =
          fprintf ppf "%a->value.%a" gen_target () pp_print_string cons_id
        in
        rec_f gen_subtarget subpat (conds, binds)
      | _ -> assert false
    in
    let f_statecons cons_id subpat =
      let conds =
        if Hashset.mem singleton_types tpat
        then conds
        else (
          let tag = Hashtbl.find cons_tag tpat |> Idmap.find cons_id in
          let gen_cond ppf () =
            fprintf ppf "%a->tag == %a" gen_target () pp_print_int tag
          in
          gen_cond :: conds)
      in
      let param_ids = Hashtbl.find tstate_param_ids tpat |> Idmap.find cons_id in
      match param_ids with
      | [] -> conds, binds
      | [ param_id ] ->
        let gen_subtarget ppf () =
          fprintf
            ppf
            "%a->params.%a.%a"
            gen_target
            ()
            pp_print_string
            cons_id
            pp_print_string
            param_id
        in
        rec_f gen_subtarget subpat (conds, binds)
      | param_ids ->
        List.fold_left
          (fun (conds, binds) param_id ->
            let gen_subtarget ppf () =
              fprintf
                ppf
                "%a->params.%a.%a"
                gen_target
                ()
                pp_print_string
                cons_id
                pp_print_string
                param_id
            in
            rec_f gen_subtarget subpat (conds, binds))
          (conds, binds)
          param_ids
    in
    match ast with
    | PWild -> conds, binds
    | PId id -> f_id id
    | PConst literal -> f_const literal
    | PTuple subpats -> f_tuple subpats
    | PVariant (idref, subpat) ->
      let cons_id, idinfo = idref in
      (match idinfo with
       | ValueCons _ -> f_valuecons cons_id subpat
       | StateCons _ -> f_statecons cons_id subpat
       | _ -> assert false)
  in
  let conds, binds = rec_f gen_target pattern ([], []) in
  List.rev conds, List.rev binds
;;

(* return writers for code body and writer for return expression *)
let get_expr_generator metainfo codegen_ctx expr : writer list * writer =
  let rec rec_f (ast, tast) body_writers =
    let f_uni_op op e1 =
      let body_writers, gen_e1 = rec_f e1 body_writers in
      let gen_op ppf () =
        pp_print_string
          ppf
          (match op with
           | UNot -> "!"
           | UInv -> "~"
           | UPlus | UFPlus -> "+"
           | UMinus | UFMinus -> "-")
      in
      let gen_expr ppf () = fprintf ppf "(%a %a)" gen_op () gen_e1 () in
      body_writers, gen_expr
    in
    let f_bin_op op e1 e2 =
      let body_writers, gen_e1 = rec_f e1 body_writers in
      let body_writers, gen_e2 = rec_f e2 body_writers in
      let gen_op ppf () =
        pp_print_string
          ppf
          (match op with
           | BAdd | BFAdd -> "+"
           | BSub | BFSub -> "-"
           | BMul | BFMul -> "*"
           | BDiv | BFDiv -> "/"
           | BMod -> "%"
           | BShl -> "<<"
           | BShr -> ">>"
           | BLt | BFLt -> "<"
           | BLeq | BFLeq -> "<="
           | BGt | BFGt -> ">"
           | BGeq | BFGeq -> ">="
           | BEq -> "=="
           | BNeq -> "!="
           | BLand -> "&&"
           | BLor -> "||"
           | BAnd -> "&"
           | BOr -> "|"
           | BXor -> "^")
      in
      let gen_expr ppf () = fprintf ppf "(%a %a %a)" gen_e1 () gen_op () gen_e2 () in
      body_writers, gen_expr
    in
    let f_variant idref value =
      let cons_id, idinfo = idref in
      let _, vtype = value in
      let body_writers, gen_value =
        match vtype with
        | TUnit -> body_writers, pp_none
        | TBool | TInt | TFloat | TId _ | TTuple _ -> rec_f value body_writers
        | _ -> assert false
      in
      let f_valuecons file type_id =
        let enum_types = metainfo.typedata.enum_types in
        if Hashset.mem enum_types tast
        then (
          let tag_table = Hashtbl.find metainfo.typedata.cons_tag tast in
          let cons_tag = Idmap.find cons_id tag_table in
          let gen_expr ppf () = pp_print_int ppf cons_tag in
          body_writers, gen_expr)
        else (
          let gen_expr ppf () =
            fprintf ppf "%a(%a)" gen_tid_consname (file, type_id, cons_id) gen_value ()
          in
          body_writers, gen_expr)
      in
      let f_statecons file module_id tvalue =
        let body_writers, gen_args =
          match tvalue with
          | TUnit | TBool | TInt | TFloat | TId _ -> body_writers, gen_value
          | TTuple ts ->
            let varname = make_tmpvar_name () in
            let gen_prepare_args ppf () =
              fprintf
                ppf
                "%a %a = %a;"
                (gen_value_type metainfo)
                tvalue
                pp_print_string
                varname
                gen_value
                ()
            in
            let tuple_size = List.length ts in
            let tuple_members = List.init tuple_size (fun i -> asprintf "member%d" i) in
            let gen_args ppf () =
              pp_print_list pp_print_string ppf tuple_members ~pp_sep:pp_print_commaspace
            in
            gen_prepare_args :: body_writers, gen_args
          | _ -> assert false
        in
        let gen_expr ppf () =
          fprintf
            ppf
            "%a(@[<hov>%a@])"
            gen_tstate_consname
            (file, module_id, cons_id)
            gen_args
            ()
        in
        body_writers, gen_expr
      in
      match idinfo with
      | ValueCons (file, _, TId (_, type_id)) -> f_valuecons file type_id
      | StateCons (file, module_id, tvalue) -> f_statecons file module_id tvalue
      | _ -> assert false
    in
    let f_tuple es =
      let body_writers, generators =
        List.fold_left
          (fun (body_writers, generators) expr ->
            let body_writers, gen_expr = rec_f expr body_writers in
            body_writers, gen_expr :: generators)
          (body_writers, [])
          es
      in
      let generators = List.rev generators in
      let _, type_list = List.split es in
      let gen_expr ppf () =
        fprintf
          ppf
          "%a(@[<hov>%a@])"
          gen_ttuple_consname
          type_list
          (exec_all_writers () ~pp_sep:pp_print_commaspace)
          generators
      in
      body_writers, gen_expr
    in
    let f_const literal = body_writers, fun ppf () -> gen_literal ppf literal in
    let f_retain () =
      let gen_expr ppf () =
        let f_module_node nattr node_id =
          match nattr with
          | OutputNode | NormalNode -> fprintf ppf "memory->%s[!current_side]" node_id
          | _ -> assert false
        in
        let f_state_node state_id nattr node_id =
          match nattr with
          | OutputNode | SharedNode -> fprintf ppf "memory->%s[!current_side]" node_id
          | NormalNode ->
            fprintf ppf "memory->statebody.%s.%s[!current_side]" state_id node_id
          | _ -> assert false
        in
        match codegen_ctx with
        | CTXGlobalConst
        | CTXModuleConst
        | CTXModuleNewnodeIn
        | CTXStateConst _
        | CTXStateNewnodeIn _ -> assert false
        | CTXModuleNode (nattr, node_id) -> f_module_node nattr node_id
        | CTXStateNode (state_id, nattr, node_id) -> f_state_node state_id nattr node_id
        | CTXSwitch _ -> fprintf ppf "memory->state"
      in
      body_writers, gen_expr
    in
    let f_id idref =
      let id, idinfo = idref in
      let gen_expr ppf () =
        let f_module_value () =
          match codegen_ctx with
          | CTXGlobalConst -> assert false
          | _ -> fprintf ppf "memory->%s" id
        in
        let f_state_const () =
          match codegen_ctx with
          | CTXStateConst state_id
          | CTXStateNewnodeIn state_id
          | CTXStateNode (state_id, _, _)
          | CTXSwitch state_id -> fprintf ppf "memory->statebody.%s.%s" state_id id
          | _ -> assert false
        in
        let f_state_param () =
          match codegen_ctx with
          | CTXStateConst state_id
          | CTXStateNewnodeIn state_id
          | CTXStateNode (state_id, _, _)
          | CTXSwitch state_id -> fprintf ppf "memory->state->params.%s.%s" state_id id
          | _ -> assert false
        in
        let f_node nattr ty =
          match codegen_ctx, nattr, ty with
          | CTXModuleNewnodeIn, _, TMode (_, _, _) | CTXModuleNode _, _, TMode (_, _, _)
            -> fprintf ppf "memory->%s.value" id
          | CTXModuleNewnodeIn, _, _ | CTXModuleNode _, _, _ ->
            fprintf ppf "memory->%s[current_side]" id
          | CTXStateNode (state_id, _, _), NormalNode, _
          | CTXStateNewnodeIn state_id, NormalNode, _
          | CTXSwitch state_id, NormalNode, _ ->
            fprintf ppf "memory->statebody.%s.%s[current_side]" state_id id
          | CTXStateNode _, _, _ | CTXStateNewnodeIn _, _, _ | CTXSwitch _, _, _ ->
            fprintf ppf "memory->%s[current_side]" id
          | _ -> assert false
        in
        match idinfo with
        | LocalId _ -> pp_print_string ppf id
        | ConstId (file, _) -> gen_global_constname ppf (file, id)
        | ModuleParam _ | ModuleConst _ -> f_module_value ()
        | StateConst _ -> f_state_const ()
        | StateParam _ -> f_state_param ()
        | NodeId (nattr, ty) -> f_node nattr ty
        | InaccNodeId _ ->
          Format.printf "InaccNodeId is not supported yet.\n";
          assert false
        | _ -> assert false
      in
      body_writers, gen_expr
    in
    let f_annot idref annot =
      let id, idinfo = idref in
      let gen_expr ppf () =
        match idinfo, annot with
        | NodeId (nattr, _), ALast ->
          (match codegen_ctx, nattr with
           | CTXModuleNode _, _ | CTXModuleNewnodeIn, _ ->
             fprintf ppf "memory->%s[!current_side]" id
           | CTXStateNode (state_id, _, _), NormalNode
           | CTXStateNewnodeIn state_id, NormalNode
           | CTXSwitch state_id, NormalNode ->
             fprintf ppf "memory->statebody.%s.%s[!current_side]" state_id id
           | CTXStateNode _, _ | CTXStateNewnodeIn _, _ | CTXSwitch _, _ ->
             fprintf ppf "memory->%s[!current_side]" id
           | _ -> assert false)
        | _ -> assert false
      in
      body_writers, gen_expr
    in
    let f_funcall idref es =
      let id, idinfo = idref in
      let body_writers, generators =
        List.fold_left
          (fun (body_writers, generators) expr ->
            let body_writers, gen_expr = rec_f expr body_writers in
            body_writers, gen_expr :: generators)
          ([], [])
          es
      in
      let generators = List.rev generators in
      let gen_expr ppf () =
        match idinfo with
        | FunId (file, _, _) ->
          fprintf
            ppf
            "%a(@[<hov>%a@])"
            gen_global_funname
            (file, id)
            (exec_all_writers () ~pp_sep:pp_print_commaspace)
            generators
        | _ -> assert false
      in
      body_writers, gen_expr
    in
    let f_if etest ethen eelse =
      let testbody_writers, gen_test = rec_f etest [] in
      let thenbody_writers, gen_then = rec_f ethen [] in
      let elsebody_writers, gen_else = rec_f eelse [] in
      let testbody_writers = List.rev testbody_writers in
      let thenbody_writers = List.rev thenbody_writers in
      let elsebody_writers = List.rev elsebody_writers in
      let ret_varname = make_tmpvar_name () in
      let gen_body_then ppf () =
        fprintf ppf "@[<v>";
        if thenbody_writers = []
        then ()
        else fprintf ppf "%a@," (exec_all_writers ()) thenbody_writers;
        fprintf ppf "%a = %a;" pp_print_string ret_varname gen_then ();
        fprintf ppf "@]"
      in
      let gen_body_else ppf () =
        fprintf ppf "@[<v>";
        if elsebody_writers = []
        then ()
        else fprintf ppf "%a@," (exec_all_writers ()) elsebody_writers;
        fprintf ppf "%a = %a;" pp_print_string ret_varname gen_else ();
        fprintf ppf "@]"
      in
      let gen_body ppf () =
        fprintf ppf "@[<v>";
        fprintf ppf "%a %a;" (gen_value_type metainfo) tast pp_print_string ret_varname;
        if testbody_writers = []
        then ()
        else fprintf ppf "@,%a" (exec_all_writers ()) testbody_writers;
        fprintf ppf "@,@[<v>";
        fprintf ppf "if (%a) {@;<0 2>" gen_test ();
        fprintf ppf "%a@," gen_body_then ();
        fprintf ppf "} else {@;<0 2>";
        fprintf ppf "%a@," gen_body_else ();
        fprintf ppf "}@]";
        fprintf ppf "@]"
      in
      let body_writers = gen_body :: body_writers in
      let gen_expr ppf () = pp_print_string ppf ret_varname in
      body_writers, gen_expr
    in
    let f_let binders body =
      let body_writers =
        List.fold_left
          (fun body_writers binder ->
            let var_id, _ = binder.binder_id in
            let _, var_type = binder.binder_body in
            let body_writers, gen_bexpr = rec_f binder.binder_body body_writers in
            let gen_vardecl ppf () =
              fprintf
                ppf
                "%a %a = %a;"
                (gen_value_type metainfo)
                var_type
                pp_print_string
                var_id
                gen_bexpr
                ()
            in
            gen_vardecl :: body_writers)
          body_writers
          binders
      in
      rec_f body body_writers
    in
    let f_case target branchs =
      let _, ttarget = target in
      let tbody_writers, gen_texpr = rec_f target [] in
      let tbody_writers = List.rev tbody_writers in
      let target_varname = make_tmpvar_name () in
      let gen_body_head ppf () =
        fprintf ppf "@[<v>";
        if tbody_writers = []
        then ()
        else fprintf ppf "%a@," (exec_all_writers ()) tbody_writers;
        fprintf
          ppf
          "%a %a = %a;"
          (gen_value_type metainfo)
          ttarget
          pp_print_string
          target_varname
          gen_texpr
          ();
        fprintf ppf "@]"
      in
      let gen_target ppf () = pp_print_string ppf target_varname in
      let f_single_branch branch =
        let pattern = branch.branch_pat in
        let pbody_writers, gen_expr = rec_f branch.branch_body [] in
        let pbody_writers = List.rev pbody_writers in
        let _, binds = get_pattern_conds_binds metainfo gen_target pattern in
        let gen_body ppf () =
          fprintf ppf "@[<v>";
          fprintf ppf "%a" gen_body_head ();
          if binds = [] then () else fprintf ppf "@,%a" (exec_all_writers ()) binds;
          if pbody_writers = []
          then ()
          else fprintf ppf "@,%a" (exec_all_writers ()) pbody_writers;
          fprintf ppf "@]"
        in
        gen_body :: body_writers, gen_expr
      in
      let f_multiple_branch branchs =
        let ret_varname = make_tmpvar_name () in
        let gen_condexpr ppf conds =
          let pp_print_condsep ppf () = fprintf ppf "@ &&" in
          (exec_all_writers () ~pp_sep:pp_print_condsep) ppf conds
        in
        let gen_branch_body ppf (binds, pbody_writers, gen_pexpr) =
          fprintf ppf "@[<v>";
          if binds = [] then () else fprintf ppf "%a@," (exec_all_writers ()) binds;
          if pbody_writers = []
          then ()
          else fprintf ppf "%a@," (exec_all_writers ()) pbody_writers;
          fprintf ppf "%a = %a;" pp_print_string ret_varname gen_pexpr ();
          fprintf ppf "@]"
        in
        let gen_body ppf () =
          let branch_size = List.length branchs in
          fprintf ppf "@[<v>";
          fprintf ppf "%a@," gen_body_head ();
          fprintf
            ppf
            "%a %a;@,"
            (gen_value_type metainfo)
            tast
            pp_print_string
            ret_varname;
          List.iteri
            (fun pos branch ->
              let pattern = branch.branch_pat in
              let pbody_writers, gen_pret = rec_f branch.branch_body [] in
              let pbody_writers = List.rev pbody_writers in
              let conds, binds = get_pattern_conds_binds metainfo gen_target pattern in
              if pos = 0
              then fprintf ppf "if (@[<hov>%a@]) {@;<0 2>" gen_condexpr conds
              else if pos = branch_size - 1
              then fprintf ppf " else {@;<0 2>"
              else fprintf ppf " else if (@[<hov>%a@]) {@;<0 2>" gen_condexpr conds;
              fprintf ppf "@[<v>%a@]@," gen_branch_body (binds, pbody_writers, gen_pret);
              fprintf ppf "}")
            branchs;
          fprintf ppf "@]"
        in
        let gen_expr ppf () = pp_print_string ppf ret_varname in
        gen_body :: body_writers, gen_expr
      in
      match branchs with
      | [] -> assert false
      | [ branch ] -> f_single_branch branch
      | branchs -> f_multiple_branch branchs
    in
    (* body of rec_f *)
    match ast with
    | EUniOp (op, e1) -> f_uni_op op e1
    | EBinOp (op, e1, e2) -> f_bin_op op e1 e2
    | EVariant (cons_id, e1) -> f_variant cons_id e1
    | ETuple es -> f_tuple es
    | EConst l -> f_const l
    | ERetain -> f_retain ()
    | EId idref -> f_id idref
    | EAnnot (idref, annot) -> f_annot idref annot
    | EFuncall (idref, args) -> f_funcall idref args
    | EIf (etest, ethen, eelse) -> f_if etest ethen eelse
    | ELet (binders, body) -> f_let binders body
    | ECase (target, branchs) -> f_case target branchs
  in
  let body_writers, gen_expr = rec_f expr [] in
  let body_writers = List.rev body_writers in
  body_writers, gen_expr
;;

let gen_body_expr body_writers gen_lastline ppf () =
  fprintf ppf "@[<v>";
  if body_writers = [] then () else fprintf ppf "%a@," (exec_all_writers ()) body_writers;
  fprintf ppf "%a" gen_lastline ();
  fprintf ppf "@]"
;;

type updatefun_generator =
  { updatefun_ctx : codegen_ctx
  ; updatefun_body : expression
  ; updatefun_gen_funname : writer
  ; updatefun_gen_memorytype : writer
  ; updatefun_gen_address : writer
  }

let define_updatefun metainfo generator fun_writers =
  let fundef_ctx = generator.updatefun_ctx in
  let body_expr = generator.updatefun_body in
  let gen_funname = generator.updatefun_gen_funname in
  let gen_memorytype = generator.updatefun_gen_memorytype in
  let gen_address = generator.updatefun_gen_address in
  let body_writers, gen_expr = get_expr_generator metainfo fundef_ctx body_expr in
  let gen_prototype ppf () = fprintf ppf "%a(%a*);" gen_funname () gen_memorytype () in
  let gen_body_lastline ppf () =
    fprintf ppf "@[<2>%a =@ @[%a@];@]" gen_address () gen_expr ()
  in
  let gen_definition ppf () =
    gen_codeblock
      (fun ppf () -> fprintf ppf "%a(@[<h>%a* memory@])" gen_funname () gen_memorytype ())
      (gen_body_expr body_writers gen_body_lastline)
      ppf
      ()
  in
  (gen_prototype, gen_definition) :: fun_writers
;;
