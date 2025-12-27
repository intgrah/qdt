open Frontend
open Nbe

(* ========== Program Elaboration ========== *)

module ModuleNameMap = Map.Make (Name)

type module_status =
  | Importing
  | Imported

type st = {
  genv : Global.t;
  modules : module_status ModuleNameMap.t;
}

let elab_definition (d : Ast.Command.definition) (st : st) : st =
  let name = Name.parse d.name in
  let param_ctx, param_tys = Params.elab_params st.genv d.params in
  let term, ty_val =
    match d.ty_opt with
    | None -> Bidir.infer_tm st.genv param_ctx d.body
    | Some ty_raw ->
        let expected_ty = Bidir.check_ty st.genv param_ctx ty_raw in
        let expected_ty_val = eval_ty st.genv param_ctx.env expected_ty in
        let term = Bidir.check_tm st.genv param_ctx d.body expected_ty_val in
        (term, expected_ty_val)
  in
  let term_with_params = Params.build_lambda param_tys term in
  let term_val = eval_tm st.genv param_ctx.env term_with_params in
  let ty =
    Params.build_pi param_tys (Quote.quote_ty st.genv param_ctx.lvl ty_val)
  in
  {
    st with
    genv = Global.NameMap.add name (Global.Def { ty; tm = term_val }) st.genv;
  }

let elab_example (e : Ast.Command.example) (st : st) : st =
  let param_ctx, _param_tys = Params.elab_params st.genv e.params in
  let _term, _ty_val =
    match e.ty_opt with
    | Some ty_raw ->
        let expected_ty = Bidir.check_ty st.genv param_ctx ty_raw in
        let expected_ty_val = eval_ty st.genv param_ctx.env expected_ty in
        let term = Bidir.check_tm st.genv param_ctx e.body expected_ty_val in
        (term, expected_ty_val)
    | None -> Bidir.infer_tm st.genv param_ctx e.body
  in
  st

let elab_axiom (a : Ast.Command.axiom) (st : st) : st =
  let name = Name.parse a.name in
  let param_ctx, param_tys = Params.elab_params st.genv a.params in
  let ty = Bidir.check_ty st.genv param_ctx a.ty in
  let ty_val = eval_ty st.genv param_ctx.env ty in
  let ty =
    Params.build_pi param_tys (Quote.quote_ty st.genv param_ctx.lvl ty_val)
  in
  { st with genv = Global.NameMap.add name (Global.Axiom { ty }) st.genv }

let elab_inductive (info : Ast.Command.inductive) (st : st) : st =
  { st with genv = Inductive.elab_inductive st.genv info }

let elab_structure (info : Ast.Command.structure) (st : st) : st =
  { st with genv = Structure.elab_structure st.genv info }

let protect_unit ~filename (k : st -> st) (st : st) : st =
  try k st with
  | Error.Error err ->
      Format.eprintf "Error: %a@." (Error.pp ~filename) err;
      st

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    (prog : Ast.program) : Global.t =
  let rec elab_program ~filename (prog : Ast.program) : st -> st =
    List.fold_right
      (function
        | Ast.Command.Import m -> process_import m
        | Definition def -> protect_unit ~filename (elab_definition def)
        | Example ex -> protect_unit ~filename (elab_example ex)
        | Axiom ax -> protect_unit ~filename (elab_axiom ax)
        | Inductive info -> protect_unit ~filename (elab_inductive info)
        | Structure info -> protect_unit ~filename (elab_structure info))
      (List.rev prog)
  and process_import (m : Ast.Command.import) (st : st) : st =
    let name = Name.parse m.module_name in
    match ModuleNameMap.find_opt name st.modules with
    | Some Imported -> st
    | Some Importing ->
        Error.raise_with_src ~kind:Import "Circular import" m.src
    | None ->
        let st =
          { st with modules = ModuleNameMap.add name Importing st.modules }
        in
        let path = Filename.concat root (String.concat "/" name ^ ".qdt") in
        let content =
          try read_file path with
          | _ -> Error.raise_with_src ~kind:Import "Import not found" m.src
        in
        let imported_prog = Parser.parse content in
        let imported_prog = Desugar.desugar_program imported_prog in
        let st = elab_program ~filename:path imported_prog st in
        { st with modules = ModuleNameMap.add name Imported st.modules }
  in
  let st : st = { genv = Global.empty; modules = ModuleNameMap.empty } in
  let st = elab_program ~filename:"<main>" prog st in
  Format.printf "Elaborated %d definitions@." (Global.NameMap.cardinal st.genv);
  st.genv
