open Core_syntax
open Quote
open Frontend

(* ========== Program Elaboration ========== *)

module ModuleNameMap = Map.Make (Name)

type module_status =
  | Importing
  | Imported

type st = {
  genv : Global.t;
  modules : module_status ModuleNameMap.t;
  has_errors : bool;
}

let elab_definition (d : Ast.Command.definition) (st : st) : st =
  let name = Name.parse d.name in
  let param_ctx, param_tys = Params.elab_params st.genv d.params in
  let tm, ty =
    match d.ty_opt with
    | None ->
        let tm, ty_val = Bidir.infer_tm st.genv param_ctx d.body in
        (tm, quote_ty st.genv param_ctx.lvl ty_val)
    | Some ty_raw ->
        let ty = Bidir.check_ty st.genv param_ctx ty_raw in
        let ty_val = Nbe.eval_ty st.genv param_ctx.env ty in
        let tm = Bidir.check_tm st.genv param_ctx d.body ty_val in
        (tm, ty)
  in
  let tm = param_tys @==> tm in
  let ty = param_tys @--> ty in
  { st with genv = Global.add name (Global.Definition { ty; tm }) st.genv }

let elab_example (e : Ast.Command.example) (st : st) : st =
  let param_ctx, _param_tys = Params.elab_params st.genv e.params in
  let _term, _ty_val =
    match e.ty_opt with
    | Some ty_raw ->
        let expected_ty = Bidir.check_ty st.genv param_ctx ty_raw in
        let expected_ty_val = Nbe.eval_ty st.genv param_ctx.env expected_ty in
        let term = Bidir.check_tm st.genv param_ctx e.body expected_ty_val in
        (term, expected_ty_val)
    | None -> Bidir.infer_tm st.genv param_ctx e.body
  in
  st

let elab_axiom (a : Ast.Command.axiom) (st : st) : st =
  let name = Name.parse a.name in
  let param_ctx, param_tys = Params.elab_params st.genv a.params in
  let ty = Bidir.check_ty st.genv param_ctx a.ty in
  let ty = param_tys @--> ty in
  { st with genv = Global.add name (Global.Axiom { ty }) st.genv }

let elab_inductive (info : Ast.Command.inductive) (st : st) : st =
  { st with genv = Inductive.elab_inductive st.genv info }

let elab_structure (info : Ast.Command.structure) (st : st) : st =
  { st with genv = Structure.elab_structure st.genv info }

let protect_unit ~filename (k : st -> st) (st : st) : st =
  try k st with
  | Error.Error err ->
      Format.eprintf "Error: %a@." (Error.pp ~filename) err;
      { st with has_errors = true }

let elab_program_with_imports ~(current_file : string)
    ~(read_file : string -> string) (prog : Ast.program) :
    (Global.t, Global.t) result =
  let rec elab_program ~filename (prog : Ast.program) : st -> st =
    List.fold_right
      (function
        | Ast.Command.Import m ->
            protect_unit ~filename (process_import filename m)
        | Definition def -> protect_unit ~filename (elab_definition def)
        | Example ex -> protect_unit ~filename (elab_example ex)
        | Axiom ax -> protect_unit ~filename (elab_axiom ax)
        | Inductive info -> protect_unit ~filename (elab_inductive info)
        | Structure info -> protect_unit ~filename (elab_structure info))
      (List.rev prog)
  and process_import filename (m : Ast.Command.import) (st : st) : st =
    let name = Name.parse m.module_name in
    match ModuleNameMap.find_opt name st.modules with
    | Some Imported -> st
    | Some Importing -> Error.raise Import "Circular import" m.src
    | None ->
        let st =
          { st with modules = ModuleNameMap.add name Importing st.modules }
        in
        let path =
          match name with
          | "Std" :: _ ->
              let stdlib_path =
                try Sys.getenv "QDT_PATH" with
                | Not_found ->
                    Error.raise Import "QDT_PATH environment variable not set"
                      m.src
              in
              let stdlib_path =
                if Filename.is_relative stdlib_path then
                  Filename.concat (Sys.getcwd ()) stdlib_path
                else
                  stdlib_path
              in
              Filename.concat stdlib_path (String.concat "/" name ^ ".qdt")
          | _ ->
              let current_dir = Filename.dirname filename in
              Filename.concat current_dir (String.concat "/" name ^ ".qdt")
        in
        let content =
          try read_file path with
          | _ -> Error.raise Import "Import not found" m.src
        in
        let imported_prog = Parser.parse content in
        let imported_prog = Desugar.desugar_program imported_prog in
        let st = elab_program ~filename:path imported_prog st in
        { st with modules = ModuleNameMap.add name Imported st.modules }
  in
  let st : st =
    { genv = Global.empty; modules = ModuleNameMap.empty; has_errors = false }
  in
  let st = elab_program ~filename:current_file prog st in
  Format.printf "Elaborated %d definitions@." (Global.cardinal st.genv);
  if st.has_errors then
    Error st.genv
  else
    Ok st.genv
