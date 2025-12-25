open Frontend
open Syntax
open Nbe

(* ========== Program Elaboration ========== *)

exception Circular_import of Name.t
exception Import_not_found of Name.t

module ModuleNameSet = Set.Make (Name)

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    ~(parse : string -> Raw_syntax.program) (prog : Raw_syntax.program) :
    (Name.t * tm * ty) list =
  let rec process_import genv imported importing m =
    if List.mem m importing then raise (Circular_import m);
    if ModuleNameSet.mem m imported then
      (genv, imported)
    else
      let path = Filename.concat root (String.concat "/" m ^ ".qdt") in
      let content =
        try read_file path with
        | _ -> raise (Import_not_found m)
      in
      let imported_prog = parse content in
      let genv, imported, _ =
        go genv imported (m :: importing) [] imported_prog
      in
      (genv, ModuleNameSet.add m imported)
  and go genv imported importing acc = function
    | [] -> (genv, imported, List.rev acc)
    | Import { module_name } :: rest ->
        let m = Name.parse module_name in
        let genv, imported = process_import genv imported importing m in
        go genv imported importing acc rest
    | Def { name; params; ty_opt; body } :: rest ->
        let name = Name.parse name in
        let params = Desugar.desugar_typed_binder_groups params in
        let param_ctx, param_tys = Params.elab_params genv params in
        let term, ty_val =
          match ty_opt with
          | Some ty_raw ->
              let expected_ty = Bidir.check_ty genv param_ctx ty_raw in
              let expected_ty_val = eval_ty genv param_ctx.env expected_ty in
              let term = Bidir.check_tm genv param_ctx body expected_ty_val in
              (term, expected_ty_val)
          | None -> Bidir.infer_tm genv param_ctx body
        in
        let term_with_params = Params.build_lambda param_tys term in
        let term_val = eval_tm genv param_ctx.env term_with_params in
        let ty =
          Params.build_pi param_tys (Quote.quote_ty genv param_ctx.lvl ty_val)
        in
        let genv =
          Global.NameMap.add name (Global.Def { ty; tm = term_val }) genv
        in
        go genv imported importing ((name, term_with_params, ty) :: acc) rest
    | Example { params; ty_opt; body } :: rest ->
        let params = Desugar.desugar_typed_binder_groups params in
        let param_ctx, _param_tys = Params.elab_params genv params in
        let _, _ =
          match ty_opt with
          | Some ty_raw ->
              let expected_ty = Bidir.check_ty genv param_ctx ty_raw in
              let expected_ty_val = eval_ty genv param_ctx.env expected_ty in
              let term = Bidir.check_tm genv param_ctx body expected_ty_val in
              (term, expected_ty_val)
          | None -> Bidir.infer_tm genv param_ctx body
        in
        go genv imported importing acc rest
    | Axiom { name; params; ty } :: rest ->
        let name = Name.parse name in
        let params = Desugar.desugar_typed_binder_groups params in
        let param_ctx, param_tys = Params.elab_params genv params in
        let ty = Bidir.check_ty genv param_ctx ty in
        let ty_val = eval_ty genv param_ctx.env ty in
        let ty =
          Params.build_pi param_tys (Quote.quote_ty genv param_ctx.lvl ty_val)
        in
        let genv = Global.NameMap.add name (Global.Axiom { ty }) genv in
        go genv imported importing ((name, TmSorry (0, ty), ty) :: acc) rest
    | Inductive info :: rest ->
        let genv, results = Inductive.elab_inductive genv info in
        go genv imported importing (results @ acc) rest
    | Structure info :: rest ->
        let genv, results = Structure.elab_structure genv info in
        go genv imported importing (results @ acc) rest
  in
  let genv, _, result = go Global.empty ModuleNameSet.empty [] [] prog in
  Format.printf "Elaborated %d definitions\n" (Global.NameMap.cardinal genv);
  result

let elab_program : Raw_syntax.program -> (Name.t * tm * ty) list =
  elab_program_with_imports ~root:"."
    ~read_file:(fun _ -> "")
    ~parse:(fun _ -> [])
