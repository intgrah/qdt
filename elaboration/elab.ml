open Syntax
open Frontend
open Nbe

(* ========== Program Elaboration ========== *)

module ModuleNameSet = Set.Make (Name)

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    (prog : Ast.program) : (Name.t * tm * ty) list =
  let rec process_import genv imported importing (m : Ast.Command.import) =
    let name = Name.parse m.module_name in
    if List.mem name importing then
      raise (Error.make_with_src ~kind:Import "Circular import" m.src);
    if ModuleNameSet.mem name imported then
      (genv, imported)
    else
      let path = Filename.concat root (String.concat "/" name ^ ".qdt") in
      let content =
        try read_file path with
        | _ -> raise (Error.make_with_src ~kind:Import "Import not found" m.src)
      in
      let imported_prog = Parser.parse content in
      let imported_prog = Desugar.desugar_program imported_prog in
      let genv, imported, _ =
        go genv imported (name :: importing) [] imported_prog ~filename:path
      in
      (genv, ModuleNameSet.add name imported)
  and go genv imported importing acc ~filename = function
    | [] -> (genv, imported, List.rev acc)
    | Import import :: rest ->
        let genv, imported = process_import genv imported importing import in
        go genv imported importing acc rest ~filename
    | Definition { src; name; params; ty_opt; body } :: rest -> (
        let name = Name.parse name in
        try
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
          go genv imported importing
            ((name, term_with_params, ty) :: acc)
            rest ~filename
        with
        | Error.Error err ->
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename
        | exn ->
            let err =
              Error.make_with_src_t ~kind:Elaboration
                (Format.asprintf "Elaboration error in %s: %s"
                   (Name.to_string name) (Printexc.to_string exn))
                src
            in
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename)
    | Example { src; params; ty_opt; body } :: rest -> (
        try
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
          go genv imported importing acc rest ~filename
        with
        | Error.Error err ->
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename
        | exn ->
            let err =
              Error.make_with_src_t ~kind:Elaboration
                (Format.asprintf "Elaboration error in example: %s"
                   (Printexc.to_string exn))
                src
            in
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename)
    | Axiom { src; name; params; ty } :: rest -> (
        let name = Name.parse name in
        try
          let param_ctx, param_tys = Params.elab_params genv params in
          let ty = Bidir.check_ty genv param_ctx ty in
          let ty_val = eval_ty genv param_ctx.env ty in
          let ty =
            Params.build_pi param_tys (Quote.quote_ty genv param_ctx.lvl ty_val)
          in
          let genv = Global.NameMap.add name (Global.Axiom { ty }) genv in
          go genv imported importing
            ((name, TmSorry (0, ty), ty) :: acc)
            rest ~filename
        with
        | Error.Error err ->
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename
        | exn ->
            let err =
              Error.make_with_src_t ~kind:Elaboration
                (Format.asprintf "Elaboration error in axiom %s: %s"
                   (Name.to_string name) (Printexc.to_string exn))
                src
            in
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename)
    | Inductive info :: rest -> (
        try
          let genv, results = Inductive.elab_inductive genv info in
          go genv imported importing (results @ acc) rest ~filename
        with
        | Error.Error err ->
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename
        | exn ->
            let err =
              Error.make_with_src_t ~kind:Elaboration
                (Format.asprintf "Elaboration error in inductive %s: %s"
                   info.name (Printexc.to_string exn))
                info.src
            in
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename)
    | Structure info :: rest -> (
        try
          let genv, results = Structure.elab_structure genv info in
          go genv imported importing (results @ acc) rest ~filename
        with
        | Error.Error err ->
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename
        | exn ->
            let err =
              Error.make_with_src_t ~kind:Elaboration
                (Format.asprintf "Elaboration error in structure %s: %s"
                   info.name (Printexc.to_string exn))
                info.src
            in
            Format.eprintf "%a\n" (Error.pp ~filename) err;
            go genv imported importing acc rest ~filename)
  in
  let genv, _, result =
    go Global.empty ModuleNameSet.empty [] [] prog ~filename:"<main>"
  in
  Format.printf "Elaborated %d definitions\n" (Global.NameMap.cardinal genv);
  result
