open Frontend
open Syntax
open Nbe

exception Elab_error of string

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
    | Def { name; ty_opt = _; body } :: rest ->
        let full_name = Name.parse name in
        let term, ty_val = Bidir.infer_tm genv Context.empty body in
        let term_val = eval_tm genv [] term in
        let ty_quoted = Quote.quote_ty genv 0 ty_val in
        let genv =
          Global.NameMap.add full_name
            (Global.Def { ty = ty_quoted; tm = term_val })
            genv
        in
        let ty_out = Quote.quote_ty genv 0 ty_val in
        go genv imported importing ((full_name, term, ty_out) :: acc) rest
    | Example { ty_opt = _; body } :: rest ->
        let _ = Bidir.infer_tm genv Context.empty body in
        go genv imported importing acc rest
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
