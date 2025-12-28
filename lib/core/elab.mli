val elab_program_with_imports :
  root:string ->
  read_file:(string -> string) ->
  Frontend.Ast.program ->
  Global.t
