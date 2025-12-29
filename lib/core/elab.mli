val elab_program_with_imports :
  current_file:string ->
  read_file:(string -> string) ->
  Frontend.Ast.program ->
  (Global.t, Global.t) result
