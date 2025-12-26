let rec desugar : Cst.t -> Ast.t = function
  | Missing src -> Missing src
  | Ident (src, name) -> Ident (src, name)
  | App (src, f, a) -> App (src, desugar f, desugar a)
  | Lam (src, binders, body) ->
      List.fold_right
        (fun (binder : Cst.binder_group) acc : Ast.t ->
          match binder with
          | Untyped (b_src, name) -> Lam (src, Untyped (b_src, name), acc)
          | Typed typed_group ->
              let group_src, names, ty = typed_group in
              let desugared_ty = desugar ty in
              List.fold_right
                (fun name acc' : Ast.t ->
                  Lam (src, Typed (group_src, name, desugared_ty), acc'))
                names acc)
        binders (desugar body)
  | Pi (src, (group_src, names, ty), body) ->
      let desugared_ty = desugar ty in
      List.fold_right
        (fun name acc : Ast.t -> Pi (src, (group_src, name, desugared_ty), acc))
        names (desugar body)
  | Arrow (src, a, b) -> Pi (src, (src, None, desugar a), desugar b)
  | Let (src, name, ty_opt, rhs, body) ->
      Let (src, name, Option.map desugar ty_opt, desugar rhs, desugar body)
  | U src -> U src
  | Sigma (src, (group_src, names, ty), body) ->
      let desugared_ty = desugar ty in
      List.fold_right
        (fun name acc : Ast.t ->
          App
            ( src,
              App (src, Ident (src, "Sigma"), desugared_ty),
              Lam (src, Typed (group_src, name, desugared_ty), acc) ))
        names (desugar body)
  | Prod (src, a, b) ->
      App (src, App (src, Ident (src, "Prod"), desugar a), desugar b)
  | Pair (src, a, b) -> Pair (src, desugar a, desugar b)
  | Eq (src, a, b) -> Eq (src, desugar a, desugar b)
  | NatLit (src, n) ->
      let rec build_nat : int -> Ast.t = function
        | 0 -> Ident (src, "Nat.zero")
        | k -> App (src, Ident (src, "Nat.succ"), build_nat (k - 1))
      in
      build_nat n
  | Add (src, a, b) ->
      App (src, App (src, Ident (src, "Nat.add"), desugar a), desugar b)
  | Sub (src, a, b) ->
      App (src, App (src, Ident (src, "Nat.sub"), desugar a), desugar b)
  | Ann (src, e, ty) -> Ann (src, desugar e, desugar ty)
  | Sorry src -> Sorry src

let desugar_typed_binder_group_list (groups : Cst.typed_binder_group list) :
    Ast.typed_binder list =
  List.concat_map
    (fun (group_src, names, ty) ->
      let desugared_ty = desugar ty in
      List.map (fun name -> (group_src, name, desugared_ty)) names)
    groups

let desugar_command : Cst.Command.t -> Ast.Command.t = function
  | Import import ->
      Import { src = import.src; module_name = import.module_name }
  | Definition def ->
      Definition
        {
          src = def.src;
          name = def.name;
          params = desugar_typed_binder_group_list def.params;
          ty_opt = Option.map desugar def.ty_opt;
          body = desugar def.body;
        }
  | Example ex ->
      Example
        {
          src = ex.src;
          params = desugar_typed_binder_group_list ex.params;
          ty_opt = Option.map desugar ex.ty_opt;
          body = desugar ex.body;
        }
  | Axiom ax ->
      Axiom
        {
          src = ax.src;
          name = ax.name;
          params = desugar_typed_binder_group_list ax.params;
          ty = desugar ax.ty;
        }
  | Inductive ind ->
      Inductive
        {
          src = ind.src;
          name = ind.name;
          params = desugar_typed_binder_group_list ind.params;
          ty_opt = Option.map desugar ind.ty_opt;
          ctors =
            List.map
              (fun (ctor : Cst.Command.inductive_constructor) :
                   Ast.Command.inductive_constructor ->
                {
                  src = ctor.src;
                  name = ctor.name;
                  params = desugar_typed_binder_group_list ctor.params;
                  ty_opt = Option.map desugar ctor.ty_opt;
                })
              ind.ctors;
        }
  | Structure str ->
      Structure
        {
          src = str.src;
          name = str.name;
          params = desugar_typed_binder_group_list str.params;
          ty_opt = Option.map desugar str.ty_opt;
          fields =
            List.map
              (fun (field : Cst.Command.structure_field) :
                   Ast.Command.structure_field ->
                {
                  src = field.src;
                  name = field.name;
                  params = desugar_typed_binder_group_list field.params;
                  ty = desugar field.ty;
                })
              str.fields;
        }

let desugar_program (prog : Cst.program) : Ast.program =
  List.map desugar_command prog
