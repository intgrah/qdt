open Elaboration
open Syntax

let tm_testable : tm Alcotest.testable = Alcotest.testable Pretty.pp_tm ( = )

module Test_eval = struct
  let identity () =
    let term = Lam ("x", Var 0) in
    let result = Eval.eval [] term in
    match result with
    | VLam ("x", Closure ([], Var 0)) -> ()
    | _ -> Alcotest.fail "identity evaluation failed"

  let beta () =
    let term = App (Lam ("x", Var 0), U) in
    let result = Eval.eval [] term in
    match result with
    | VU -> ()
    | _ -> Alcotest.fail "beta reduction failed"

  let tests =
    [
      Alcotest.test_case "identity" `Quick identity;
      Alcotest.test_case "beta" `Quick beta;
    ]
end

module Test_quote = struct
  let variable () =
    let v = VRigid (0, []) in
    let tm = Quote.quote 1 v in
    Alcotest.(check string) "same" "#0" (Pretty.tm_to_string tm)

  let lambda () =
    let v = VLam ("x", Closure ([], Var 0)) in
    let tm = Quote.quote 0 v in
    match tm with
    | Lam ("x", Var 0) -> ()
    | _ -> Alcotest.fail "lambda quoting failed"

  let tests =
    [
      Alcotest.test_case "variable" `Quick variable;
      Alcotest.test_case "lambda" `Quick lambda;
    ]
end

module Test_nbe = struct
  let beta () =
    let term = App (Lam ("x", Var 0), U) in
    let normalized = Quote.nf [] term in
    match normalized with
    | U -> ()
    | _ -> Alcotest.failf "expected U, got %s" (Pretty.tm_to_string normalized)

  let nested () =
    let term = App (Lam ("x", Lam ("y", Var 1)), U) in
    let normalized = Quote.nf [] term in
    match normalized with
    | Lam ("y", U) -> ()
    | _ ->
        Alcotest.failf "expected Lam(y,U), got %s"
          (Pretty.tm_to_string normalized)

  let idempotent () =
    let term = App (Lam ("x", Var 0), U) in
    let norm1 = Quote.nf [] term in
    let norm2 = Quote.nf [] norm1 in
    Alcotest.(check string)
      "same"
      (Pretty.tm_to_string norm1)
      (Pretty.tm_to_string norm2)

  let tests =
    [
      Alcotest.test_case "beta" `Quick beta;
      Alcotest.test_case "nested" `Quick nested;
      Alcotest.test_case "idempotent" `Quick idempotent;
    ]
end

module Test_unify = struct
  let reflexive () = Unify.unify 0 VU VU

  let rigid_same () =
    let v = VRigid (0, []) in
    Unify.unify 1 v v

  let rigid_different () =
    let v1 = VRigid (0, []) in
    let v2 = VRigid (1, []) in
    Alcotest.check_raises "unify error" Unify.Unify_error (fun () ->
        Unify.unify 2 v1 v2)

  let solve_meta () =
    reset_meta_context ();
    let m = fresh_meta () in
    Unify.solve 0 m [] VU;
    match lookup_meta m with
    | Some v -> (
        match v with
        | VU -> ()
        | _ -> Alcotest.fail "wrong solution")
    | None -> Alcotest.fail "meta not solved"

  let occurs_check () =
    reset_meta_context ();
    let m = fresh_meta () in
    let rhs = VFlex (m, []) in
    Alcotest.check_raises "occurs check" Unify.Unify_error (fun () ->
        Unify.solve 0 m [] rhs)

  let scope_check () =
    reset_meta_context ();
    let m = fresh_meta () in
    let rhs = VRigid (0, []) in
    Alcotest.check_raises "scope check" Unify.Unify_error (fun () ->
        Unify.solve 0 m [] rhs)

  let pattern () =
    reset_meta_context ();
    let m = fresh_meta () in
    let spine = [ VRigid (0, []); VRigid (1, []) ] in
    let rhs = VRigid (0, []) in
    Unify.solve 2 m spine rhs;
    match lookup_meta m with
    | Some v ->
        let tm = Quote.quote 0 v in
        Alcotest.(check tm_testable) "same" (Lam ("x1", Lam ("x0", Var 1))) tm
    | None -> Alcotest.fail "pattern not solved"

  let eta () =
    let f = VRigid (0, []) in
    let lam = VLam ("x", Closure ([ f ], App (Var 1, Var 0))) in
    Unify.unify 1 lam f

  let tests =
    [
      Alcotest.test_case "reflexive" `Quick reflexive;
      Alcotest.test_case "rigid same" `Quick rigid_same;
      Alcotest.test_case "rigid different" `Quick rigid_different;
      Alcotest.test_case "solve meta" `Quick solve_meta;
      Alcotest.test_case "occurs check" `Quick occurs_check;
      Alcotest.test_case "scope check" `Quick scope_check;
      Alcotest.test_case "pattern" `Quick pattern;
      Alcotest.test_case "eta" `Quick eta;
    ]
end

module Test_elab = struct
  let check_identity () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Lambda ("x", Some U, Ident "x")) in
    let expected = VPi ("_", VU, Closure ([], U)) in
    let tm = Elab.check ctx [] raw expected in
    match tm with
    | Lam ("x", Var 0) -> ()
    | _ -> Alcotest.fail "check failed"

  let infer_unannotated () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Lambda ("x", None, Ident "x")) in
    let tm, ty = Elab.infer ctx [] raw in
    match (tm, ty) with
    | Lam ("x", Var 0), VPi _ -> ()
    | _ -> Alcotest.fail "infer failed"

  let hole_check () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.Hole in
    let tm = Elab.check ctx [] raw VU in
    match tm with
    | InsertedMeta (_, []) -> ()
    | _ -> Alcotest.fail "hole check failed"

  let hole_infer () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.Hole in
    let tm, _ty = Elab.infer ctx [] raw in
    match tm with
    | InsertedMeta (_, []) -> ()
    | _ -> Alcotest.fail "hole infer failed"

  let application () =
    reset_meta_context ();
    let id_ty = VPi ("_", VU, Closure ([], U)) in
    let id_val = VLam ("x", Closure ([], Var 0)) in
    let ctx = Check.bind_def Check.empty_context id_val id_ty in
    let raw = Lang.Raw_syntax.(App (Ident "id", U)) in
    let _tm, ty = Elab.infer ctx [ "id" ] raw in
    match ty with
    | VU -> ()
    | _ -> Alcotest.fail "application failed"

  let pi_type () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Pi ("A", U, Arrow (Ident "A", Ident "A"))) in
    let tm, ty = Elab.infer ctx [] raw in
    match ty with
    | VU ->
        Alcotest.(check tm_testable)
          "same"
          (Pi ("A", U, Pi ("_", Var 0, Var 1)))
          tm
    | _ -> Alcotest.fail "pi type failed"

  let let_annotated_check () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Let ("x", Some U, U, Ident "x")) in
    let tm = Elab.check ctx [] raw VU in
    match tm with
    | Let ("x", U, U, Var 0) -> ()
    | _ -> Alcotest.fail "let annotated check failed"

  let let_unannotated_check () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Let ("x", None, U, Ident "x")) in
    let tm = Elab.check ctx [] raw VU in
    match tm with
    | Let ("x", U, U, Var 0) -> ()
    | _ -> Alcotest.fail "let unannotated check failed"

  let let_annotated_infer () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Let ("x", Some U, U, Ident "x")) in
    let tm, ty = Elab.infer ctx [] raw in
    match (tm, ty) with
    | Let ("x", U, U, Var 0), VU -> ()
    | _ -> Alcotest.fail "let annotated infer failed"

  let let_unannotated_infer () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Let ("x", None, U, Ident "x")) in
    let tm, ty = Elab.infer ctx [] raw in
    match (tm, ty) with
    | Let ("x", U, U, Var 0), VU -> ()
    | _ -> Alcotest.fail "let unannotated infer failed"

  let arrow_type () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Arrow (U, U)) in
    let tm, ty = Elab.infer ctx [] raw in
    match ty with
    | VU -> Alcotest.(check tm_testable) "same" (Pi ("_", U, U)) tm
    | _ -> Alcotest.fail "arrow type failed"

  let error_var_not_in_scope () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Ident "x") in
    Alcotest.check_raises "var not in scope"
      (Elab.Elab_error "Variable not in scope: x") (fun () ->
        ignore (Elab.infer ctx [] raw))

  let error_unify_mismatch () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(Lambda ("x", Some U, Ident "x")) in
    try
      ignore (Elab.check ctx [] raw VU);
      Alcotest.fail "expected unify error"
    with
    | Elab.Elab_error msg ->
        if String.starts_with ~prefix:"Cannot unify" msg then
          ()
        else
          Alcotest.failf "wrong error: %s" msg

  let non_pi_application () =
    reset_meta_context ();
    let ctx = Check.empty_context in
    let raw = Lang.Raw_syntax.(App (U, U)) in
    try
      let _tm, _ty = Elab.infer ctx [] raw in
      Alcotest.fail "expected unify error when applying to non-function"
    with
    | Elab.Elab_error msg ->
        if String.starts_with ~prefix:"Cannot unify" msg then
          ()
        else
          Alcotest.failf "wrong error: %s" msg

  let tests =
    [
      Alcotest.test_case "check identity" `Quick check_identity;
      Alcotest.test_case "infer unannotated" `Quick infer_unannotated;
      Alcotest.test_case "hole check" `Quick hole_check;
      Alcotest.test_case "hole infer" `Quick hole_infer;
      Alcotest.test_case "application" `Quick application;
      Alcotest.test_case "pi type" `Quick pi_type;
      Alcotest.test_case "let annotated check" `Quick let_annotated_check;
      Alcotest.test_case "let unannotated check" `Quick let_unannotated_check;
      Alcotest.test_case "let annotated infer" `Quick let_annotated_infer;
      Alcotest.test_case "let unannotated infer" `Quick let_unannotated_infer;
      Alcotest.test_case "arrow type" `Quick arrow_type;
      Alcotest.test_case "error: var not in scope" `Quick error_var_not_in_scope;
      Alcotest.test_case "error: unify mismatch" `Quick error_unify_mismatch;
      Alcotest.test_case "non-pi application" `Quick non_pi_application;
    ]
end

module Programs = struct
  let simple_id () =
    reset_meta_context ();
    let prog =
      [
        ( "id",
          Some Lang.Raw_syntax.(Arrow (U, U)),
          Lang.Raw_syntax.(Lambda ("x", Some U, Ident "x")) );
      ]
    in
    let result = Elab.elab_program prog in
    match result with
    | [ ("id", Lam ("x", Var 0), ty) ] -> (
        match ty with
        | VPi ("_", VU, Closure ([], U)) -> ()
        | _ -> Alcotest.fail "wrong type")
    | _ -> Alcotest.fail "program failed"

  let const () =
    reset_meta_context ();
    let prog =
      [
        ( "const",
          Some
            Lang.Raw_syntax.(
              Pi
                ( "A",
                  U,
                  Pi ("B", U, Arrow (Ident "A", Arrow (Ident "B", Ident "A")))
                )),
          Lang.Raw_syntax.(
            Lambda
              ( "A",
                Some U,
                Lambda
                  ( "B",
                    Some U,
                    Lambda
                      ( "x",
                        Some (Ident "A"),
                        Lambda ("y", Some (Ident "B"), Ident "x") ) ) )) );
      ]
    in
    let result = Elab.elab_program prog in
    match result with
    | [ ("const", tm, _ty) ] ->
        Alcotest.(check tm_testable)
          "same"
          (Lam ("A", Lam ("B", Lam ("x", Lam ("y", Var 1)))))
          tm
    | _ -> Alcotest.fail "const failed"

  let hole_solved () =
    reset_meta_context ();
    let prog =
      [ ("id", None, Lang.Raw_syntax.(Lambda ("x", None, Ident "x"))) ]
    in
    let result = Elab.elab_program prog in
    match result with
    | [ ("id", Lam ("x", Var 0), VPi _) ] -> ()
    | _ -> Alcotest.fail "hole solving failed"

  let multiple_defs () =
    reset_meta_context ();
    let prog =
      [
        ("A", Some Lang.Raw_syntax.U, Lang.Raw_syntax.U);
        ( "id",
          Some Lang.Raw_syntax.(Arrow (Ident "A", Ident "A")),
          Lang.Raw_syntax.(Lambda ("x", Some (Ident "A"), Ident "x")) );
      ]
    in
    let result = Elab.elab_program prog in
    match result with
    | [ ("A", U, VU); ("id", Lam ("x", Var 0), VPi _) ] -> ()
    | _ -> Alcotest.fail "multiple defs failed"

  let def_with_let () =
    reset_meta_context ();
    let prog =
      [
        ( "f",
          Some Lang.Raw_syntax.(Arrow (U, U)),
          Lang.Raw_syntax.(
            Lambda ("x", Some U, Let ("y", Some U, Ident "x", Ident "y"))) );
      ]
    in
    let result = Elab.elab_program prog in
    match result with
    | [ ("f", Lam ("x", Let ("y", U, Var 0, Var 0)), VPi _) ] -> ()
    | _ -> Alcotest.fail "def with let failed"

  let tests =
    [
      Alcotest.test_case "simple id" `Quick simple_id;
      Alcotest.test_case "const" `Quick const;
      Alcotest.test_case "hole solved" `Quick hole_solved;
      Alcotest.test_case "multiple defs" `Quick multiple_defs;
      Alcotest.test_case "def with let" `Quick def_with_let;
    ]
end

let () =
  Alcotest.run "Elaboration"
    [
      ("Eval", Test_eval.tests);
      ("Quote", Test_quote.tests);
      ("Nbe", Test_nbe.tests);
      ("Unify", Test_unify.tests);
      ("Elab", Test_elab.tests);
      ("Programs", Programs.tests);
    ]
