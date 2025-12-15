open Elaboration.Syntax
open Elaboration.Elab
open Elaboration.Pretty

let ty_testable : ty Alcotest.testable = Alcotest.testable pp_ty ( = )

module Test_eval = struct
  let identity () =
    let term = TmLam (None, TyU, TmVar (Idx 0)) in
    let result = eval_tm [] term in
    match result with
    | VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) -> ()
    | _ -> Alcotest.fail "identity evaluation failed"

  let beta () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmIntHat) in
    let result = eval_tm [] term in
    match result with
    | VTmIntHat -> ()
    | _ -> Alcotest.fail "beta reduction failed"

  let pi_eval () =
    let ty = TyPi (None, TyU, TyU) in
    let result = eval_ty [] ty in
    match result with
    | VTyPi (None, VTyU, ClosTy ([], TyU)) -> ()
    | _ -> Alcotest.fail "pi evaluation failed"

  let tests =
    [
      Alcotest.test_case "identity" `Quick identity;
      Alcotest.test_case "beta" `Quick beta;
      Alcotest.test_case "pi eval" `Quick pi_eval;
    ]
end

module Test_quote = struct
  let variable () =
    let v = VTmNeutral (HVar (Lvl 0), []) in
    let tm = quote_tm 1 v in
    (* Variable at level 0 with quote level 1 -> index = 1-1-0 = 0 *)
    match tm with
    | TmVar (Idx 0) -> ()
    | _ -> Alcotest.fail "variable quoting failed"

  let lambda () =
    let v = VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) in
    let tm = quote_tm 0 v in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "lambda quoting failed"

  let tests =
    [
      Alcotest.test_case "variable" `Quick variable;
      Alcotest.test_case "lambda" `Quick lambda;
    ]
end

module Test_nbe = struct
  let whnf t = quote_tm 0 (eval_tm [] t)

  let beta () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmIntHat) in
    let normalized = whnf term in
    match normalized with
    | TmIntHat -> ()
    | _ -> Alcotest.failf "expected Int, got %s" (tm_to_string normalized)

  let nested () =
    let term =
      TmApp (TmLam (None, TyU, TmLam (None, TyU, TmVar (Idx 1))), TmIntHat)
    in
    let normalized = whnf term in
    match normalized with
    | TmLam (_, _, TmIntHat) -> ()
    | _ ->
        Alcotest.failf "expected Lam(_, Int), got %s" (tm_to_string normalized)

  let idempotent () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmIntHat) in
    let norm1 = whnf term in
    let norm2 = whnf norm1 in
    Alcotest.(check string) "same" (tm_to_string norm1) (tm_to_string norm2)

  let tests =
    [
      Alcotest.test_case "beta" `Quick beta;
      Alcotest.test_case "nested" `Quick nested;
      Alcotest.test_case "idempotent" `Quick idempotent;
    ]
end

module Test_elab = struct
  let check_identity () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.Lam ([ (Some "x", Some Raw.U) ], Raw.Ident "x") in
    let expected = VTyPi (Some "x", VTyU, ClosTy ([], TyU)) in
    let tm = check_tm genv ctx raw expected in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "check failed"

  let pi_type () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.Pi (([ Some "x" ], Raw.U), Raw.U) in
    let ty = check_ty genv ctx raw in
    Alcotest.(check ty_testable) "same" (TyPi (Some "x", TyU, TyU)) ty

  let arrow_type () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.Arrow (Raw.U, Raw.U) in
    let ty = check_ty genv ctx raw in
    Alcotest.(check ty_testable) "same" (TyPi (None, TyU, TyU)) ty

  let error_var_not_in_scope () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.Ident "x" in
    Alcotest.check_raises "var not in scope" (Elab_error "Unbound variable: x")
      (fun () ->
        let _, _ = infer_tm genv ctx raw in
        ())

  let int_type () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.Int in
    let ty = check_ty genv ctx raw in
    Alcotest.(check ty_testable) "same" TyInt ty

  let int_lit_infer () =
    let genv = GlobalEnv.create () in
    let ctx = Context.empty in
    let raw = Raw.IntLit 42 in
    let tm, ty = infer_tm genv ctx raw in
    match (tm, ty) with
    | TmIntLit 42, VTyInt -> ()
    | _ -> Alcotest.fail "int lit infer failed"

  let tests =
    [
      Alcotest.test_case "check identity" `Quick check_identity;
      Alcotest.test_case "pi type" `Quick pi_type;
      Alcotest.test_case "arrow type" `Quick arrow_type;
      Alcotest.test_case "error: var not in scope" `Quick error_var_not_in_scope;
      Alcotest.test_case "int type" `Quick int_type;
      Alcotest.test_case "int lit infer" `Quick int_lit_infer;
    ]
end

module Programs = struct
  let simple_id () =
    let prog =
      [
        Raw.Def
          ( "id",
            Raw.Ann
              ( Raw.Lam ([ (Some "x", Some Raw.U) ], Raw.Ident "x"),
                Raw.Arrow (Raw.U, Raw.U) ) );
      ]
    in
    let result = elab_program prog in
    match result with
    | [ ("id", TmLam (_, _, TmVar (Idx 0)), ty) ] -> (
        match ty with
        | TyPi (None, TyU, TyU) -> ()
        | _ -> Alcotest.fail "wrong type")
    | _ -> Alcotest.fail "program failed"

  let tests = [ Alcotest.test_case "simple id" `Quick simple_id ]
end

let () =
  Alcotest.run "Elaboration"
    [
      ("Eval", Test_eval.tests);
      ("Quote", Test_quote.tests);
      ("Nbe", Test_nbe.tests);
      ("Elab", Test_elab.tests);
      ("Programs", Programs.tests);
    ]
