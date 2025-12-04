open Elaboration.Syntax
open Elaboration.Elab
open Elaboration.Pretty

let ty_testable : ty Alcotest.testable = Alcotest.testable pp_ty ( = )

module Test_eval = struct
  let identity () =
    let term = TmLam (None, TyUnit, TyUnit, TmVar 0) in
    let result = eval_tm [] term in
    match result with
    | VTmLam (None, VTyUnit, ClosTm ([], TmVar 0)) -> ()
    | _ -> Alcotest.fail "identity evaluation failed"

  let beta () =
    let term = TmApp (TmLam (None, TyUnit, TyUnit, TmVar 0), TmUnit) in
    let result = eval_tm [] term in
    match result with
    | VTmUnit -> ()
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
    let v = VTmNeutral (HVar 0, []) in
    let tm = quote_tm 1 v in
    Alcotest.(check string) "same" "#0" (tm_to_string tm)

  let lambda () =
    let v = VTmLam (None, VTyU, ClosTm ([], TmVar 0)) in
    let tm = quote_tm 0 v in
    match tm with
    | TmLam (_, _, _, TmVar 0) -> ()
    | _ -> Alcotest.fail "lambda quoting failed"

  let tests =
    [
      Alcotest.test_case "variable" `Quick variable;
      Alcotest.test_case "lambda" `Quick lambda;
    ]
end

module Test_nbe = struct
  let beta () =
    let term = TmApp (TmLam (None, TyUnit, TyUnit, TmVar 0), TmUnit) in
    let normalized = nf_tm [] term in
    match normalized with
    | TmUnit -> ()
    | _ -> Alcotest.failf "expected (), got %s" (tm_to_string normalized)

  let nested () =
    let term =
      TmApp
        ( TmLam (None, TyUnit, TyUnit, TmLam (None, TyUnit, TyUnit, TmVar 1)),
          TmUnit )
    in
    let normalized = nf_tm [] term in
    match normalized with
    | TmLam (_, _, _, TmUnit) -> ()
    | _ ->
        Alcotest.failf "expected Lam(_, ()), got %s" (tm_to_string normalized)

  let idempotent () =
    let term = TmApp (TmLam (None, TyUnit, TyUnit, TmVar 0), TmUnit) in
    let norm1 = nf_tm [] term in
    let norm2 = nf_tm [] norm1 in
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
    let ctx = Context.empty in
    let raw = RLam ([ (Some "x", Some RU) ], RIdent "x") in
    let expected = VTyPi (Some "x", VTyU, ClosTy ([], TyU)) in
    let tm = check_tm ctx raw expected in
    match tm with
    | TmLam (_, _, _, TmVar 0) -> ()
    | _ -> Alcotest.fail "check failed"

  let pi_type () =
    let ctx = Context.empty in
    let raw = RPi (([ Some "x" ], RU), RU) in
    let ty = check_ty ctx raw in
    Alcotest.(check ty_testable) "same" (TyPi (Some "x", TyU, TyU)) ty

  let arrow_type () =
    let ctx = Context.empty in
    let raw = RArrow (RU, RU) in
    let ty = check_ty ctx raw in
    Alcotest.(check ty_testable) "same" (TyArrow (TyU, TyU)) ty

  let error_var_not_in_scope () =
    let ctx = Context.empty in
    let raw = RIdent "x" in
    Alcotest.check_raises "var not in scope"
      (Elab_error "Variable not in scope: x") (fun () ->
        let _, _ = infer_tm ctx raw in
        ())

  let unit_type () =
    let ctx = Context.empty in
    let raw = RUnit in
    let ty = check_ty ctx raw in
    Alcotest.(check ty_testable) "same" TyUnit ty

  let unit_term_infer () =
    let ctx = Context.empty in
    let raw = RUnitTm in
    let tm, ty = infer_tm ctx raw in
    match (tm, ty) with
    | TmUnit, VTyUnit -> ()
    | _ -> Alcotest.fail "unit term infer failed"

  let tests =
    [
      Alcotest.test_case "check identity" `Quick check_identity;
      Alcotest.test_case "pi type" `Quick pi_type;
      Alcotest.test_case "arrow type" `Quick arrow_type;
      Alcotest.test_case "error: var not in scope" `Quick error_var_not_in_scope;
      Alcotest.test_case "unit type" `Quick unit_type;
      Alcotest.test_case "unit term infer" `Quick unit_term_infer;
    ]
end

module Programs = struct
  let simple_id () =
    let prog =
      [
        ( "id",
          RAnn (RLam ([ (Some "x", Some RU) ], RIdent "x"), RArrow (RU, RU)) );
      ]
    in
    let result = elab_program prog in
    match result with
    | [ ("id", TmLam (_, _, _, TmVar 0), ty) ] -> (
        match ty with
        | TyArrow (TyU, TyU) -> ()
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
