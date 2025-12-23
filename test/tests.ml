open Frontend
open Elaboration
open Syntax
open Elab
open Pretty
open Nbe

let ty_testable : ty Alcotest.testable = Alcotest.testable pp_ty ( = )
let genv = Global.empty

module Test_eval = struct
  let identity () =
    let term = TmLam (None, TyU, TmVar (Idx 0)) in
    let result = eval_tm genv [] term in
    match result with
    | VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) -> ()
    | _ -> Alcotest.fail "identity evaluation failed"

  let beta () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmConst [ "c" ]) in
    let result = eval_tm genv [] term in
    match result with
    | VTmNeutral (HConst [ "c" ], []) -> ()
    | _ -> Alcotest.fail "beta reduction failed"

  let pi_eval () =
    let ty = TyPi (None, TyU, TyU) in
    let result = eval_ty genv [] ty in
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
    let tm = quote_tm genv 1 v in
    match tm with
    | TmVar (Idx 0) -> ()
    | _ -> Alcotest.fail "variable quoting failed"

  let lambda () =
    let v = VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) in
    let tm = quote_tm genv 0 v in
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
  let whnf t = quote_tm genv 0 (eval_tm genv [] t)

  let beta () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmConst [ "c" ]) in
    let normalized = whnf term in
    match normalized with
    | TmConst _ -> ()
    | _ ->
        Alcotest.failf "expected a constant, got %s" (tm_to_string normalized)

  let nested () =
    let term =
      TmApp
        (TmLam (None, TyU, TmLam (None, TyU, TmVar (Idx 1))), TmConst [ "c" ])
    in
    let normalized = whnf term in
    match normalized with
    | TmLam (_, _, TmConst _) -> ()
    | _ ->
        Alcotest.failf "expected Lam(_, Const _), got %s"
          (tm_to_string normalized)

  let idempotent () =
    let term = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmConst [ "c" ]) in
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
    let ctx = Context.empty in
    let raw =
      Raw_syntax.Lam
        ([ Raw_syntax.Typed ([ Some "x" ], Raw_syntax.U) ], Raw_syntax.Ident "x")
    in
    let expected = VTyPi (Some "x", VTyU, ClosTy ([], TyU)) in
    let tm = check_tm genv ctx raw expected in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "check failed"

  let pi_type () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Pi (([ Some "x" ], Raw_syntax.U), Raw_syntax.U) in
    let ty = check_ty genv ctx raw in
    Alcotest.(check ty_testable) "same" (TyPi (Some "x", TyU, TyU)) ty

  let arrow_type () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Arrow (Raw_syntax.U, Raw_syntax.U) in
    let ty = check_ty genv ctx raw in
    Alcotest.(check ty_testable) "same" (TyPi (None, TyU, TyU)) ty

  let error_var_not_in_scope () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Ident "x" in
    Alcotest.check_raises "var not in scope" (Elab_error "Unbound variable: x")
      (fun () ->
        let _, _ = infer_tm genv ctx raw in
        ())

  let tests =
    [
      Alcotest.test_case "check identity" `Quick check_identity;
      Alcotest.test_case "pi type" `Quick pi_type;
      Alcotest.test_case "arrow type" `Quick arrow_type;
      Alcotest.test_case "error: var not in scope" `Quick error_var_not_in_scope;
    ]
end

module Programs = struct
  let simple_id () =
    let prog =
      [
        Raw_syntax.Def
          {
            name = "id";
            body =
              Raw_syntax.Ann
                ( Raw_syntax.Lam
                    ( [ Raw_syntax.Typed ([ Some "x" ], Raw_syntax.U) ],
                      Raw_syntax.Ident "x" ),
                  Raw_syntax.Arrow (Raw_syntax.U, Raw_syntax.U) );
          };
      ]
    in
    let result = elab_program prog in
    match result with
    | [ ([ "id" ], TmLam (_, _, TmVar (Idx 0)), ty) ] -> (
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
