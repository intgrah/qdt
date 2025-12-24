open Elaboration
open Syntax

let vl_tm_testable : vl_tm Alcotest.testable =
  Alcotest.testable Pretty.pp_vl_tm ( = )

let vl_ty_testable : vl_ty Alcotest.testable =
  Alcotest.testable Pretty.pp_vl_ty ( = )

let whnf_tm = Nbe.eval_tm Global.empty []
let whnf_ty = Nbe.eval_ty Global.empty []
let id = TmLam (None, TyU, TmVar (Idx 0))
let k = TmLam (None, TyU, TmLam (None, TyU, TmVar (Idx 1)))

let identity () =
  let term : tm = id in
  let result : vl_tm = whnf_tm term in
  let expected : vl_tm = VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) in
  Alcotest.check vl_tm_testable "same" expected result

let beta () =
  let term : tm = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmConst [ "c" ]) in
  let result : vl_tm = whnf_tm term in
  let expected : vl_tm = VTmNeutral (HConst [ "c" ], []) in
  Alcotest.check vl_tm_testable "same" expected result

let pi () =
  let ty : ty = TyPi (None, TyU, TyU) in
  let result : vl_ty = whnf_ty ty in
  let expected : vl_ty = VTyPi (None, VTyU, ClosTy ([], TyU)) in
  Alcotest.check vl_ty_testable "same" expected result

let nested () =
  let term : tm = TmApp (TmApp (k, TmConst [ "a" ]), TmConst [ "b" ]) in
  let result : vl_tm = whnf_tm term in
  let expected : vl_tm = VTmNeutral (HConst [ "a" ], []) in
  Alcotest.check vl_tm_testable "captures" expected result

let tests =
  [
    Alcotest.test_case "identity" `Quick identity;
    Alcotest.test_case "beta" `Quick beta;
    Alcotest.test_case "pi" `Quick pi;
    Alcotest.test_case "nested" `Quick nested;
  ]
