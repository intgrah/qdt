open Core
open Syntax
open Semantics

let vtm_testable : vtm Alcotest.testable = Alcotest.testable Pretty.pp_vtm ( = )
let vty_testable : vty Alcotest.testable = Alcotest.testable Pretty.pp_vty ( = )
let whnf_tm = Nbe.eval_tm Global.empty []
let whnf_ty = Nbe.eval_ty Global.empty []
let id = TmLam (None, TyU, TmVar (Idx 0))
let k = TmLam (None, TyU, TmLam (None, TyU, TmVar (Idx 1)))

let identity () =
  let term : tm = id in
  let result : vtm = whnf_tm term in
  let expected : vtm = VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) in
  Alcotest.check vtm_testable "same" expected result

let beta () =
  let term : tm = TmApp (TmLam (None, TyU, TmVar (Idx 0)), TmConst [ "c" ]) in
  let result : vtm = whnf_tm term in
  let expected : vtm = VTmNeutral (HConst [ "c" ], []) in
  Alcotest.check vtm_testable "same" expected result

let pi () =
  let ty : ty = TyPi (None, TyU, TyU) in
  let result : vty = whnf_ty ty in
  let expected : vty = VTyPi (None, VTyU, ClosTy ([], TyU)) in
  Alcotest.check vty_testable "same" expected result

let nested () =
  let term : tm = TmApp (TmApp (k, TmConst [ "a" ]), TmConst [ "b" ]) in
  let result : vtm = whnf_tm term in
  let expected : vtm = VTmNeutral (HConst [ "a" ], []) in
  Alcotest.check vtm_testable "captures" expected result

let tests =
  [
    Alcotest.test_case "identity" `Quick identity;
    Alcotest.test_case "beta" `Quick beta;
    Alcotest.test_case "pi" `Quick pi;
    Alcotest.test_case "nested" `Quick nested;
  ]
