open Frontend
open Elaboration
open Syntax
open Elab
open Pretty

let ty_testable : ty Alcotest.testable = Alcotest.testable pp_ty ( = )

module Test_quote = struct
  let variable () =
    let v = VTmNeutral (HVar (Lvl 0), []) in
    let tm = Quote.quote_tm Global.empty 1 v in
    match tm with
    | TmVar (Idx 0) -> ()
    | _ -> Alcotest.fail "variable quoting failed"

  let lambda () =
    let v = VTmLam (None, VTyU, ClosTm ([], TmVar (Idx 0))) in
    let tm = Quote.quote_tm Global.empty 0 v in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "lambda quoting failed"

  let tests =
    [
      Alcotest.test_case "variable" `Quick variable;
      Alcotest.test_case "lambda" `Quick lambda;
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
    let tm = Bidir.check_tm Global.empty ctx raw expected in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "check failed"

  let pi_type () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Pi (([ Some "x" ], Raw_syntax.U), Raw_syntax.U) in
    let ty = Bidir.check_ty Global.empty ctx raw in
    Alcotest.check ty_testable "same" (TyPi (Some "x", TyU, TyU)) ty

  let arrow_type () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Arrow (Raw_syntax.U, Raw_syntax.U) in
    let ty = Bidir.check_ty Global.empty ctx raw in
    Alcotest.check ty_testable "same" (TyPi (None, TyU, TyU)) ty

  let error_var_not_in_scope () =
    let ctx = Context.empty in
    let raw = Raw_syntax.Ident "x" in
    Alcotest.check_raises "var not in scope" (Elab_error "Unbound variable: x")
      (fun () ->
        let _, _ = Bidir.infer_tm Global.empty ctx raw in
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
            ty_opt = Some (Raw_syntax.Arrow (Raw_syntax.U, Raw_syntax.U));
            body =
              Raw_syntax.Lam
                ( [ Raw_syntax.Typed ([ Some "x" ], Raw_syntax.U) ],
                  Raw_syntax.Ident "x" );
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

module Qdt_files = struct
  let read_file path = In_channel.with_open_text path In_channel.input_all

  let parse source =
    let chars = List.of_seq (String.to_seq source) in
    let tokens = Lexer.scan [] chars in
    Parser.parse tokens

  let elaborate_file ~root path =
    let source = read_file path in
    let prog = parse source in
    elab_program_with_imports ~root ~read_file ~parse prog

  let root_dir () = Filename.dirname (Sys.getcwd ())

  let check_succeeds path () =
    let root = root_dir () in
    match elaborate_file ~root path with
    | _ -> ()
    | exception exn ->
        Alcotest.failf "expected %s to elaborate, but got: %s" path
          (Printexc.to_string exn)

  let check_fails path () =
    let root = root_dir () in
    match elaborate_file ~root path with
    | _ -> Alcotest.failf "expected %s to fail, but it elaborated" path
    | exception _ -> ()

  let passing = [ "../Std.qdt"; "../examples/test.qdt" ]

  let failing =
    [
      "../examples/bad.qdt";
      "../examples/reject_negative_contra.qdt";
      "../examples/reject_negative_direct.qdt";
      "../examples/reject_negative_nested.qdt";
      "../examples/reject_nested_def.qdt";
      "../examples/reject_wrong_return.qdt";
    ]

  let tests =
    List.map
      (fun path ->
        Alcotest.test_case ("pass: " ^ path) `Slow (check_succeeds path))
      passing
    @ List.map
        (fun path ->
          Alcotest.test_case ("fail: " ^ path) `Quick (check_fails path))
        failing
end

let () =
  Alcotest.run "Elaboration"
    [
      ("Quote", Test_quote.tests);
      ("Nbe", Test_nbe.tests);
      ("Elab", Test_elab.tests);
      ("Programs", Programs.tests);
      ("QDT files", Qdt_files.tests);
    ]
