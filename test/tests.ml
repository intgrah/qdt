open Frontend
open Elaboration
open Syntax
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
      Ast.Lam
        (None, Ast.Typed (None, Some "x", Ast.U None), Ast.Ident (None, "x"))
    in
    let expected = VTyPi (Some "x", VTyU, ClosTy ([], TyU)) in
    let tm = Bidir.check_tm Global.empty ctx raw expected in
    match tm with
    | TmLam (_, _, TmVar (Idx 0)) -> ()
    | _ -> Alcotest.fail "check failed"

  let pi_type () =
    let ctx = Context.empty in
    let raw = Ast.Pi (None, (None, Some "x", Ast.U None), Ast.U None) in
    let ty = Bidir.check_ty Global.empty ctx raw in
    Alcotest.check ty_testable "same" (TyPi (Some "x", TyU, TyU)) ty

  let arrow_type () =
    let ctx = Context.empty in
    let raw = Ast.Pi (None, (None, None, Ast.U None), Ast.U None) in
    let ty = Bidir.check_ty Global.empty ctx raw in
    Alcotest.check ty_testable "same" (TyPi (None, TyU, TyU)) ty

  let error_var_not_in_scope () =
    let ctx = Context.empty in
    let raw = Ast.Ident (None, "x") in
    Alcotest.check_raises "var not in scope"
      (Elaboration.Error.Error
         { message = "Unbound variable: x"; location = None; kind = Type_check })
      (fun () -> ignore (Bidir.infer_tm Global.empty ctx raw))

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
        Ast.Command.Definition
          {
            src = None;
            name = "id";
            params = [ (None, Some "x", Ast.U None) ];
            ty_opt = Some (Ast.U None);
            body = Ast.Ident (None, "x");
          };
      ]
    in
    let genv =
      Elab.elab_program_with_imports ~root:"." ~read_file:(fun _ -> "") prog
    in
    match Global.find_opt [ "id" ] genv with
    | Some (Global.Def { ty; _ }) ->
        Alcotest.check ty_testable "same" (TyPi (Some "x", TyU, TyU)) ty
    | _ -> Alcotest.fail "program failed"

  let tests = [ Alcotest.test_case "simple id" `Quick simple_id ]
end

module Qdt_files = struct
  (* Find project root: look for dune-project marker file.
     Start from test binary location (_build/default/test/tests.exe),
     go up to project root. *)
  let project_root =
    let rec find_root dir =
      if Sys.file_exists (Filename.concat dir "dune-project") then
        dir
      else
        let parent = Filename.dirname dir in
        if parent = dir then
          (* Fallback: if we can't find it, assume current directory *)
          Sys.getcwd ()
        else
          find_root parent
    in
    (* Start from directory containing the test binary *)
    let test_dir =
      try Filename.dirname Sys.executable_name with
      | Sys_error _ -> Sys.getcwd ()
    in
    find_root test_dir

  (* Run the actual binary, like Lean does. This ensures we test the same code path as users.
     Returns (exit_code, output).
     Change to project_root so relative paths work correctly. *)
  let run_binary path =
    let old_dir = Sys.getcwd () in
    try
      Sys.chdir project_root;
      let cmd =
        Printf.sprintf "./_build/default/bin/main.exe --root=stdlib %s 2>&1"
          path
      in
      let ic = Unix.open_process_in cmd in
      let output = In_channel.input_all ic in
      let exit_code = Unix.close_process_in ic in
      let exit_code =
        match exit_code with
        | Unix.WEXITED n -> n
        | _ -> 1
      in
      Sys.chdir old_dir;
      (exit_code, output)
    with
    | exn ->
        Sys.chdir old_dir;
        raise exn

  let contains_substring str substr =
    let len_str = String.length str in
    let len_sub = String.length substr in
    if len_sub > len_str then
      false
    else
      let rec check i =
        if i + len_sub > len_str then
          false
        else if String.sub str i len_sub = substr then
          true
        else
          check (i + 1)
      in
      check 0

  let has_error output =
    let output_lower = String.lowercase_ascii output in
    contains_substring output_lower "error"
    || contains_substring output_lower "failed"

  let check_succeeds path () =
    let exit_code, output = run_binary path in
    (* Check for error messages in output *)
    if has_error output || exit_code <> 0 then
      Alcotest.failf "expected %s to elaborate successfully, but got:\n%s" path
        output

  (* Check that a file fails with a specific error message *)
  let check_fails_with path expected_error () =
    let exit_code, output = run_binary path in
    let output_lower = String.lowercase_ascii output in
    let expected_lower = String.lowercase_ascii expected_error in
    if not (contains_substring output_lower expected_lower) then
      Alcotest.failf
        "expected %s to fail with error containing '%s', but got:\n%s" path
        expected_error output
    else if exit_code = 0 && not (has_error output) then
      Alcotest.failf "expected %s to fail, but it elaborated successfully:\n%s"
        path output

  let check_fails path () =
    let exit_code, output = run_binary path in
    (* File should fail - check for error messages *)
    if (not (has_error output)) && exit_code = 0 then
      Alcotest.failf "expected %s to fail, but it elaborated successfully:\n%s"
        path output

  let passing = [ "stdlib/Std.qdt" ]

  (* Tests that should fail with generic error checking *)
  let failing =
    [
      "examples/reject_negative_contra.qdt";
      "examples/reject_negative_direct.qdt";
      "examples/reject_negative_nested.qdt";
      "examples/reject_nested_def.qdt";
      "examples/reject_wrong_return.qdt";
    ]

  (* Tests that should fail with specific error messages *)
  let failing_with_specific_errors =
    [
      ("examples/reject_nat_ext.qdt", "Type mismatch");
      (* Add more specific error tests here *)
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
    @ List.map
        (fun (path, error) ->
          Alcotest.test_case
            ("fail with: " ^ error ^ " in " ^ path)
            `Quick
            (check_fails_with path error))
        failing_with_specific_errors
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
