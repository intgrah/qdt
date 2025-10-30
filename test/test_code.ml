open Code__Core
open Code__Nbe
open Code__Typecheck

let test_identity () =
  let id = Lambda (Var 0) in
  let _id_ty = Pi (Star, Star) in

  let ctx = [ StarV ] in
  check ctx 0 id (PiV (StarV, ([], Star)));
  print_endline "✓ Identity function type checks"

let test_eval_identity () =
  let id = Lambda (Var 0) in
  let id_val = eval [] id in

  match id_val with
  | LambdaV _ -> print_endline "✓ Identity evaluates to lambda"
  | _ -> failwith "Identity should evaluate to lambda"

let test_quote_identity () =
  let id = Lambda (Var 0) in
  let id_val = eval [] id in
  let id_quoted = quote id_val 0 in

  let _ = id_quoted in
  print_endline "✓ Identity can be quoted"

let test_beta_reduction () =
  let app = App (Lambda (Var 0), Lambda (Var 0)) in
  let result = eval [] app in

  match result with
  | LambdaV _ -> print_endline "✓ Beta reduction works"
  | _ -> failwith "Application should beta reduce"

let () =
  print_endline "Running tests...";
  test_identity ();
  test_eval_identity ();
  test_quote_identity ();
  test_beta_reduction ();
  print_endline "\nAll tests passed!"
