let stdlib_path = ref ""
let code_exe = ref ""
let accept_pattern = Str.regexp "^accept_.*\\.qdt$"
let reject_pattern = Str.regexp "^reject_.*\\.qdt$"

let rec find_files dir pattern =
  let entries = Sys.readdir dir in
  Array.fold_left
    (fun acc entry ->
      let path = Filename.concat dir entry in
      if Sys.is_directory path then
        acc @ find_files path pattern
      else if Str.string_match pattern (Filename.basename path) 0 then
        path :: acc
      else
        acc)
    [] entries

let run_test path =
  let stdin, stdout, stderr =
    Unix.open_process_args_full !code_exe [| !code_exe; path |]
      [| "QDT_PATH=" ^ !stdlib_path |]
  in
  close_out_noerr stdout;
  let buf = Buffer.create 256 in
  let read_all ch =
    try
      while true do
        let c = input_char ch in
        Buffer.add_char buf c
      done
    with
    | End_of_file -> ()
  in
  read_all stderr;
  close_in_noerr stderr;
  read_all stdin;
  close_in_noerr stdin;
  let status = Unix.close_process_full (stdin, stdout, stderr) in
  let output = Buffer.contents buf in
  let exit_code =
    match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED _ -> -1
    | Unix.WSTOPPED _ -> -1
  in
  (exit_code, output)

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let test_accept path =
  let exit_code, output = run_test path in
  if exit_code = 0 then
    true
  else (
    Format.printf "FAIL %s (exit %d)\n%s\n" path exit_code output;
    false
  )

let test_reject path =
  let expected_path = Filename.remove_extension path ^ ".expected" in
  let exit_code, output = run_test path in
  let expected = read_file expected_path in
  if exit_code = 1 && output = expected then
    true
  else (
    Format.printf "FAIL %s\n" path;
    if exit_code <> 1 then Format.printf "  expected exit 1, got %d\n" exit_code;
    if output <> expected then (
      Format.printf "  expected:\n%s" expected;
      Format.printf "  actual:\n%s" output
    );
    false
  )

let () =
  if Array.length Sys.argv < 4 then (
    Format.eprintf "Usage: %s <code_exe> <stdlib_path> <test_dir>\n"
      Sys.argv.(0);
    exit 1
  );
  code_exe := Sys.argv.(1);
  stdlib_path := Sys.argv.(2);
  let test_dir = Sys.argv.(3) in
  let accept_tests = find_files test_dir accept_pattern in
  let reject_tests = find_files test_dir reject_pattern in
  let passed = ref 0 in
  let failed = ref 0 in
  List.iter
    (fun path ->
      if test_accept path then
        incr passed
      else
        incr failed)
    (List.sort String.compare accept_tests);
  List.iter
    (fun path ->
      if test_reject path then
        incr passed
      else
        incr failed)
    (List.sort String.compare reject_tests);
  Format.printf "%d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
