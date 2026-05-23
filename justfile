lean_include := `lean --print-prefix` / "include"
c_sources := "FSWatch/c/rdcw.c FSWatch/c/inotify.c Incremental/c/shake.c"
qdt_bin := justfile_directory() / ".lake/build/bin/qdt"

default: qdt

install:
    ln -sf {{qdt_bin}} ~/.local/bin/qdt

qdt:
    lake build qdt

test:
    lake test

compile_commands:
    echo '{{c_sources}}' \
      | tr ' ' '\n' \
      | jq -Rs --arg dir "{{justfile_directory()}}" --arg inc "{{lean_include}}" \
        'split("\n") | map(select(. != "")) | map({directory: $dir, file: ., arguments: ["cc", "-I", $inc, "-c", .]})' \
      > compile_commands.json

stdlib:
    {{qdt_bin}} build --root examples/stdlib Std

normalisation-bench:
    {{qdt_bin}} build --root examples/normalisation-bench Bench

long NAME:
    cd examples/long && ./{{NAME}}.sh > {{capitalize(NAME)}}.qdt
    {{qdt_bin}} build --root examples/long {{capitalize(NAME)}}
