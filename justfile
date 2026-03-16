lean_include := `lean --print-prefix` / "include"
c_sources := "FSWatch/c/rdcw.c FSWatch/c/inotify.c Incremental/c/shake.c"

default: qdt qdt-lsp

install:
    ln -sf {{justfile_directory()}}/.lake/build/bin/qdt ~/.local/bin/qdt
    ln -sf {{justfile_directory()}}/.lake/build/bin/qdt-lsp ~/.local/bin/qdt-lsp

qdt:
    lake build qdt

qdt-lsp:
    lake build qdt-lsp

test:
    lake test

compile_commands:
    echo '{{c_sources}}' \
      | tr ' ' '\n' \
      | jq -Rs --arg dir "{{justfile_directory()}}" --arg inc "{{lean_include}}" \
        'split("\n") | map(select(. != "")) | map({directory: $dir, file: ., arguments: ["cc", "-I", $inc, "-c", .]})' \
      > compile_commands.json

stdlib:
    qdt --root examples/stdlib Std

normalisation-bench:
    qdt --root examples/normalisation-bench Bench

long-discrete:
    cd examples/long && ./discrete.sh > Discrete.qdt
    qdt --root examples/long Discrete

long-chain:
    cd examples/long && ./chain.sh > Chain.qdt
    qdt --root examples/long Chain

long-random:
    cd examples/long && ./random.sh > Random.qdt
    qdt --root examples/long Random

long-triangle:
    cd examples/long && ./triangle.sh > Triangle.qdt
    qdt --root examples/long Triangle
