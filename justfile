lean_include := `lean --print-prefix` / "include"
c_sources := "FSWatch/c/rdcw.c FSWatch/c/inotify.c Incremental/c/shake.c"

default: qdt qdt-lsp

qdt:
    lake build qdt
    cp .lake/build/bin/qdt ~/.local/bin

qdt-lsp:
    lake build qdt-lsp
    cp .lake/build/bin/qdt-lsp ~/.local/bin

compile_commands:
    echo '{{c_sources}}' \
      | tr ' ' '\n' \
      | jq -Rs --arg dir "{{justfile_directory()}}" --arg inc "{{lean_include}}" \
        'split("\n") | map(select(. != "")) | map({directory: $dir, file: ., arguments: ["cc", "-I", $inc, "-c", .]})' \
      > compile_commands.json
