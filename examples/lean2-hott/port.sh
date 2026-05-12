#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
out_dir_raw=${1:-$here/build/qdt}
mkdir -p "$out_dir_raw"
out_dir=$(cd "$out_dir_raw" && pwd)
txt_dir=${TXT_DIR:-$here/build/txt}
mkdir -p "$txt_dir"
txt_dir=$(cd "$txt_dir" && pwd)

if [ -n "${LEAN2_DIR-}" ]; then
  lean2=$LEAN2_DIR/bin/lean
  hott_dir=$LEAN2_DIR/hott
elif [ -n "${LEAN2_BIN-}" ] && [ -n "${LEAN2_HOTT-}" ]; then
  lean2=$LEAN2_BIN
  hott_dir=$LEAN2_HOTT
elif [ -x "$here/lean2/bin/lean" ] && [ -d "$here/lean2/hott" ]; then
  lean2=$here/lean2/bin/lean
  hott_dir=$here/lean2/hott
else
  echo "error: cannot locate a built lean2 tree." >&2
  echo "  Set LEAN2_DIR=<path-to-built-lean2>," >&2
  echo "  or LEAN2_BIN=<path-to-bin/lean> and LEAN2_HOTT=<path-to-hott/>," >&2
  echo "  or build the submodule at $here/lean2 with bin/linja." >&2
  exit 1
fi

if [ ! -x "$lean2" ]; then
  echo "error: $lean2 is not executable." >&2
  exit 1
fi
if [ ! -d "$hott_dir" ]; then
  echo "error: $hott_dir not found." >&2
  exit 1
fi
echo "lean2 binary: $lean2"
echo "hott sources: $hott_dir"

if ! find "$hott_dir" -maxdepth 2 -name '*.olean' -print -quit | grep -q .; then
  echo "warning: no .olean files found under $hott_dir." >&2
  echo "  The export will fail because lean2 cannot resolve imports." >&2
  echo "  Run 'bin/linja' from the lean2 tree to build the library first." >&2
fi

export_one() {
  local src=$1 stem=$2
  "$lean2" --hlean --export="$txt_dir/$stem.txt" "$src" >/dev/null
}

echo "Exporting from $hott_dir → $txt_dir"
for f in "$hott_dir"/*.hlean; do
  [ -e "$f" ] || continue
  stem=$(basename "$f" .hlean)
  export_one "$f" "$stem"
done

for f in "$hott_dir"/init/*.hlean; do
  [ -e "$f" ] || continue
  stem=$(basename "$f" .hlean)
  export_one "$f" "init.$stem"
done

find "$hott_dir" -mindepth 2 -name '*.hlean' \
  ! -path "$hott_dir/init/*" | while read -r f; do
  rel=${f#$hott_dir/}
  rel=${rel%.hlean}
  stem=${rel//\//.}
  export_one "$f" "$stem"
done

export_one "$hott_dir/init/default.hlean" "init"

txt_count=$(find "$txt_dir" -name '*.txt' | wc -l)
echo "Exported $txt_count modules"

echo "Converting to .qdt in $out_dir"
cd "$(dirname "$here")/.."
lake env lean --run "$here/Lean2Export.lean" "$txt_dir" "$out_dir"
qdt_count=$(find "$out_dir" -name '*.qdt' | wc -l)
echo "Wrote $qdt_count .qdt files."
