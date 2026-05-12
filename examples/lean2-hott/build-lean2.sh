#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
lean2_dir="$here/lean2"

if [ ! -d "$lean2_dir" ]; then
  echo "error: $lean2_dir not found. Run 'git submodule update --init' first." >&2
  exit 1
fi

cd "$lean2_dir"
patch_file="$here/lean2.patch"
if git apply --check "$patch_file" 2>/dev/null; then
  git apply "$patch_file"
elif ! git apply --check --reverse "$patch_file" 2>/dev/null; then
  echo "error: lean2.patch does not apply cleanly." >&2
  exit 1
fi

mkdir -p src/build
cd src/build
[ -f CMakeCache.txt ] || cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_POLICY_VERSION_MINIMUM=3.5 ..
make lean -j"$(nproc)"

lean=$lean2_dir/bin/lean
cd "$lean2_dir/hott"

build_one() {
  local f=$1
  local olean=${f%.hlean}.olean
  [ -e "$olean" ] && return 0
  for dep in $("$lean" --hlean --deps "$f"); do
    [[ $dep == *.olean ]] || continue
    local depsrc=${dep%.olean}.hlean
    [ -e "$depsrc" ] && build_one "$depsrc"
  done
  "$lean" --hlean -o "$olean" "$f"
}

find . -name '*.hlean' | while read -r f; do
  build_one "$f"
done

count=$(find . -name '*.olean' | wc -l)
echo "Built $count .olean files."
