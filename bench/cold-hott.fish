#!/usr/bin/env fish

set REPO_ROOT (realpath (dirname (status filename))/..)
set QDT_BIN $REPO_ROOT/.lake/build/bin/qdt
set HOTT_ROOT $REPO_ROOT/examples/lean2-hott/build/qdt

set out (dirname (status filename))/data/cold-hott.csv
mkdir -p (dirname $out)
echo "variant,trial,time_ms" >$out

set variants shake-c shake shake-rdeps salsa-c salsa

for variant in $variants
    for trial in (seq 5)
        set line ($QDT_BIN --root $HOTT_ROOT --build $variant init/default 2>&1 | tail -1)
        set ms (string match -rg '\(([0-9.]+)ms\)' -- $line)
        if test -z "$ms"
            echo "$variant,$trial,NaN" >>$out
            echo "  $variant trial $trial: timeout"
        else
            echo "$variant,$trial,$ms" >>$out
            echo "  $variant trial $trial: $ms ms"
        end
    end
end

echo "Wrote $out"
