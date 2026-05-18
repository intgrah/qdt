#!/usr/bin/env fish

source (dirname (status filename))/lib.fish

set out (dirname (status filename))/data/cold.csv
mkdir -p (dirname $out)
echo "variant,trial,time_ms" >$out

set variants shake-c shake shake-rdeps salsa-c salsa less-busy

for variant in $variants
    for trial in (seq 5)
        set line ($QDT_BIN --root $QDT_STDLIB --build $variant Std 2>&1 | tail -1)
        set ms (string match -rg '\(([0-9.]+)ms\)' -- $line)
        if test -z "$ms"
            set ms NaN
        end
        echo "$variant,$trial,$ms" >>$out
        echo "$variant trial $trial: $ms ms"
    end
end

echo "Wrote $out"
