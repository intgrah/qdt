#!/usr/bin/env fish

source (dirname (status filename))/lib.fish

set out (dirname (status filename))/data/scatter.csv
mkdir -p (dirname $out)
echo "file,category,cold_ms,incr_ms" >$out

set files (find $QDT_STDLIB/Std -name "*.qdt" -printf "%P\n" | sort)

set cold_csv (mktemp)
echo "=== per-file cold (one-shot, single trial) ==="
for f in $files
    set mod (string replace -r '\.qdt$' '' -- $f | string replace -a '/' '.')
    set line ($QDT_BIN --root $QDT_STDLIB --build shake-c "Std.$mod" 2>&1 | tail -1)
    set cold (string match -rg '\(([0-9.]+)ms\)' -- $line)
    test -z "$cold"; and set cold NaN
    echo "$f,$cold" >>$cold_csv
    echo "  Std.$mod: $cold ms"
end

function lookup_cold
    awk -F, -v key=$argv[2] '$1==key {print $2}' $argv[1]
end

echo ""
echo "=== per-file incremental, one watch session PER FILE (entry module = file) ==="
for f in $files
    set mod (string replace -r '\.qdt$' '' -- $f | string replace -a '/' '.')
    set corpus (fresh_corpus)
    set log (mktemp)
    set target $corpus/Std/$f

    if not start_watch shake-c $corpus $log "Std.$mod"
        rm -rf $corpus
        rm -f $log
        continue
    end

    cat $target >/tmp/_qdt_x
    mv /tmp/_qdt_x $target
    sync
    wait_for_rebuild $log $target
    set t (last_time_ms $log)
    set cold (lookup_cold $cold_csv $f)
    echo "$f,noop,$cold,$t" >>$out

    echo "" >>$target
    sync
    wait_for_rebuild $log $target
    set t (last_time_ms $log)
    set cold (lookup_cold $cold_csv $f)
    echo "$f,whitespace,$cold,$t" >>$out
    sed -i '$d' $target
    sync
    wait_for_rebuild $log $target

    set probe_name __scatter_probe_(string replace -a / _ -- $f | string replace -a . _)
    echo "def $probe_name : Nat := Nat.zero" >>$target
    sync
    wait_for_rebuild $log $target
    set t (last_time_ms $log)
    set cold (lookup_cold $cold_csv $f)
    echo "$f,hub-append,$cold,$t" >>$out
    sed -i '$d' $target
    sync
    wait_for_rebuild $log $target

    stop_watch
    rm -rf $corpus
    rm -f $log
    echo "  Std.$mod done"
end

echo ""
echo "Wrote $out"
wc -l $out
