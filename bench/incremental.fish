#!/usr/bin/env fish

source (dirname (status filename))/lib.fish

set out (dirname (status filename))/data/incremental.csv
mkdir -p (dirname $out)
echo "variant,category,trial,time_ms,errors" >$out

set variants shake-c shake-rdeps salsa-c salsa
set categories noop whitespace body-clean body-broken leaf-type delete-replace hub-append parse-error

for variant in $variants
    echo "=== $variant ==="
    set corpus (fresh_corpus)
    set log (mktemp)
    set snap (mktemp -d)

    if not start_watch $variant $corpus $log
        echo "$variant: cold timeout, skipping" >&2
        rm -rf $corpus $snap
        rm -f $log
        continue
    end
    set cold_ms (last_time_ms $log)
    set cold_err (last_errors $log)
    echo "$variant,cold,0,$cold_ms,$cold_err" >>$out
    echo "  cold: $cold_ms ms"

    apply_edit noop $corpus
    wait_for_rebuild $log $LAST_EDIT_TARGET
    apply_edit noop $corpus
    wait_for_rebuild $log $LAST_EDIT_TARGET

    snapshot_corpus $corpus $snap

    for trial in (seq 5)
        for category in $categories
            apply_edit $category $corpus
            wait_for_rebuild $log $LAST_EDIT_TARGET
            set t (last_time_ms $log)
            set e (last_errors $log)
            echo "$variant,$category,$trial,$t,$e" >>$out
            restore_snapshot $corpus $snap
            wait_for_rebuild $log $corpus/Std/Nat.qdt
        end
        echo "  trial $trial complete"
    end

    apply_edit hub-rename $corpus
    wait_for_rebuild $log $LAST_EDIT_TARGET
    set t (last_time_ms $log)
    set e (last_errors $log)
    echo "$variant,hub-rename,1,$t,$e" >>$out
    echo "  hub-rename: $t ms ($e errors)"
    restore_snapshot $corpus $snap
    wait_for_rebuild $log $corpus/Std/Nat.qdt

    stop_watch
    rm -rf $corpus $snap
    rm -f $log
end

echo "Wrote $out"
