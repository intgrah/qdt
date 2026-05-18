set -g REPO_ROOT (realpath (dirname (status filename))/..)
set -g QDT_BIN $REPO_ROOT/.lake/build/bin/qdt
set -g QDT_STDLIB $REPO_ROOT/examples/stdlib
set -g WATCH_PID 0

function start_watch
    set variant $argv[1]
    set corpus $argv[2]
    set log $argv[3]
    set module $argv[4]
    test -z "$module"; and set module Std
    rm -f $log
    nohup stdbuf -oL $QDT_BIN --root $corpus --build $variant -w $module >$log 2>&1 &
    set -g WATCH_PID $last_pid
    disown
    while not grep -qE '^(OK|[0-9]+ error)' $log 2>/dev/null
        sleep 0.2
    end
    return 0
end

function stop_watch
    if test $WATCH_PID -ne 0
        kill $WATCH_PID 2>/dev/null
        sleep 0.3
        set -g WATCH_PID 0
    end
end

function wait_for_rebuild
    set log $argv[1]
    set touch_target $argv[2]
    set before (wc -l < $log)
    set tries 0
    while test (wc -l < $log) -le $before
        sleep 0.1
        set tries (math $tries + 1)
        if test $tries -eq 50; and test -n "$touch_target"
            cat $touch_target >/tmp/_qdt_nudge
            mv /tmp/_qdt_nudge $touch_target
            sync
        end
    end
    return 0
end

function last_time_ms
    set log $argv[1]
    tail -1 $log | grep -oE '\([0-9.]+ms\)' | grep -oE '[0-9.]+'
end

function last_errors
    set log $argv[1]
    set line (tail -1 $log)
    set matched (string match -rg '^([0-9]+) error' -- $line)
    if test -n "$matched"
        echo $matched
    else
        echo 0
    end
end

function apply_edit
    set kind $argv[1]
    set corpus $argv[2]
    set -g LAST_EDIT_TARGET ""
    switch $kind
        case noop
            set -g LAST_EDIT_TARGET $corpus/Std/Ackermann.qdt
            cat $corpus/Std/Ackermann.qdt >/tmp/_qdt_x
            mv /tmp/_qdt_x $corpus/Std/Ackermann.qdt
        case whitespace
            set -g LAST_EDIT_TARGET $corpus/Std/Sigma.qdt
            echo "" >>$corpus/Std/Sigma.qdt
        case body-clean
            set -g LAST_EDIT_TARGET $corpus/Std/Ackermann.qdt
            sed -i '0,/Eq.refl.{0} Nat (Nat.succ n)/{s|Eq.refl.{0} Nat (Nat.succ n)|Eq.refl.{0} Nat (ack 0 n)|}' $corpus/Std/Ackermann.qdt
        case body-broken
            set -g LAST_EDIT_TARGET $corpus/Std/Ackermann.qdt
            sed -i '0,/Nat.succ n/{s|Nat.succ n|Nat.succ (Nat.succ n)|}' $corpus/Std/Ackermann.qdt
        case hub-append
            set -g LAST_EDIT_TARGET $corpus/Std/Nat.qdt
            echo "def __hub_append : Nat := Nat.zero" >>$corpus/Std/Nat.qdt
        case hub-rename
            set -g LAST_EDIT_TARGET $corpus/Std/Nat.qdt
            sed -i 's|^def Nat.add (m : Nat) : Nat → Nat :=|def Nat.addX (m : Nat) : Nat → Nat :=|' $corpus/Std/Nat.qdt
        case leaf-type
            set -g LAST_EDIT_TARGET $corpus/Std/Nat.qdt
            sed -i 's|^def Nat.factorial : Nat → Nat :=|def Nat.factorial : Nat → Bool :=|' $corpus/Std/Nat.qdt
        case delete-replace
            set -g LAST_EDIT_TARGET $corpus/Std/Nat.qdt
            sed -i 's|Nat\.pow|Nat.pow2|g' $corpus/Std/Nat.qdt
        case parse-error
            set -g LAST_EDIT_TARGET $corpus/Std/Sigma.qdt
            echo "def __parse_error" >>$corpus/Std/Sigma.qdt
        case '*'
            echo "apply_edit: unknown category '$kind'" >&2
            return 1
    end
    sync
end

function snapshot_corpus
    set corpus $argv[1]
    set snap $argv[2]
    mkdir -p $snap
    cp $corpus/Std/Ackermann.qdt $snap/Ackermann.qdt
    cp $corpus/Std/Nat.qdt $snap/Nat.qdt
    cp $corpus/Std/Sigma.qdt $snap/Sigma.qdt
end

function restore_snapshot
    set corpus $argv[1]
    set snap $argv[2]
    cp $snap/Ackermann.qdt $corpus/Std/Ackermann.qdt
    cp $snap/Nat.qdt $corpus/Std/Nat.qdt
    cp $snap/Sigma.qdt $corpus/Std/Sigma.qdt
    sync
end

function fresh_corpus
    set d (mktemp -d)
    cp -r $QDT_STDLIB/* $d/
    echo $d
end
