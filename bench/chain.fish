#!/usr/bin/env fish

source (dirname (status filename))/lib.fish

set out (dirname (status filename))/data/chain.csv
mkdir -p (dirname $out)
echo "n,variant,kind,trial,time_ms" >$out

set Ns 50 100 200 400
set variants shake-c shake-rdeps

set chain_gen ~/git/intgrah/ii/code/examples/long/chain.sh

for n in $Ns
    set corpus (mktemp -d)
    env N=$n bash $chain_gen >$corpus/Chain.qdt

    for variant in $variants
        for trial in (seq 5)
            set line ($QDT_BIN --root $corpus --build $variant Chain 2>&1 | tail -1)
            set ms (string match -rg '\(([0-9.]+)ms\)' -- $line)
            test -z "$ms"; and set ms NaN
            echo "$n,$variant,cold,$trial,$ms" >>$out
        end

        set log (mktemp)
        if not start_watch $variant $corpus $log Chain
            rm -f $log
            continue
        end
        cat $corpus/Chain.qdt >/tmp/_qdt_x
        mv /tmp/_qdt_x $corpus/Chain.qdt
        wait_for_rebuild $log $corpus/Chain.qdt

        for trial in (seq 3)
            sed -i 's|^def n0 : Nat := Nat.zero|def n0 : Nat := Nat.succ Nat.zero|' $corpus/Chain.qdt
            sync
            wait_for_rebuild $log $corpus/Chain.qdt
            set t (last_time_ms $log)
            echo "$n,$variant,root-edit,$trial,$t" >>$out
            sed -i 's|^def n0 : Nat := Nat.succ Nat.zero|def n0 : Nat := Nat.zero|' $corpus/Chain.qdt
            sync
            wait_for_rebuild $log $corpus/Chain.qdt
        end

        stop_watch
        rm -f $log
        echo "  N=$n $variant done"
    end

    rm -rf $corpus
end

echo "Wrote $out"
