#!/usr/bin/env fish

source (dirname (status filename))/lib.fish

set repo_root (dirname (dirname (status filename)))
set conv_src $repo_root/Qdt/Conversion.lean
set with_flex_src $repo_root/bench/variants/Conversion.WithFlex.lean
set no_flex_src $repo_root/bench/variants/Conversion.NoFlex.lean
set out $repo_root/bench/data/conversion.csv

mkdir -p (dirname $out)
echo "variant,corpus,trial,time_ms" >$out

set saved_conv (mktemp)
cp $conv_src $saved_conv
function on_exit --on-event fish_exit
    cp $saved_conv $conv_src
    rm -f $saved_conv
end

set variants with-flex no-flex

set chain_ns 100 200 400
set triangle_ns 25 50 100
set discrete_ns 500 2000
set random_ns 1000 5000

for variant in $variants
    echo "$variant:"
    switch $variant
        case with-flex
            cp $with_flex_src $conv_src
        case no-flex
            cp $no_flex_src $conv_src
    end

    pushd $repo_root >/dev/null
    lake build qdt >/dev/null 2>&1
    popd >/dev/null

    set corpora_pairs \
        "stdlib examples/stdlib Std"
    for n in $chain_ns
        cd $repo_root/examples/long; and N=$n ./chain.sh >Chain.qdt; and cd $repo_root
        set corpora_pairs $corpora_pairs "chain_N$n examples/long Chain"
    end
    for n in $triangle_ns
        cd $repo_root/examples/long; and N=$n ./triangle.sh >Triangle.qdt; and cd $repo_root
        set corpora_pairs $corpora_pairs "triangle_N$n examples/long Triangle"
    end
    for n in $discrete_ns
        cd $repo_root/examples/long; and N=$n ./discrete.sh >Discrete.qdt; and cd $repo_root
        set corpora_pairs $corpora_pairs "discrete_N$n examples/long Discrete"
    end
    for n in $random_ns
        cd $repo_root/examples/long; and N=$n ./random.sh >Random.qdt; and cd $repo_root
        set corpora_pairs $corpora_pairs "random_N$n examples/long Random"
    end

    for entry in $corpora_pairs
        set parts (string split " " -- $entry)
        set label $parts[1]
        set root $parts[2]
        set module $parts[3]
        for trial in (seq 5)
            set line ($QDT_BIN --root $repo_root/$root --build shake-c $module 2>&1 | tail -1)
            set ms (string match -rg '\(([0-9]+)ms\)' -- $line)
            if test -z "$ms"
                set ms NaN
            end
            echo "$variant,$label,$trial,$ms" >>$out
            echo "  $label trial $trial: $ms ms"
        end
    end
end

echo "Wrote $out"
