#! /usr/bin/env nix-shell
#! nix-shell -i bash -p z3

RUNS=250


rm results.md
for stamp in $(ls *.smt)
do
    echo "# $stamp" >> results.md
    hyperfine --runs 250 --warmup 5 --ignore-failure \
              "z3 $stamp > /dev/null" \
              "./with-bindings-oneshot-from-c.bin $stamp > /dev/null" \
              "./with-bindings-from-c.bin $stamp > /dev/null" \
              "with-bindings-from-haskell.bin $stamp > /dev/null" \
              "with-shell-cmd-bytestring-from-haskell.bin $stamp > /dev/null" \
              "with-shell-cmd-from-haskell.bin $stamp > /dev/null" \
              --export-markdown tmp.md
    cat tmp.md >> results.md
    echo >> results.md
done
rm tmp.md
