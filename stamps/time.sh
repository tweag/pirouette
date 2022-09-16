#! /usr/bin/env nix-shell
#! nix-shell -i bash -p z3

rm results
for stamp in $(ls *.smt)
do
    echo "-----------------------------------" >> results
    echo $stamp >> results
    (time z3 $stamp > /dev/null) &>> results
    echo "when run directly from a shell" >> results
    (time ./with-shell-cmd-from-haskell $stamp > /dev/null) &>> results
    echo "when launched from a haskell binary" >> results
    echo >> results
done
