#! /usr/bin/env nix-shell
#! nix-shell -i bash -p z3

for stamp in $(ls *.smt)
do
    echo $stamp >> results
    (time z3 $stamp > /dev/null) &>> results
    echo >> results
done
