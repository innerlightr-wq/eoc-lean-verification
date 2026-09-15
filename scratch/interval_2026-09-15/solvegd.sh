#!/bin/bash
# bisection for the extra deep-step amplitude rate gd giving chain constant C <= target (refined weights)
K=$1; tgt=$2; lo=0; hi=0.4
for it in $(seq 1 14); do
  mid=$(python3 -c "print(($lo+$hi)/2)")
  C=$(./c3chain3 $K 1 $mid | sed 's/.*: C=\([^ ]*\) .*/\1/')
  ok=$(python3 -c "print(1 if float('$C') <= $tgt else 0)")
  if [ $ok = 1 ]; then hi=$mid; else lo=$mid; fi
done
echo "K=$K target C<=$tgt : gd* = $hi"
