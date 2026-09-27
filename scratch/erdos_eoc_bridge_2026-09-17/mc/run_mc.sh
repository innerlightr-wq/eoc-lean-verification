#!/bin/bash
# 8 parallel seeds, eta = 1/54 (black model, what the rigorous operators bound) and 1/108 (dark threshold d)
cd "$(dirname "$0")"
for eta in 54 108; do
  for seed in 1 2 3 4; do
    ./haarwin 24 1500000 $eta $((seed*1000+eta)) 2 4 6 8 10 12 14 16 18 20 24 > out_${eta}_${seed}.txt &
  done
  wait
done
echo done > MC_DONE
