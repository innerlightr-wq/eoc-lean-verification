#!/bin/bash
# scan exact characteristic sums at larger prefix depths, sigma = top shell, t in {8,12,16}
for J in 30 40 50 60; do
  S=$(python3 -c "import math;print(math.floor($J*math.log2(3)))")
  for t in 8 12 16; do
    H=$(( (1<<t) - 1 )); [ $H -gt 4095 ] && H=4095
    ./phi_dp 0 $J $S $((S+t+1)) $H > scan_J${J}_t${t}.txt &
  done
done
wait
