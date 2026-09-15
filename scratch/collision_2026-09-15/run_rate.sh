#!/bin/bash
for J in 30 40 50 60 70; do
  S=$(python3 -c "import math;print(math.floor($J*math.log2(3)))")
  for off in 0 1; do ./phi_dp 0 $J $S $((S+13)) 4095 $off > rate_J${J}_off${off}.txt & done
done
./phi_dp 1 60 $(python3 -c "import math;print(math.floor(1+60*math.log2(3)))") $(python3 -c "import math;print(math.floor(1+60*math.log2(3))+13)") 4095 0 > rate_c1_J60.txt &
./phi_dp 0 60 93 $((93+13)) 4095 0 > rate_J60_gap2.txt &
wait
