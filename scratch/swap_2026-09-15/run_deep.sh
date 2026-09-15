#!/bin/bash
# exhaustive h <= 4095 at the A=0.7 modulus ratio t ~ 0.1736 j0, sigma = top shell
run() { J=$1; t=$2; a=$3; b=$4; S=$(python3 -c "import math;print(math.floor($J*math.log2(3)))"); ./deep_dp 0 $J $S $t $a $b 0.05 > deep_J${J}_t${t}_${a}.txt 2>&1; }
run 100 17 1 2048 & run 100 17 2049 4095 &
run 120 21 1 2048 & run 120 21 2049 4095 &
run 150 26 1 1024 & run 150 26 1025 2048 & run 150 26 2049 3072 & run 150 26 3073 4095 &
wait
