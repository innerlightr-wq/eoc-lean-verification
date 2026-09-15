import sys, glob, re, math
from collections import defaultdict
rows = defaultdict(list)
for f in glob.glob('deep_J*_t*_*.txt'):
    J = int(re.search(r'J(\d+)', f).group(1))
    for line in open(f):
        if not line.startswith('h='): continue
        d = dict(re.findall(r'(\w+)=([-\d.e+]+)', line))
        rows[J].append((int(d['h']), int(d['v2']), float(d['phi']), float(d['swap']), float(d['blk2']), float(d['badfr'])))
for J in sorted(rows):
    R = rows[J]; n = len(R)
    worst_phi = max(R, key=lambda r: r[2]); worst_sw = max(R, key=lambda r: r[3]); worst_b2 = max(R, key=lambda r: r[4])
    rms_sw = math.sqrt(sum(r[3]**2 for r in R) / n)
    print(f"j0={J}: n_h={n}  worst-case rates (bits/step): phi {-math.log2(worst_phi[2])/J:.4f} (h={worst_phi[0]})  "
          f"swap {-math.log2(worst_sw[3])/J:.4f} (h={worst_sw[0]}, v2={worst_sw[1]})  blk2 {-math.log2(worst_b2[4])/J:.4f} (h={worst_b2[0]})  "
          f"rms-swap rate {-math.log2(rms_sw)/J:.4f}  mean badfr {sum(r[5] for r in R)/n:.4f}")
    for a in range(0, 6):
        S = [r for r in R if r[1] == a]
        if S: print(f"    v2={a}: n={len(S)} worst swap rate {-math.log2(max(r[3] for r in S))/J:.4f}  worst blk2 rate {-math.log2(max(r[4] for r in S))/J:.4f}")
