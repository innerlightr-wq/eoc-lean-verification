"""Part XLVI: balanced-ternary digits of the 3-adic numbers 2^{-a} (the environment columns).
black(a,b) <=> digits b-3, b-2, b-1 of 2^{-a} vanish, so the black cells of column a are the aligned
3-zero windows of this digit sequence.  Reports digit frequencies, zero-run distribution, aligned
3-zero window density (Haar: 1/27 = 0.037), and digit autocorrelation.
usage: python3 digits.py D a1 a2 ..."""
import math, sys
from collections import Counter
D = int(sys.argv[1]); AS = [int(x) for x in sys.argv[2:]] or [1, 2, 700, 1401, 2102]
q = 3 ** D
print(f"depth D={D}")
for a in AS:
    v = pow(2, -a, q) if a > 0 else pow(2, -a, q)
    dg = []
    x = v
    for _ in range(D):
        r = x % 3
        if r == 2: r = -1; x += 1          # balanced digit
        dg.append(r); x = (x - r) // 3
    cnt = Counter(dg)
    runs = Counter(); i = 0
    while i < D:
        if dg[i] == 0:
            j = i
            while j < D and dg[j] == 0: j += 1
            runs[j - i] += 1; i = j
        else: i += 1
    win = sum(1 for j in range(D - 2) if dg[j] == 0 and dg[j+1] == 0 and dg[j+2] == 0)
    mu = sum(dg) / D; var = sum(x * x for x in dg) / D - mu * mu
    ac = []
    for h in (1, 2, 3, 10):
        c = sum(dg[j] * dg[j + h] for j in range(D - h)) / (D - h)
        ac.append(f"h={h}: {((c - mu * mu) / var if var > 0 else float('nan')):+.4f}")
    print(f"  a={a}: digit freqs -1/0/+1 = {cnt[-1]/D:.4f}/{cnt[0]/D:.4f}/{cnt[1]/D:.4f}; "
          f"aligned 3-zero windows {win/(D-2):.5f} (Haar 0.03704); max zero run {max(runs) if runs else 0}; "
          f"runs>=3: {sum(c for r, c in runs.items() if r >= 3)}; autocorr " + " ".join(ac))
