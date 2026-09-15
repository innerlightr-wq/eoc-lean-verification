"""Part XIV: does the renewal phase change the normalized dependence structure C_N(q) = psi_N(q)/p_N^2?
Exact Haar split-depth law (haar_pairs.py) for N in a range; regress detrended log C_N(q) on the
detrended phase factor of p_N.  Also the empirical C from survivor pairs (pair_v2) at X = 2^36."""
import subprocess, re, json, sys
from math import log2
A = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = A * (1 - H2(1 / A))
T = json.load(open("pn_table.json"))["0"]
lp = {r["N"]: r["lP"] for r in T}
Ns = list(range(96, 145))
qs = [4, 8, 12, 16, 20, 24, 28]
C = {}
for N in Ns:
    out = subprocess.run(["python3", "haar_pairs.py", "0", str(N), "30"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        m = re.match(r"\s+(\d+)\s+([\d.e+-]+)$", line)
        if m and int(m.group(1)) in qs:
            C[(N, int(m.group(1)))] = float(m.group(2))
def detr(v, i, w=8):
    lo, hi = max(0, i - w), min(len(v), i + w + 1)
    return v[i] - sum(v[lo:hi]) / (hi - lo)
Lam = [lp[N] + I0 * N + 1.5 * log2(N) for N in Ns]
dl = [detr(Lam, i) for i in range(len(Ns))]
print("Haar model: slope of detrended log2 C_N(q) on detrended log2 phase factor of p_N (N = 96..144)")
for q in qs:
    lc = [log2(C[(N, q)]) for N in Ns]
    dc = [detr(lc, i) for i in range(len(Ns))]
    sl = sum(a * b for a, b in zip(dc, dl)) / sum(b * b for b in dl)
    rms = (sum(a * a for a in dc) / len(dc)) ** 0.5
    print(f"  q={q:2d}: C ~ {C[(120, q)]:8.3f}   slope {sl:+.4f}   rms detrended log2 C {rms:.5f} bits"
          f"  (phase factor rms {(sum(b*b for b in dl)/len(dl))**0.5:.4f})")
