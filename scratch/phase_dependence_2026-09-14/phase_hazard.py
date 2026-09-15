"""Central phase test (Parts II-V at the seed level).  For odd seeds below X = 2^HI and wall c:
  rho_N = S_X(N) / ((X/2) p_N(c)),   S_X(N) = #{odd mu < X : exit > N}  (exact, sieve histogram).
p_N(c) contains the renewal phase: Lambda_N := log2 p_N + I0 N + 1.5 log2 N -> log2 L_c(phi_N).
If actual integers track the ensemble (H0), log2 rho_N has no component along the phase factor.
If integer placement were 'phase-blind' (following only the smooth part of p_N), the residual of
log2 rho_N would be -(Lambda_N - smooth Lambda): regression slope -1.
Also the one-step exit hazard h_N = 1 - S(N)/S(N-1) vs 1 - p_N/p_{N-1} (the Sturmian clock).
usage: python3 phase_hazard.py c HI logfile NMIN NMAX"""
import json
import re
import sys
from math import log2, floor
c, HI, logf, NMIN, NMAX = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
T = json.load(open("pn_table.json"))[str(c)]
A = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = A * (1 - H2(1 / A))
lp = {r["N"]: r["lP"] for r in T}
hist = {}
for line in open(logf):
    m = re.match(r"HIST k=(\d+):(.*)", line)
    if m and int(m.group(1)) < HI:
        for e, v in re.findall(r"(\d+):(\d+)", m.group(2)):
            hist[int(e)] = hist.get(int(e), 0) + int(v)
emax = max(hist)
S = {}
acc = 0
for e in range(emax + 1, 0, -1):
    acc += hist.get(e, 0)
    S[e - 1] = acc   # #exit > e-1
X2 = 2.0 ** (HI - 1)
rows = []
for N in range(NMIN, NMAX + 1):
    if S.get(N, 0) < 30:
        break
    rho = S[N] / (X2 * 2 ** lp[N])
    Lam = lp[N] + I0 * N + 1.5 * log2(N)
    phi = (N * A) % 1
    hobs = 1 - S[N] / S[N - 1]
    hpred = 1 - 2 ** (lp[N] - lp[N - 1])
    rows.append((N, phi, S[N], rho, Lam, hobs, hpred))


def smooth(vals, i, w=12):
    lo, hi = max(0, i - w), min(len(vals), i + w + 1)
    return sum(vals[lo:hi]) / (hi - lo)


lr = [log2(r[3]) for r in rows]
La = [r[4] for r in rows]
res = [lr[i] - smooth(lr, i) for i in range(len(rows))]
lam = [La[i] - smooth(La, i) for i in range(len(rows))]
wts = [r[2] / (1 + 0.0) for r in rows]
num = sum(a * b for a, b in zip(res, lam))
den = sum(b * b for b in lam)
slope = num / den
print(f"c={c} X=2^{HI}  N in [{rows[0][0]},{rows[-1][0]}] ({len(rows)} depths)")
print(f"  regression of detrended log2 rho_N on detrended phase factor Lambda_N: slope = {slope:+.4f}"
      f"   (H0: 0;  phase-blind placement: -1)")
# standard error of the slope from residual scatter (independent-errors approximation, optimistic)
resid = [a - slope * b for a, b in zip(res, lam)]
se = (sum(r * r for r in resid) / max(1, len(resid) - 1) / den) ** 0.5
# block-correlation-robust version: slope from 5 disjoint depth blocks
blk = []
nb = 5
L = len(rows) // nb
for bi in range(nb):
    sl = slice(bi * L, (bi + 1) * L)
    d2 = sum(b * b for b in lam[sl])
    if d2 > 0:
        blk.append(sum(a * b for a, b in zip(res[sl], lam[sl])) / d2)
mb = sum(blk) / len(blk)
sb = (sum((x - mb) ** 2 for x in blk) / (len(blk) - 1) / len(blk)) ** 0.5
print(f"  slope s.e. (naive) {se:.4f};  block slopes {[round(x,3) for x in blk]}  mean {mb:+.4f} +- {sb:.4f}")
print(f"  rms detrended phase factor {((den/len(rows))**0.5):.4f} bits; rms detrended log2 rho {((sum(r*r for r in res)/len(res))**0.5):.5f} bits")
# phase-window means of rho (all depths), and of observed/predicted hazard
print("  phase window   #N   mean rho_N    mean h_obs/h_pred")
for w in range(10):
    sel = [r for r in rows if w / 10 <= r[1] < (w + 1) / 10]
    if sel:
        mr = sum(r[3] for r in sel) / len(sel)
        mh = sum(r[5] / r[6] for r in sel) / len(sel)
        print(f"   [{w/10:.1f},{(w+1)/10:.1f})   {len(sel):4d}   {mr:.5f}      {mh:.5f}")
# depth bands
print("  depth band     mean rho_N   (min,max)")
for a in range(NMIN, rows[-1][0] + 1, 40):
    sel = [r[3] for r in rows if a <= r[0] < a + 40]
    if sel:
        print(f"   [{a},{a+40})    {sum(sel)/len(sel):.5f}   ({min(sel):.4f},{max(sel):.4f})")
