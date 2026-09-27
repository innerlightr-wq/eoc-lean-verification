"""Audit of the transport bridge on genuine seeds (Parts I-III, XX-XXXVI, XLII).

For a seed m with word d_1..d_L (L = L_1(m)) we compute, along the prefix:
  S_j, R_j = S_j - j log2 3, C_j (C_{j+1} = 3C_j + 2^{S_j}), the least realizer
  r(D_j) = (-C_j 3^{-j}) mod 2^{S_j}, the coarse depth F_j = S_j - log2 chi_j (chi_j = r(D_j)),
  the matching precision M_j = S_L - S_j (the depth still realizable by this same seed),
  H_j = F_j + M_j, and the transport deficit delta_{j+1} = d_{j+1} - (F_{j+1} - F_j).
Checks: (a) anchor lock r(D_j) = m once 2^{S_j} > m; (b) F_j = R_j + j*alpha - log2 m after lock;
(c) H_j constant after lock; (d) whether any post-lock deficit (failure) occurs.
usage: python3 lock.py"""
import math

AL = math.log2(3)
NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]

def word(m):
    x = m; S = 0; ds = []
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j]: break
        S += a; ds.append(a); x = v >> a
    return ds

RECORDS = [27, 703, 35655, 270271, 1859241, 10507503]
print("seed        L_1   j0(lock)  S_{j0}  log2 m   post-lock r(D_j)=m always?  max|F_j-(R_j+ja-log2 m)|  H const?")
for m in RECORDS:
    ds = word(m); L = len(ds)
    S = 0; C = 0; Ss = []; rs = []
    for j in range(L):
        C = 3 * C + (1 << S)          # C_{j+1} = 3 C_j + 2^{S_j}
        S += ds[j]
        Ss.append(S)
        mod = 1 << S
        r = (-C * pow(3, -(j + 1), mod)) % mod
        rs.append(r)
    j0 = next((j for j in range(L) if (1 << Ss[j]) > m), None)
    lock_ok = all(rs[j] == m for j in range(j0, L)) if j0 is not None else None
    SL = Ss[-1]
    dev = 0.0; hs = []
    for j in range(j0, L):
        R = Ss[j] - (j + 1) * AL
        F = Ss[j] - math.log2(rs[j])
        dev = max(dev, abs(F - (R + (j + 1) * AL - math.log2(m))))
        hs.append(F + (SL - Ss[j]))
    print(f"{m:10d}  {L:4d}   {j0+1:6d}  {Ss[j0]:6d}  {math.log2(m):7.2f}   {str(lock_ok):>6}"
          f"                    {dev:.2e}            {'yes' if max(hs)-min(hs) < 1e-9 else 'NO'}"
          f"  (H = {hs[0]:.3f} = S_L - log2 m = {SL - math.log2(m):.3f})")
print()
print("interpretation: after the lock the coarse anchor is the seed itself, so F_j = S_j - log2 m grows by")
print("d_{j+1} each step: the transport deficit is identically 0 and no 'failure' can occur (tautology).")
print("M_j = S_L - S_j is exactly the remaining realizable depth, so H = F + M = S_L - log2 m is the seed's")
print("total confined depth: the transport coordinates carry no information beyond L_1(m) itself.")
