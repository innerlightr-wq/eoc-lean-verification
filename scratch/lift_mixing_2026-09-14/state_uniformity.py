"""Orbit-state (restart-state) uniformity for survivors: at selected steps j, survivors mu < X with
state m = T^j(mu); the next lift digit / next digit is a function of m mod 2^(d+1).  Test whether
m mod 2^k is uniform over odd residues, overall and conditioned on headroom h = K_j - S_j (drift)
and prefix residue b = mu mod 16.  Reports chi2/dof, TV, max relative bias, mutual information,
and Poisson-normalized cell deviations at expected-count thresholds.
usage: python3 state_uniformity.py file.bin HI"""
import array, sys
from math import log2, sqrt, floor
fn, HI = sys.argv[1], int(sys.argv[2])
JM, SM, DM, NJ = 260, 480, 24, 8
J = [20, 30, 40, 60, 80, 100, 130, 160]
arr = array.array("Q"); arr.frombytes(open(fn, "rb").read())
off = (JM + 1) * SM + (JM + 1) * SM * DM
def st(jj, h, b, a): return arr[off + ((jj * 16 + h) * 8 + b) * 512 + a]
A = log2(3)
print(f"{fn}: state uniformity of T^j(mu) mod 2^k over odd residues (survivors through j)")
print("   j   A=j/log2X  survivors   k : chi2/dof   TV       maxrelbias  MI(m;h,b) bits | cell z rms (E>=10/30/100/1000)")
for jj, j in enumerate(J):
    tot = sum(st(jj, h, b, a) for h in range(16) for b in range(8) for a in range(512))
    if tot < 100: continue
    for k in (3, 6, 10):
        ncls = 2 ** (k - 1)
        # marginal over odd residues mod 2^k (a is (m mod 1024) >> 1 -> m mod 2^k odd class = a mod 2^(k-1))
        cnt = [0] * ncls
        joint = {}
        for h in range(16):
            for b in range(8):
                for a in range(512):
                    v = st(jj, h, b, a)
                    if v:
                        cnt[a % ncls] += v
                        joint[(h, b, a % ncls)] = joint.get((h, b, a % ncls), 0) + v
        e = tot / ncls
        chi = sum((x - e) ** 2 / e for x in cnt) / (ncls - 1)
        tv = 0.5 * sum(abs(x / tot - 1 / ncls) for x in cnt)
        mrb = max(abs(x / e - 1) for x in cnt)
        # mutual information between residue class and (h,b)
        hb = {}
        for (h, b, a), v in joint.items(): hb[(h, b)] = hb.get((h, b), 0) + v
        mi = 0.0
        for (h, b, a), v in joint.items():
            mi += v / tot * log2((v / tot) / ((hb[(h, b)] / tot) * (cnt[a] / tot)))
        # Poisson-normalized local cells: each (h,b) cell's residue counts vs uniform within the cell
        zz = {10: [], 30: [], 100: [], 1000: []}
        for (h, b), nhb in hb.items():
            ex = nhb / ncls
            for thr in zz:
                if ex >= thr:
                    for a in range(ncls):
                        v = joint.get((h, b, a), 0)
                        zz[thr].append((v - ex) / sqrt(ex))
        zr = " ".join(f"{sqrt(sum(z*z for z in zz[t])/len(zz[t])):.2f}" if zz[t] else "  -  " for t in (10, 30, 100, 1000))
        print(f"  {j:3d}   {j/HI:5.2f}   {tot:10d}  {k:2d} : {chi:7.3f}  {tv:.2e}  {mrb:.2e}   {mi:.2e}      | {zr}")
