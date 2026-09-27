"""m-scan: the pressure of N_odd for the actual environment family xi = lambda 2^{-m} (Parts XIX-XXVII).

For fixed J the confined path ensemble depends only on J (barrier top[i], sg, R): changing m only translates the
path's column window over the fixed Tao array, since the cell of block r is (m - S_{2r+1}, 2r+2) and
y(m - S, b) = centered(lambda 2^{S-m} mod 3^b).  So the family {lambda 2^{-m}} is ONE orbit of multiplication by
2^{-1} in Z_3^x, and lambda only shifts the starting point (2 is a primitive root mod 3^b).

For each m in a window we compute (exactly, up to float DP):
  Psi(m) = (1/J) log2 E_conf[s^{N_odd}]    (s = 3 by default)
  mu(m)  = E_conf[N_odd] / R
and report the distribution, the empirical density of exceptional m at thresholds, the autocorrelation of the
exceptional indicator, and the longest run of exceptional m.
usage: python3 mscan.py J M [s] [lambda]"""
import math, sys
from collections import Counter

AL = math.log2(3)
J = int(sys.argv[1]); M = int(sys.argv[2])
SV = float(sys.argv[3]) if len(sys.argv) > 3 else 3.0
LAM = int(sys.argv[4]) if len(sys.argv) > 4 else 1
R = J // 2; sg = math.floor(J * AL); t = J // 6; m0 = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]

# ---- path marginals (independent of m): pi[i][S] for odd times, and the forward/backward counts
F = [None] * (J + 1); F[0] = {0: 1}
for i in range(J):
    acc = 0; nx = {}
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += F[i].get(S2 - 1, 0)
        if acc: nx[S2] = acc
    F[i + 1] = nx
G = [None] * (J + 1); G[J] = {sg: 1}
for i in range(J - 1, -1, -1):
    acc = 0; cur = {}
    for S in range(top[i + 1] - 1, i - 1, -1):
        acc += G[i + 1].get(S + 1, 0)
        if acc and S <= top[i]: cur[S] = acc
    G[i] = cur
Z = F[J][sg]; shift = max(Z.bit_length() - 60, 0)
pi_odd = []
for r in range(R):
    i = 2 * r + 1
    pi_odd.append({S: (F[i][S] * G[i][S] >> shift) / (Z >> shift) for S in F[i] if S in G[i]})

# ---- black tables: for each row b = 2r+2, a-range covers a = m - x, m in [m0, m0+M), x in [2r+1, top[2r+1]]
MLO, MHI = m0, m0 + M - 1
blk = []
for r in range(R):
    b = 2 * r + 2; qb = 3 ** b; half = qb // 2
    a_lo = MLO - top[2 * r + 1]; a_hi = MHI - (2 * r + 1)
    inv2 = (qb + 1) // 2                      # 2^{-1} mod 3^b
    v = LAM * pow(2, -a_lo, qb) % qb          # lambda 2^{-a_lo}
    row = bytearray(a_hi - a_lo + 1)
    for k in range(a_hi - a_lo + 1):
        y = v if v <= half else v - qb
        row[k] = 1 if 54 * abs(y) < qb else 0
        v = v * inv2 % qb                      # a -> a + 1
    blk.append((a_lo, row))

def stats(m):
    """(Psi, mu) for environment lambda 2^{-m}."""
    # tilted DP over words: weight s at odd steps with black own cell
    v = [0.0] * (sg + 2); v[0] = 1.0; lg = 0.0; mu = 0.0
    for i in range(J):
        acc = 0.0; nv = [0.0] * (sg + 2); lo = i + 1; hi = top[i + 1]
        odd = (i + 1) % 2 == 1
        if odd:
            r = i // 2; a_lo, row = blk[r]; pr = pi_odd[r]
        for S2 in range(lo, hi + 1):
            acc += v[S2 - 1]
            if acc:
                if odd and row[m - S2 - a_lo]:
                    nv[S2] = acc * SV
                else:
                    nv[S2] = acc
        if odd:
            mu += sum(w for S, w in pr.items() if row[m - S - a_lo])
        mx = max(nv)
        if mx == 0: return float('nan'), float('nan')
        lg += math.log2(mx)
        v = [x / mx for x in nv]
    return (lg + math.log2(v[sg]) - math.log2(Z)) / J, mu / R

vals = []
for m in range(MLO, MHI + 1):
    vals.append(stats(m))
ps = [x for x, _ in vals]; mus = [y for _, y in vals]
ps_sorted = sorted(ps)
qt = lambda f: ps_sorted[min(int(f * len(ps_sorted)), len(ps_sorted) - 1)]
mean = sum(ps) / len(ps); sd = math.sqrt(sum((x - mean) ** 2 for x in ps) / len(ps))
print(f"J={J} lambda={LAM} s={SV}: m in [{MLO}, {MHI}] ({M} values); Psi = (1/J) log2 E[s^N_odd]")
print(f"  Psi: mean {mean:.5f} sd {sd:.5f} | min {ps_sorted[0]:.5f} 5% {qt(0.05):.5f} 50% {qt(0.5):.5f} "
      f"95% {qt(0.95):.5f} 99% {qt(0.99):.5f} max {ps_sorted[-1]:.5f}")
print(f"  mu = E[N_odd]/R: mean {sum(mus) / len(mus):.5f} max {max(mus):.5f} min {min(mus):.5f}")
for th in (0.06, 0.07, 0.08, 0.085, 0.09, 0.10):
    bad = [i for i, x in enumerate(ps) if x >= th]
    if not bad:
        print(f"  threshold Psi >= {th}: 0 exceptional m of {M}")
        continue
    runs = []; cur = 1
    for a_, b_ in zip(bad, bad[1:]):
        if b_ == a_ + 1: cur += 1
        else: runs.append(cur); cur = 1
    runs.append(cur)
    dens = len(bad) / M
    cor = []
    S = set(bad)
    for h in (1, 2, 3, 5, 10):
        c = sum(1 for i in bad if i + h in S) / M
        cor.append(f"h={h}: {c:.2e} (indep {dens * dens:.2e})")
    print(f"  threshold Psi >= {th}: {len(bad)} exceptional m ({dens:.4f}); longest run {max(runs)}; "
          f"autocorr " + " ".join(cor))
