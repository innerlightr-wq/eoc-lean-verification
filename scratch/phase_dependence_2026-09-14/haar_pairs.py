"""Exact split-depth survival law in the 2-adic (Haar) model.
For odd x, y with v2(x - y) = q (PairValuation: v2 = S_k + min(a, b)), the shared valuation prefix
D_k is UNIFORM over the 2^(q-1) positive words with S_k <= q-1 (odd residues mod 2^q <-> such
words), the split digits are {g, g+G} with g = q - S_k and P(G) = 2^-G, and the two tails are
independent iid Geom(2) continuations.  Hence, with F[k][S] = #confined prefixes (count) and
B(j, s) = P(Geom(2) walk from (j, S_j = s) stays under the wall through N):
  psi_N(q) = P(both survive N | v2 = q)
           = 2^-(q-1) sum_{k<N} sum_{S<=q-1} F[k][S] sum_{G>=1} 2^-G B(k+1, q) B(k+1, q+G)
             + sum_{D_N confined, S_N <= q-1} 2^-S_N .
C_N(q) = psi_N(q) / p_N^2.  Wall: S_j <= floor(j alpha + c) (exact).
Also compares with empirical survivor pairs (pair_v2 output) when given.
usage: python3 haar_pairs.py c N QMAX [pair_v2_output_file log2X]"""
import re
import sys
from math import floor, log2
c, N, QMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
A = log2(3)


def K(j):
    s = floor(c + j * A)
    while (1 << (s - c)) > 3 ** j:
        s -= 1
    return s


Ks = [K(j) if j > 0 else 10 ** 9 for j in range(N + 2)]
# backward survival B[j][s] for s <= K_j, j = 0..N (B[N][s] = 1)
B = [None] * (N + 1)
B[N] = {s: 1.0 for s in range(N, Ks[N] + 1)}
for j in range(N - 1, -1, -1):
    nxt = B[j + 1]
    top = Ks[j + 1]
    cur = {}
    # T(s) = sum_{s' > s, s' <= top} 2^-(s'-s) B[j+1][s']  computed downward
    t = 0.0
    lo = j  # S_j >= j
    hi = min(Ks[j], top - 1) if j > 0 else 0
    vals = {}
    for s in range(top - 1, lo - 1, -1):
        t = 0.5 * (nxt.get(s + 1, 0.0) + t)
        vals[s] = t
    for s in range(lo, hi + 1):
        cur[s] = vals.get(s, 0.0)
    B[j] = cur
pN = B[0][0]


def Bget(j, s):
    return B[j].get(s, 0.0) if j <= N else 0.0


# forward counts F[k][S] of confined prefixes with S <= QMAX
F = [{0: 1}]
for k in range(1, N + 1):
    prev, cur = F[-1], {}
    for S, v in prev.items():
        for d in range(1, QMAX + 1):
            S2 = S + d
            if S2 > min(Ks[k], QMAX):
                break
            cur[S2] = cur.get(S2, 0) + v
    F.append(cur)
psi = {}
for q in range(1, QMAX + 1):
    tot = 0.0
    for k in range(0, N):
        for S, v in F[k].items():
            if S > q - 1:
                continue
            j = k + 1
            b1 = Bget(j, q)
            if b1 == 0.0:
                continue
            inner = sum(2.0 ** -G * Bget(j, q + G) for G in range(1, max(1, Ks[j] - q) + 1))
            tot += v * b1 * inner
    tot *= 2.0 ** -(q - 1)
    tot += sum(v * 2.0 ** -S for S, v in F[N].items() if S <= q - 1)
    psi[q] = tot
print(f"c={c} N={N}  p_N = {pN:.6e}")
emp = None
if len(sys.argv) > 4:
    L = int(sys.argv[5])
    for line in open(sys.argv[4]):
        m = re.match(r"N=(\d+) n=(\d+) (.*)", line)
        if m and int(m.group(1)) == N:
            n = int(m.group(2))
            emp = (n, {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", m.group(3))})
if emp:
    n, pr = emp
    phat = n / 2 ** (L - 1)
    print(f"  empirical p_N = {phat:.6e}  (ratio {phat / pN:.4f}), X = 2^{L}")
print("   q   C_haar(q)    " + ("C_emp(q)[/p_N^2]  emp/haar  C_emp[/phat^2]  shape ratio" if emp else ""))
for q in range(1, QMAX + 1):
    line = f"  {q:3d}  {psi[q] / pN ** 2:11.4e}"
    if emp and q < L:
        base = 2.0 ** (2 * L - q - 3)
        pe = pr.get(q, 0) / base
        r = pe / psi[q] if psi[q] else float('nan')
        line += (f"  {pe / pN ** 2:11.4e}  {r:8.4f}  {pe / phat ** 2:11.4e}  {r * (pN / phat) ** 2:8.4f}"
                 f"  (pairs {pr.get(q, 0)})")
    print(line)
