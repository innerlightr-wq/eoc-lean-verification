"""Exponent audit: discriminate N^-p prefactors for the c-confined word count |W_c(N)|, the endpoint
shell count W_c(N, s*), and the Geom(2) survival mass P_N, using PHASE-MATCHED N (the constants
oscillate with {N alpha}).  Exact integer DP; logs only for reporting.

  s* = floor(N alpha) + c  (largest feasible endpoint)
  rho_tot   = N |W_c(N)| / C(s*, N)             proved >= 1 (rotation + terminalCount_eq_choose)
  rho_shell = N W_c(N,s*) / C(s*-1, N-1)        (the Sept-12 audit's object)
  Q_p       = |W_c(N)| N^p 2^{-(alpha - I0) N}  for p in {0.5, 1, 1.5, 2}
  Qm_p      = P_N N^p 2^{I0 N}
usage: python3 exponent_audit.py c NMAX
"""
import sys
from math import log2, floor, comb
c = int(sys.argv[1]); NMAX = int(sys.argv[2])
ALPHA = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = ALPHA * (1 - H2(1 / ALPHA))
RATE = ALPHA - I0


def lg(x):
    b = x.bit_length()
    return b - 60 + log2(x >> (b - 60)) if b > 60 else log2(x)


def smax_of(r):
    s = floor(c + r * ALPHA)
    while s - c >= 0 and (1 << (s - c)) > 3 ** r:
        s -= 1
    return s


targets = [125, 250, 500, 1000, 2000, 4000, 6000, 8000]
windows = [(0.20, 0.26), (0.45, 0.51), (0.70, 0.76)]
want = {}
for T in targets:
    if T > NMAX:
        continue
    for w in windows:
        N = T
        while not (w[0] <= (N * ALPHA) % 1 < w[1]):
            N += 1
        if N <= NMAX:
            want[N] = (T, w)
layer = {0: 1}
rows = []
for r in range(1, NMAX + 1):
    sm = smax_of(r)
    keys = sorted(layer)
    new, acc, idx = {}, 0, 0
    for Sp in range(r, sm + 1):
        while idx < len(keys) and keys[idx] < Sp:
            acc += layer[keys[idx]]
            idx += 1
        if acc:
            new[Sp] = acc
    layer = new
    if r in want:
        N = r
        W = sum(layer.values())
        top = layer.get(sm, 0)
        mS = max(layer)
        mass_num = sum(v << (mS - S) for S, v in layer.items())
        lW, lP = lg(W), lg(mass_num) - mS
        lC = lg(comb(sm, N))
        lshell = lg(comb(sm - 1, N - 1))
        rows.append(dict(N=N, T=want[N][0], w=want[N][1], rho_tot=2 ** (log2(N) + lW - lC),
                         rho_shell=2 ** (log2(N) + lg(top) - lshell) if top else 0.0,
                         Q={p: 2 ** (lW + p * log2(N) - RATE * N) for p in (0.5, 1, 1.5, 2)},
                         Qm={p: 2 ** (lP + p * log2(N) + I0 * N) for p in (0.5, 1, 1.5, 2)},
                         lW=lW, lP=lP))
print(f"c={c}  (rate alpha-I0 = {RATE:.6f}, I0 = {I0:.6f})")
for w in windows:
    sub = sorted([x for x in rows if x["w"] == w], key=lambda x: x["N"])
    print(f"  phase window {w}:")
    print("     N     rho_tot  rho_shell |  Q_0.5      Q_1      Q_1.5     Q_2   |  Qm_1.5   | local slope of log2|W| - rate N (per log2 N)")
    prev = None
    for x in sub:
        sl = ""
        if prev:
            sl = f"{((x['lW'] - RATE * x['N']) - (prev['lW'] - RATE * prev['N'])) / (log2(x['N']) - log2(prev['N'])):+.4f}"
            slm = ((x['lP'] + I0 * x['N']) - (prev['lP'] + I0 * prev['N'])) / (log2(x['N']) - log2(prev['N']))
            sl += f"  (mass {slm:+.4f})"
        print(f"   {x['N']:5d}  {x['rho_tot']:8.4f}  {x['rho_shell']:8.4f} | {x['Q'][0.5]:.3e} {x['Q'][1]:.4f} {x['Q'][1.5]:9.4f} {x['Q'][2]:9.2f} | {x['Qm'][1.5]:8.4f}  | {sl}")
        prev = x
