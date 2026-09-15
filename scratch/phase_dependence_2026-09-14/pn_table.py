"""Exact ensemble reference table: for c in {0,1,2,3} and N <= NMAX, with the wall R_j <= c
(S_j <= floor(j alpha + c), exact integer test 2^(S-c) <= 3^j):
  log2 W_c(N), log2 p_N(c) (Geom(2) mass), s_N, phi_N = {alpha N}, and the shell profile
  (count and mass fractions for shell gaps x = s_N - S_N, x = 0..11).
Writes pn_table.json.  usage: python3 pn_table.py NMAX"""
import json
import sys
from math import floor, log2
NMAX = int(sys.argv[1])
A = log2(3)


def lg(x):
    b = x.bit_length()
    return b - 60 + log2(x >> (b - 60)) if b > 60 else log2(x)


out = {}
for c in range(4):
    def smax_of(r):
        s = floor(c + r * A)
        while (1 << (s - c)) > 3 ** r:
            s -= 1
        return s
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
        W = sum(layer.values())
        mS = max(layer)
        mass = sum(v << (mS - S) for S, v in layer.items())
        lW, lP = lg(W), lg(mass) - mS
        cf = [layer.get(sm - x, 0) / W if W else 0 for x in range(12)]
        mf = [(layer.get(sm - x, 0) << x) / mass for x in range(12)]
        rows.append(dict(N=r, sN=sm, phi=(r * A) % 1, lW=lW, lP=lP, cf=cf, mf=mf))
    out[c] = rows
    print(f"c={c} done", file=sys.stderr)
json.dump(out, open("pn_table.json", "w"))
