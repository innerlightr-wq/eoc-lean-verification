"""Validation: (1) class DP vs brute force over all words for small j; (2) 2-adic vs 3-adic dark flags;
(3) telescoping sum of w_r equals the exact log-moment."""
import itertools, math, sys
from pexact import Instance, barrier, log2ratio

def brute(inst, s):
    j, top, R = inst.j, inst.top, inst.R
    dark = [inst.dark_row(r) for r in range(R)]
    tot = 0; cnt = 0
    def rec(i, S, word):
        nonlocal tot, cnt
        if i == j:
            if S != inst.sg: return
            N = 0
            P = [0]
            for d in word: P.append(P[-1] + d)
            for r in range(R):
                x, z, y, cap = P[2*r], P[2*r+1], P[2*r+2], top[2*r+1]
                if inst.obs == 'odd':
                    elig = (z + 1 < y) and (z + 1 <= cap)
                    if elig and dark[r][z]: N += 1
                else:
                    if dark[r][z]: N += 1
            tot += s ** N; cnt += 1
            return
        for d in range(1, top[i+1] - S + 1):
            word.append(d); rec(i+1, S+d, word); word.pop()
    rec(0, 0, [])
    return tot, cnt

ok = True
for j in (4, 6, 8, 10, 12):
    for t in (0, 3):
        for lam in (1, 5):
            for D in (4, 6, 108):
                for obs in ('odd', 'black'):
                    I = Instance(j, t, lam=lam, D=D, mode='2adic', obs=obs)
                    tb, cb = brute(I, 3)
                    if I.moment(3) != tb or I.moment(1) != cb:
                        ok = False; print("MISMATCH", j, t, lam, D, obs, I.moment(3), tb, I.moment(1), cb)
print("(1) class DP == brute force on all small cases:", ok)

mism = 0; total = 0
for j in (100, 400):
    for lam in (1, 5, 7, 17):
        a = Instance(j, j // 6, lam=lam, D=108, mode='2adic')
        b = Instance(j, j // 6, lam=lam, D=108, mode='3adic')
        for r in range(a.R):
            ra, rb = a.dark_row(r), b.dark_row(r)
            for z in range(2 * r + 1, len(ra)):
                total += 1; mism += ra[z] != rb[z]
print(f"(2) 2-adic vs 3-adic dark flags: {mism} mismatches in {total} cells")

I = Instance(200, 33, lam=1, D=108)
Z3, Z1 = I.moment(3), I.moment(1)
w, lp = I.blocks(3)
print(f"(3) exact log2(Z3/Z1) = {log2ratio(Z3, Z1):.10f}; sum w_r = {sum(w):.10f}; min w_r = {min(w):.3e}")
