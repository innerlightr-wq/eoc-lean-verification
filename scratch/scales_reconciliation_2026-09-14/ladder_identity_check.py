"""Exhaustive finite checks of the combinatorial identities behind PDF Lemma 8.10 / 8.12
for the (+1, -beta) walk, beta = log2(3) - 1.  Paths of length n are enumerated; every identity
is homogeneous in the path weight (fixed n and endpoint fix the number K of +1 steps), so it is
checked at the level of path COUNTS (exact integers).
  (I3) Alili-Doney as restated by Caravenna (2005, eq. 2.8):
       n * #{T_k = n, D_n = x} = k * #{H_{k-1} < x <= H_k, D_n = x}          (k >= 1, x > 0)
  (S2) Lemma 8.10 Step 2:  n * #{D_1..D_n > 0, D_n = x} = sum_paths(D_n = x) #{j >= 0 : H_j < x}
  (D)  Lemma 8.12 exact min decomposition (b = c + beta, c = 0, 1):
       #{D_t <= b for t <= n, D_n = y} = sum_{sigma, m} (pre-min count) * (post-min count)
usage: python3 ladder_identity_check.py NMAX"""
import sys
from itertools import product
from math import log2
BETA = log2(3) - 1
NMAX = int(sys.argv[1])


def val(K, t):  # D after t steps with K up-steps
    return K - BETA * (t - K)


def key(K, t):  # exact identity of the value: (K, t-K) pair
    return (K, t - K)


bad = {"I3": 0, "S2": 0, "D": 0}
checked = {"I3": 0, "S2": 0, "D": 0}
for n in range(1, NMAX + 1):
    I3l, I3r, S2l, S2r = {}, {}, {}, {}
    # for (D): counts of paths by endpoint staying <= b, and excursion counts for the decomposition
    stay = {0: {}, 1: {}}
    pos_exc = {}  # (length, endkey) -> count of D_1..D_len > 0
    neg_exc = {}  # (length, endkey) -> count of D_1..D_len < 0
    for steps in product((1, 0), repeat=n):
        K = 0
        vals = [0.0]
        keys = [(0, 0)]
        for t, s in enumerate(steps, 1):
            K += s
            vals.append(val(K, t))
            keys.append(key(K, t))
        x, xk = vals[-1], keys[-1]
        # strict ascending ladder epochs / heights up to n
        ladder = [(0, 0.0)]
        for t in range(1, n + 1):
            if vals[t] > ladder[-1][1]:
                ladder.append((t, vals[t]))
        if x > 0:
            for k in range(1, len(ladder)):
                if ladder[k][0] == n:
                    I3l[(k, xk)] = I3l.get((k, xk), 0) + n
                if ladder[k - 1][1] < x <= ladder[k][1]:
                    I3r[(k, xk)] = I3r.get((k, xk), 0) + k
            if all(v > 0 for v in vals[1:]):
                S2l[xk] = S2l.get(xk, 0) + n
            S2r[xk] = S2r.get(xk, 0) + sum(1 for _, h in ladder if h < x)
        for c in (0, 1):
            if all(v <= c + BETA for v in vals[1:]):
                stay[c][xk] = stay[c].get(xk, 0) + 1
    for d in (I3l, I3r):
        for kk in set(I3l) | set(I3r):
            pass
    for kk in set(I3l) | set(I3r):
        checked["I3"] += 1
        bad["I3"] += I3l.get(kk, 0) != I3r.get(kk, 0)
    for kk in set(S2l) | set(S2r):
        checked["S2"] += 1
        bad["S2"] += S2l.get(kk, 0) != S2r.get(kk, 0)
    # (D) decomposition: enumerate excursions of all lengths <= n
    if n <= 12:
        exc_pos, exc_neg = {}, {}
        for L in range(0, n + 1):
            for steps in product((1, 0), repeat=L):
                K = 0
                ok_p = ok_n = True
                for t, s in enumerate(steps, 1):
                    K += s
                    v = val(K, t)
                    ok_p &= v > 0
                    ok_n &= v < 0
                kk = (L, K)
                if ok_p:
                    exc_pos[kk] = exc_pos.get(kk, 0) + 1
                if ok_n:
                    exc_neg[kk] = exc_neg.get(kk, 0) + 1
        for c in (0, 1):
            b = c + BETA
            for K in range(n + 1):
                y = val(K, n)
                if y >= b:
                    continue
                rhs = 0
                for sig in range(n + 1):
                    for Ks in range(sig + 1):  # min value D_sigma = h (pre: positive excursion to h)
                        h = val(Ks, sig)
                        if not (0 <= h < b):
                            continue
                        pre = exc_pos.get((sig, Ks), 0) if sig > 0 else (1 if Ks == 0 else 0)
                        # post: negative excursion of length n - sig from h down to y, i.e. ending at y - h
                        Kp = K - Ks
                        if Kp < 0 or Kp > n - sig:
                            continue
                        post = exc_neg.get((n - sig, Kp), 0) if n - sig > 0 else (1 if Kp == 0 else 0)
                        rhs += pre * post
                # convention check: the max of D (= min of Y) is attained at sigma with value h
                lhs = stay[c].get((K, n - K), 0)
                checked["D"] += 1
                bad["D"] += lhs != rhs
print(f"n <= {NMAX}: identity checks (count of (n,k,x) cases checked / failures)")
for k in bad:
    print(f"  {k}: {checked[k]} checked, {bad[k]} failures")
