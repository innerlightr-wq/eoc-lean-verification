"""Parts IV, V, VIII, X, XV: certificate tables, run law, deep-dip recovery, entropy, stopping times.
Exact arithmetic where decisions matter (drift comparisons via 2^S vs 3^n for integer walls)."""
import itertools
import random
from math import log2, floor, ceil

rng = random.Random(20260920)
ALPHA = log2(3)
I0 = ALPHA - ALPHA * log2(ALPHA) + (ALPHA - 1) * log2(ALPHA - 1)


def v2(n):
    return (n & -n).bit_length() - 1


def step(m):
    x = 3 * m + 1
    d = v2(x)
    return x >> d, d


# ---------------------------------------------------------------- IV: block certificates
print("[IV] block gain G(w) = sum(w) - len(w)*log2(3); Geom(2) probability that a block certifies G > H")
Hs = (0, 0.5, 1, 2, 4, 8)
print("     l | " + " ".join(f"P(G>{H})".rjust(10) for H in Hs))
for l in range(1, 7):
    probs = []
    for H in Hs:
        # P(sum of l iid Geom(2) > H + l*alpha) = P(S >= floor(H + l alpha) + 1); S ~ NegBin
        thr = floor(H + l * ALPHA) + 1
        # P(S = s) = C(s-1, l-1) 2^-s
        from math import comb
        p = 1.0 - sum(comb(s - 1, l - 1) * 2.0 ** (-s) for s in range(l, thr))
        probs.append(p)
    print(f"     {l} | " + " ".join(f"{p:10.4f}" for p in probs))
print("     smallest single-digit certificate for headroom H: d > H + log2(3), i.e. d_min(H) = floor(H+alpha)+1")
for H in Hs:
    dmin = floor(H + ALPHA) + 1
    print(f"       H={H}: d_min = {dmin}, P(one step certifies) = 2^-{dmin-1} = {2.0**(-(dmin-1)):.4f}")
blocks = []
for l in range(1, 5):
    for w in itertools.product(range(1, 9), repeat=l):
        G = sum(w) - l * ALPHA
        blocks.append((G / l, G, w, 2.0 ** (-sum(w))))
print("     most probable positive-gain blocks by length (gain > 0):")
for l in range(1, 5):
    cand = sorted([b for b in blocks if len(b[2]) == l and b[1] > 0], key=lambda b: -b[3])[:3]
    print("       l=%d: " % l + ", ".join(f"{b[2]} G={b[1]:.3f} p={b[3]:.4f}" for b in cand))

# ---------------------------------------------------------------- V: run law
print("\n[V] run 1^r q: gain G(r,q) = r + q - (r+1) log2 3; minimal q erasing headroom H:")
print("     q(r,H) = floor(H + (r+1) log2 3 - r) + 1   (no equality case: log2 3 irrational)")
print("      r | " + " ".join(f"H={H}".rjust(6) for H in Hs))
for r in range(0, 11):
    row = []
    for H in Hs:
        q = floor(H + (r + 1) * ALPHA - r) + 1
        q = max(q, 2)
        row.append(q)
    print(f"     {r:2d} | " + " ".join(f"{q:6d}" for q in row))
print("     (each extra 1 raises the needed q by log2(3) - 1 = 0.585; a run of r ones costs 0.585 r headroom)")

# ---------------------------------------------------------------- VIII: deep-dip recovery
print("\n[VIII-a] ensemble recovery: iid Geom(2) walk from R = -G to R > U (U = 2); Wald: E[T] = (U+G+E[overshoot])/(2-log2 3)")


def geom():
    q = 1
    while rng.random() < 0.5:
        q += 1
    return q


for G in (0, 5, 10, 20, 40):
    Ts, overs = [], []
    for _ in range(20000):
        R, n = -G, 0
        while R <= 2:
            R += geom() - ALPHA
            n += 1
        Ts.append(n)
        overs.append(R - 2)
    Ts.sort()
    mean = sum(Ts) / len(Ts)
    wald = (2 + G + sum(overs) / len(overs)) / (2 - ALPHA)
    print(f"     G={G:2d}: mean T {mean:7.2f} (Wald {wald:7.2f}), median {Ts[len(Ts)//2]}, 99% {Ts[int(.99*len(Ts))]}, "
          f"max {Ts[-1]}; (U+G)/0.415 = {(2+G)/(2-ALPHA):.1f}")

print("\n[VIII-b] genuine orbits: from deep dips R_t <= -G to the next time R > U (U = 2); size-recovery condition")
seeds = [rng.getrandbits(256) | 1 for _ in range(300)] + [63728127, 1126015, 8088063, 13421671, 56924955]
for G in (5, 10, 20, 40):
    rec, sizefit = [], 0
    events = 0
    for mu in seeds:
        m, S, n = mu, 0, 0
        in_dip = False
        t_dip = None
        mt = None
        while m != 1 and n < 20000:
            m, d = step(m)
            S += d
            n += 1
            R = S - n * ALPHA
            if t_dip is None and R <= -G:
                t_dip, mt = n, m
            if t_dip is not None and R > 2:
                rec.append(n - t_dip)
                events += 1
                # exact identity: R_n > 2  <=>  4 m_n < mu U_n ; check the pure size criterion 4 m_n < mu
                sizefit += 4 * m < mu
                break
    if rec:
        rec.sort()
        print(f"     G={G:2d}: events {events}, mean recovery {sum(rec)/len(rec):7.1f}, median {rec[len(rec)//2]}, "
              f"max {rec[-1]}  [(U+G)/0.415 = {(2+G)/(2-ALPHA):.1f}]; recovery step already has 4 m_n < mu: {sizefit}/{events}")

# ---------------------------------------------------------------- X: entropy of the exceptional language
print(f"\n[X] U-confined positive words: log2(#words of length N)/N and log2(Geom mass)/N"
      f"   [alpha - I0 = {ALPHA - I0:.4f}, -I0 = {-I0:.4f}]")


def conf_counts(U, N):
    # layer r: counts by S (exact ints). admissible iff S - r*alpha <= U  <=>  2^(S-U) <= 3^r
    layer = {0: 1}
    for r in range(1, N + 1):
        smax = floor(U + r * ALPHA)
        while (1 << max(smax - U, 0)) > 3 ** r and smax - U >= 0:
            smax -= 1
        keys = sorted(layer)
        pref, acc, j = {}, 0, 0
        new = {}
        # new[S'] = sum_{S < S'} layer[S] for S' in [r, smax]
        acc = 0
        idx = 0
        for Sp in range(r, smax + 1):
            while idx < len(keys) and keys[idx] < Sp:
                acc += layer[keys[idx]]
                idx += 1
            if acc:
                new[Sp] = acc
        layer = new
    count = sum(layer.values())
    maxS = max(layer)
    mass_num = sum(c << (maxS - S) for S, c in layer.items())  # mass = mass_num / 2^maxS
    return count, mass_num, maxS


for U in (0, 2, 8):
    row = []
    for N in (100, 200, 400, 800):
        c, mn, mS = conf_counts(U, N)
        h = log2(c) / N if c.bit_length() < 1000 else (c.bit_length() - 1 + log2(c >> (c.bit_length() - 53)) - 52) / N
        lm = (mn.bit_length() - mS) / N
        row.append(f"N={N}: h={h:.4f}, mass={lm:+.4f}")
    print(f"     U={U}: " + "; ".join(row))

# ---------------------------------------------------------------- XV: U_0 vs classical descent / glide
print("\n[XV] U_0 (first R_n > 0) vs sigma_0 (first accelerated m_n < mu) for all odd mu in [3, 2^22):")
diff = 0
tot = 0
maxgap = 0
examples = []
for mu in range(3, 1 << 22, 2):
    m, S, n = mu, 0, 0
    u0 = s0 = None
    while u0 is None or s0 is None:
        m, d = step(m)
        S += d
        n += 1
        if u0 is None and (1 << S) > 3 ** n:
            u0 = n
        if s0 is None and m < mu:
            s0 = n
    tot += 1
    if u0 != s0:
        diff += 1
        maxgap = max(maxgap, s0 - u0)
        if len(examples) < 5:
            examples.append((mu, u0, s0))
print(f"     U_0 == sigma_0 for {tot - diff}/{tot} seeds; differing {diff}, max gap {maxgap}; examples {examples}")
