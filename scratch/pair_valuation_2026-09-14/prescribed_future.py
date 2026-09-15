"""Prescribed-future matching M_j(D_j, e) = v2(T_j(D_j) - A_{j,inf}(e)): exact finite checks + DP.

Exact arithmetic only. Drift comparisons S - r*log2(3) <= c are decided exactly for rational c = p/q
via 2^(qS - p) <= 3^(qr).  Paper objects (T_j, A_{j,m}) are implemented literally as in
transport_collapse_check.py.

Sections
  1. prescribed matching = split depth against the anchor future e* = word(mu_j)   (paper-literal)
     + finite detectability: a block e_1..e_m fixes A_{j,inf} mod 2^(D_m+1) via A_{j,m+1}
  2. every odd mu, 3 !| mu, is an anchor state (backward-chain construction)
  3. constrained families: exact L_C, M^max by DP along the anchor, checked against exhaustive
     search of all admissible blocks with the paper-literal matching
  4. dependence on the past prefix; anchor-residue density vs iid Geom(2) persistence probability
"""

import random
import time
from fractions import Fraction
from math import log2, floor

rng = random.Random(20260917)
ALPHA = log2(3)


# ------------------------------------------------------------------ basic arithmetic
def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1 if n else None


def a_(m):
    return v2(3 * m + 1)


def T_(m):
    x = 3 * m + 1
    return x >> v2(x)


def word(m, L):
    out = []
    for _ in range(L):
        out.append(a_(m))
        m = T_(m)
    return out


def drift_le(S, r, c):
    """exact test S - r*alpha <= c for rational c."""
    c = Fraction(c)
    p, q = c.numerator, c.denominator
    e = q * S - p
    return e < 0 or (1 << e) <= 3 ** (q * r)


def drift_ge(S, r, c):
    """exact test S - r*alpha >= c (never equality for r >= 1 by irrationality)."""
    return not drift_le(S, r, c) or (S - r * ALPHA == float(c))


def floor_c_plus(c, r):
    """exact floor(c + r*alpha)."""
    M = floor(float(c) + r * ALPHA) + 2
    while not drift_le(M, r, c):
        M -= 1
    return M


def C_of(d, j):
    C, S = 0, 0
    for i in range(j):
        C = 3 * C + (1 << S)
        S += d[i]
    return C, S


def paper_past(d, j, prec):
    C, S = C_of(d, j)
    mod = 1 << (S + prec)
    xi = (-C * pow(3, -j, mod)) % mod
    return xi % (1 << S), (xi >> S) & 1, xi >> S, S, C  # chi, beta, T mod 2^prec, S_j, C_j


def paper_target(fut, j, prec, nterms=None):
    """A_{j,nterms} mod 2^prec (nterms None: enough terms for exactness mod 2^prec)."""
    mod = 1 << prec
    tot, D = 0, 0
    for r, dr in enumerate(fut):
        if nterms is None and D >= prec:
            return tot
        if nterms is not None and r == nterms:
            return tot
        tot = (tot + pow(2, D, mod) * pow(3, -(j + 1 + r), mod)) % mod
        D += dr
    if nterms is not None and len(fut) >= nterms:
        return tot
    if nterms is None and D >= prec:
        return tot
    raise ValueError("future too short")


def anchor(d, j):
    chi, beta, _, S, C = paper_past(d, j, 1)
    mu, rem = divmod(3 ** j * chi + C, 1 << S)
    assert rem == 0
    return mu, beta, S, chi


def geom():
    q = 1
    while rng.random() < 0.5:
        q += 1
    return q


# ------------------------------------------------------------------ Section 1
t0 = time.time()
P = 140
s1 = dict(cases=0, beta0=0, fail=0, blocks=0, detect_fail=0, Ajm_extra_bit_fail=0)
for _ in range(6000):
    seed = rng.getrandbits(rng.choice([16, 48])) | 1
    j = rng.randint(1, 14)
    Dj = word(seed, j)
    chi, beta, T, S, C = paper_past(Dj, j, P)
    mu, _, _, _ = anchor(Dj, j)
    estar = word(mu, 300) if mu % 2 else None
    for _ in range(4):
        if estar is not None and rng.random() < 0.7:
            m = rng.randint(0, 25)
            b = estar[m]
            a = rng.choice([x for x in range(1, max(b, 3) + 3) if x != b])
            e = estar[:m] + [a] + [geom() for _ in range(200)]
            pred = sum(estar[:m]) + min(a, b)
        else:
            e = [geom() for _ in range(200)]
            if estar is None:
                pred = 0
            else:
                m = 0
                while e[m] == estar[m]:
                    m += 1
                pred = sum(e[:m]) + min(e[m], estar[m])
        A = paper_target(e, j, P)
        Mpaper = v2((T - A) % (1 << P))
        s1["cases"] += 1
        s1["beta0"] += beta == 0
        s1["fail"] += Mpaper != pred
    # finite detectability with blocks
    if estar is not None:
        for _ in range(3):
            m = rng.randint(1, 12)
            same = rng.random() < 0.5
            blk = estar[:m] if same else [geom() for _ in range(m)]
            same = blk == estar[:m]
            Dm = sum(blk)
            # A_{j,m+1} needs D_0..D_m, i.e. the whole block (terms r = 0..m)
            mod = 1 << (Dm + 1)
            tot, D = 0, 0
            for r in range(m + 1):
                tot = (tot + pow(2, D, mod) * pow(3, -(j + 1 + r), mod)) % mod
                if r < m:
                    D += blk[r]
            detected = (T - tot) % mod == 0
            s1["blocks"] += 1
            s1["detect_fail"] += detected != same
            # the paper's A_{j,m} (terms r < m) is only exact mod 2^{D_m}
            tot2, D = 0, 0
            for r in range(m):
                tot2 = (tot2 + pow(2, D, mod) * pow(3, -(j + 1 + r), mod)) % mod
                D += blk[r]
            if same:
                s1["Ajm_extra_bit_fail"] += (T - tot2) % mod != 0
print(f"[1] prescribed matching = split depth vs anchor word: {s1}  ({time.time()-t0:.1f}s)")
print("    detect_fail = blocks where (T = A_{j,m+1} mod 2^(D_m+1)) != (block == anchor block)")
print("    Ajm_extra_bit_fail = anchor blocks where the paper's A_{j,m} misses the extra bit")

# ------------------------------------------------------------------ Section 2
t0 = time.time()
ok = total = 0
for mu in range(1, 3000, 2):
    if mu % 3 == 0:
        continue
    total += 1
    x, chain = mu, 0
    jneed = 1
    while 3 ** jneed <= mu:
        jneed += 1
    for _ in range(jneed):
        a = 1
        while (pow(2, a, 3) * x) % 3 != 1:
            a += 1
        n = ((1 << a) * x - 1) // 3
        while n % 3 == 0:
            a += 2
            n = ((1 << a) * x - 1) // 3
        x = n
    Dj = word(x, jneed)
    m2, beta, S, chi = anchor(Dj, jneed)
    ok += (m2 == mu and beta == 1 and x < (1 << S))
print(f"[2] odd mu < 3000 with 3 !| mu realised as anchor states: {ok}/{total}  ({time.time()-t0:.1f}s)")

# ------------------------------------------------------------------ Section 3
# a family = (name, admissible(S, r) predicate on states r >= 1, extendable(S, r) predicate, horizon)
def fam_confined(c):
    return (f"confined c={c}", lambda S, r: drift_le(S, r, c), lambda S, r: True, None)


def fam_corridor(g, U):
    return (f"corridor [-{g},{U}]", lambda S, r: drift_le(S, r, U) and drift_ge(S, r, -g),
            lambda S, r: True, None)


def fam_terminal(H, w):
    # |S_H - H alpha| <= w only at the horizon; extendable iff the minimal completion fits
    lo, hi = Fraction(-w), Fraction(w)
    def adm(S, r):
        return (r < H) or (drift_le(S, r, hi) and drift_ge(S, r, lo))
    def ext(S, r):
        return r >= H or drift_le(S + (H - r), H, hi)
    return (f"near-critical |S_{H}-{H}a|<={w}", adm, ext, H)


def fam_persist(c, n):
    return (f"persistence c={c} horizon {n}", lambda S, r: r > n or drift_le(S, r, c),
            lambda S, r: True, None)


CAP = 400


def shadow(estar, fam):
    """Exact L_C (capped) and M^max via the anchor-following DP (optimum diverges at L+1)."""
    name, adm, ext, H = fam
    S, L = 0, 0
    while L < len(estar) and (H is None or L < H):
        S2, r2 = S + estar[L], L + 1
        if adm(S2, r2) and ext(S2, r2):
            S, L = S2, r2
        else:
            break
    if (H is None and L >= len(estar)) or (H is not None and L >= H):
        return L, None  # follows the anchor through the whole horizon/cap: M^max = infinity
    b = estar[L]
    best = None
    for a in range(1, b + 40):
        if a == b:
            continue
        if adm(S + a, L + 1) and ext(S + a, L + 1):
            val = S + min(a, b)
            best = val if best is None else max(best, val)
    return L, best


def exhaustive_max(Dj, j, fam, Hmax):
    """max over ALL admissible-extendable blocks of length Hmax of the paper-literal finite matching."""
    name, adm, ext, H = fam
    chi, beta, T, S0, C = paper_past(Dj, j, 200)
    best = -1
    stack = [([], 0)]
    while stack:
        blk, S = stack.pop()
        r = len(blk)
        if r == Hmax:
            Dm = S
            mod = 1 << (Dm + 1)
            tot, D = 0, 0
            for rr in range(r + 1):
                tot = (tot + pow(2, D, mod) * pow(3, -(j + 1 + rr), mod)) % mod
                if rr < r:
                    D += blk[rr]
            x = (T - tot) % mod
            val = v2(x) if x else Dm + 1
            best = max(best, val)
            continue
        for a in range(1, 30):
            if adm(S + a, r + 1) and ext(S + a, r + 1):
                stack.append((blk + [a], S + a))
            elif not drift_le(S + a, r + 1, 10 ** 6):
                break
    return best


t0 = time.time()
fams = [fam_confined(0), fam_confined(Fraction(1, 2)), fam_confined(1), fam_confined(2),
        fam_corridor(1, 1), fam_corridor(2, 1), fam_corridor(3, 2),
        fam_terminal(20, Fraction(1, 2)), fam_terminal(40, 1),
        fam_persist(0, 15)]
ver = {f[0]: [0, 0] for f in fams}
formula_conf = [0, 0]
for _ in range(250):
    seed = rng.getrandbits(40) | 1
    j = rng.randint(2, 10)
    Dj = word(seed, j)
    mu, beta, S, chi = anchor(Dj, j)
    if beta == 0:
        continue
    estar = word(mu, CAP)
    for fam in fams:
        L, best = shadow(estar, fam)
        if fam[0].startswith("confined") and best is not None:
            c = Fraction(fam[0].split("=")[1])
            formula_conf[0] += 1
            formula_conf[1] += best == floor_c_plus(c, L + 1)
        if best is not None and L + 1 <= 9 and fam[3] is None:
            ex = exhaustive_max(Dj, j, fam, L + 2)
            ver[fam[0]][0] += 1
            ver[fam[0]][1] += ex == best
print(f"[3a] confined: DP M^max == floor(c + (L_c(mu)+1) alpha): {formula_conf[1]}/{formula_conf[0]}")
print(f"[3b] DP M^max == exhaustive max of paper-literal finite matching (L+1 <= 9): "
      + ", ".join(f"{k}: {v[1]}/{v[0]}" for k, v in ver.items() if v[0]) + f"  ({time.time()-t0:.1f}s)")

# forced divergence and shadowing statistics over many past prefixes
t0 = time.time()
rows = []
nodiv = {f[0]: 0 for f in fams}
for _ in range(4000):
    kind = rng.random()
    if kind < 0.5:
        seed = rng.getrandbits(64) | 1
        j = rng.choice([5, 10, 20, 40])
        Dj = word(seed, j)
        src = "genuine"
    else:
        # confined past prefix (c = 0) by random confined walk
        j = rng.choice([10, 20, 40])
        Dj, S = [], 0
        while len(Dj) < j:
            cand = [x for x in (1, 2, 3) if drift_le(S + x, len(Dj) + 1, 0)]
            x = rng.choice(cand)
            Dj.append(x)
            S += x
        src = "confined"
    mu, beta, S, chi = anchor(Dj, j)
    if beta == 0:
        rows.append((src, j, S, beta, None, None, None, None))
        continue
    estar = word(mu, CAP)
    out = []
    for fam in fams:
        L, best = shadow(estar, fam)
        if best is None:
            nodiv[fam[0]] += 1
        out.append((L, best))
    Fj = S - log2(chi)
    Rj = S - j * ALPHA
    rows.append((src, j, S, beta, Fj, Rj, log2(mu), out))
print(f"[3c] prefixes whose anchor follows the family through the whole cap/horizon (M^max = inf): {nodiv}"
      f"  ({time.time()-t0:.1f}s)")
b1 = [r for r in rows if r[3] == 1]
print(f"     beta_j=1 prefixes: {len(b1)}/{len(rows)} (beta_j=0 => M = 0 for every prescribed future)")
for fi, fam in enumerate(fams):
    Ls = [r[7][fi][0] for r in b1]
    Ms = [r[7][fi][1] for r in b1 if r[7][fi][1] is not None]
    print(f"     {fam[0]:34s} L_C: mean {sum(Ls)/len(Ls):6.2f} max {max(Ls):4d} | "
          f"M^max: mean {sum(Ms)/max(len(Ms),1):6.2f} max {max(Ms) if Ms else '-'}")

# ------------------------------------------------------------------ Section 4: past dependence
print("\n[4] dependence of L_0 (confined c=0 shadowing length) on past descriptors (beta_j = 1):")


def corr(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    return sxy / (sxx * syy) ** 0.5


L0 = [r[7][0][0] for r in b1]
for name, idx in (("j", 1), ("S_j", 2), ("F_j", 4), ("R_j", 5), ("log2 mu_j", 6)):
    print(f"     corr(L_0, {name:9s}) = {corr([r[idx] for r in b1], L0):+.3f}")
for src in ("genuine", "confined"):
    Ls = [r[7][0][0] for r in b1 if r[0] == src]
    print(f"     past source {src:8s}: n={len(Ls)}  mean L_0 = {sum(Ls)/len(Ls):.3f}  max {max(Ls)}")
# control: generic odd mu (3 !| mu) of matched size
ctrl = []
for r in b1[:1500]:
    target = r[6]
    mu = rng.getrandbits(max(int(target), 1) + 1) | 1
    while mu % 3 == 0:
        mu += 2
    S_, L = 0, 0
    for x in word(mu, CAP):
        if drift_le(S_ + x, L + 1, 0):
            S_ += x
            L += 1
        else:
            break
    ctrl.append(L)
print(f"     control, generic odd mu (3 !| mu) of the same bit length: mean L_0 = {sum(ctrl)/len(ctrl):.3f}")

# anchor-residue density of {L_0 >= L} vs exact iid Geom(2) persistence probability
print("\n[4b] density of odd mu < 2^22 (3 !| mu) with L_0(mu) >= L  vs  P_Geom(2)(0-confined for L steps):")
t0 = time.time()
LIM = 1 << 22
hist = {}
cnt = 0
for mu in range(1, LIM, 2):
    if mu % 3 == 0:
        continue
    cnt += 1
    m, S_, L = mu, 0, 0
    while True:
        x = 3 * m + 1
        d = v2(x)
        if drift_le(S_ + d, L + 1, 0):
            S_ += d
            L += 1
            m = x >> d
        else:
            break
    hist[L] = hist.get(L, 0) + 1
# exact persistence probability by DP over S (digits Geom(2), weight 2^-d)
prob = {0: Fraction(1)}
pers = [Fraction(1)]
for r in range(1, 31):
    new = {}
    for S_, w in prob.items():
        d = 1
        while drift_le(S_ + d, r, 0):
            new[S_ + d] = new.get(S_ + d, 0) + w / (1 << d)
            d += 1
    prob = new
    pers.append(sum(prob.values()))
tail = 0
tails = {}
for L in sorted(hist, reverse=True):
    tail += hist[L]
    tails[L] = tail
for L in (1, 2, 3, 5, 8, 10, 13, 16, 20, 25, 30):
    emp = sum(v for k, v in hist.items() if k >= L) / cnt
    print(f"     L={L:2d}: density {emp:.6f}   iid persistence {float(pers[L]):.6f}   "
          f"(S_L ~ {L*ALPHA:.0f} bits vs 22-bit range)")
print(f"     max L_0 over odd mu < 2^22 with 3 !| mu: {max(hist)}  ({time.time()-t0:.1f}s)")
