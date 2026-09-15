"""Parts X-XIII, XV: extreme values to 2^40, survivor counts at 2^36, dependence among long survivors
(orbit merging inside the confined window, prefix/cylinder clustering vs the exact survivor model)."""
import random
import re
from math import log2, log, floor, sqrt
rng = random.Random(5)
ALPHA = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = ALPHA * (1 - H2(1 / ALPHA))


def v2(n): return (n & -n).bit_length() - 1


def smax_of(r):
    s = floor(r * ALPHA)
    while s >= 0 and (1 << s) > 3 ** r:
        s -= 1
    return s


def lg(x):
    b = x.bit_length()
    return b - 60 + log2(x >> (b - 60)) if b > 60 else log2(x)


# exact P_N for U = 0 up to N = 600
layer, PN = {0: 1}, {}
for r in range(1, 601):
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
    mS = max(layer)
    PN[r] = 2.0 ** (lg(sum(c << (mS - S) for S, c in layer.items())) - mS)

# ------------------------------------------------------------------ records to 2^40
rec = []
txt = open("hist_2p32.out").read()
rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"EXIT_RECORDS U=0:(.*)", txt).group(1))]
for f in ("glide_sieve_32_36.out", "glide_sieve_36_40.out"):
    try:
        rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"RECORDS:(.*)", open(f).read()).group(1))]
    except Exception as ex:
        print("   (missing", f, ")")
print("[X-XII] M_0(X) vs independent-trials extreme-value prediction (exact P_N); Gumbel scale 1/(I0 ln 2) =",
      f"{1/(I0*log(2)):.1f} steps")
print("   log2X  M_0  M/log2X  N_med  N_[10%,90%]   M-N_med   (log2X)/I0")
for k in range(12, 41, 2):
    X = 2 ** k
    M = max([e for mu, e in rec if mu < X], default=None)
    # P(max <= N) = (1 - P_{N})^{X/2}  with P_N = P(exit > N)
    def cdf(N):
        return (1 - PN[N]) ** (X / 2) if N <= 600 else 1.0
    q = {}
    for t in (0.1, 0.5, 0.9):
        N = 1
        while cdf(N) < t:
            N += 1
        q[t] = N
    print(f"   {k:5d}  {M:4d}  {M/k:6.3f}  {q[0.5]:5d}  [{q[0.1]},{q[0.9]}]   {M-q[0.5]:+5d}    {k/I0:6.1f}")

# ------------------------------------------------------------------ survivor counts at 2^36 (and 2^40)
def hist_from(fname, key):
    t = open(fname).read()
    return {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", re.search(key + r"(.*)", t).group(1))}


h32 = hist_from("hist_2p32.out", "HIST U=0:")
print("\n[IX-b] survivors #{odd mu < X : exit > N} vs (X/2) P_N beyond the fresh-bit regime (N >= 26)")
for tag, files, k in (("2^36", ["glide_sieve_32_36.out"], 36), ("2^40", ["glide_sieve_32_36.out", "glide_sieve_36_40.out"], 40)):
    try:
        hs = [hist_from(f, "SURVIVOR_HIST:") for f in files]
    except Exception:
        continue
    out = []
    for N in (30, 60, 100, 150, 200, 250, 300):
        surv = sum(c for e, c in h32.items() if e > N) + sum(sum(c for e, c in h.items() if e > N) for h in hs)
        pred = (2 ** k / 2) * PN[N]
        out.append(f"N={N}: {surv}/{pred:.1f}={surv/pred:.3f}")
    print(f"   X={tag}: " + "  ".join(out))

# ------------------------------------------------------------------ dependence among long survivors
S180 = [tuple(map(int, l.split())) for l in open("long_survivors_2p32_T180.txt")]
print(f"\n[XIII] {len(S180)} odd mu < 2^32 with exit >= 180")


def orbit_window(mu, n):
    m, vals = mu, {}
    for t in range(n):
        vals[m] = t
        x = 3 * m + 1
        m = x >> v2(x)
    return vals


win = {mu: orbit_window(mu, e) for mu, e in S180}
parent = {mu: mu for mu, _ in S180}
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x
owner = {}
for mu, e in S180:
    for val in win[mu]:
        if val in owner:
            a, b = find(owner[val]), find(mu)
            if a != b:
                parent[a] = b
        else:
            owner[val] = mu
clusters = {}
for mu, _ in S180:
    clusters.setdefault(find(mu), []).append(mu)
sizes = sorted((len(v) for v in clusters.values()), reverse=True)
print(f"   orbit-merge clusters inside the confined windows: {len(clusters)} clusters for {len(S180)} seeds; "
      f"largest sizes {sizes[:8]}")

# prefix clustering vs the exact survivor model (Geom(2) words conditioned to stay confined for 179 steps)
Nc = 179
sm = [smax_of(r) for r in range(Nc + 2)]
B = [None] * (Nc + 1)
B[Nc] = {S: 1.0 for S in range(Nc, sm[Nc] + 1)}
for r in range(Nc - 1, -1, -1):
    nxt, cur = B[r + 1], {}
    for S in range(r, sm[r] + 1):
        tot = sum(2.0 ** (-(Sp - S)) * w for Sp, w in nxt.items() if Sp > S)
        if tot > 0:
            cur[S] = tot
    B[r] = cur


def sample_word(L=40):
    S, ds = 0, []
    for r in range(L):
        opts = [(Sp, 2.0 ** (-(Sp - S)) * w) for Sp, w in B[r + 1].items() if Sp > S]
        tot = sum(w for _, w in opts)
        x = rng.random() * tot
        for Sp, w in opts:
            x -= w
            if x <= 0:
                break
        ds.append(Sp - S)
        S = Sp
    return ds


def word(mu, L=40):
    out, m = [], mu
    for _ in range(L):
        x = 3 * m + 1
        d = v2(x)
        out.append(d)
        m = x >> d
    return out


gen = [word(mu) for mu, _ in S180]
mod = [sample_word() for _ in range(len(S180))]
def cp_hist(ws):
    h = {}
    for i in range(len(ws)):
        for j in range(i + 1, len(ws)):
            a, b = ws[i], ws[j]
            c = 0
            while c < len(a) and a[c] == b[c]:
                c += 1
            h[c] = h.get(c, 0) + 1
    return h
hg, hm = cp_hist(gen), cp_hist(mod)
tot = len(S180) * (len(S180) - 1) // 2
print("   pairwise common word-prefix length: genuine survivors vs exact survivor-model words (fraction of pairs)")
for c in range(0, 16):
    g = sum(v for k, v in hg.items() if k >= c) / tot
    m = sum(v for k, v in hm.items() if k >= c) / tot
    print(f"     >= {c:2d}: genuine {g:.5f}   model {m:.5f}   ratio {g/m if m else float('inf'):.2f}")
# PairValuation cross-check on every pair: v2(mu_j - mu_i) = S_cp + min(a, b)
bad = 0
for i in range(len(S180)):
    for j in range(i + 1, len(S180)):
        a, b = gen[i], gen[j]
        c = 0
        while a[c] == b[c]:
            c += 1
        bad += v2(S180[j][0] - S180[i][0]) != sum(a[:c]) + min(a[c], b[c])
print(f"   PairValuation check v2(mu_i - mu_j) = S_k + min(a,b) on all {tot} pairs: {tot - bad}/{tot}")
# cylinder occupancy mod 2^k
for k in (8, 12, 16, 20):
    cls = {}
    for mu, _ in S180:
        cls[mu % (1 << k)] = cls.get(mu % (1 << k), 0) + 1
    print(f"   classes mod 2^{k}: {len(cls)} distinct among {len(S180)}; max occupancy {max(cls.values())}")
