"""Parts XXV-XXVIII, XLII-XLIII: triangle sizes met by sampled confined paths (sampler of hop_2026-09-15/hops.py).

Visit = maximal run of consecutive black cells with the same apex (Tao up-then-left climb); size = ln(eta/|U(apex)|).
Reports: size distribution of visits and of path time (with 95% CIs over paths), conditional size laws (headroom,
entry digit, previous size), autocorrelation of successive visit sizes, E[e^{tau R}], a coarse
(headroom-bin, black, size-bin) transition matrix, and per-path good-block fractions (lambda = 1, N0 = 2, 4).
usage: python3 tri_paths.py J npaths [random]"""
import math, random, sys
from collections import Counter, defaultdict

AL = math.log2(3); eta = 1 / 54
J, NP = int(sys.argv[1]), int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else "true"
random.seed(3000 + J)
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
xi = 1
if mode == "random":
    xi = random.randrange(1, 3 ** (J + 5)) | 1
    xi = xi if xi % 3 else xi + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
NEG = float("-inf")
def lae(x, y):
    if x == NEG: return y
    if y == NEG: return x
    return max(x, y) + math.log1p(math.exp(-abs(x - y)))
g = [None] * (J + 1); g[J] = [NEG] * (sg + 2); g[J][sg] = 0.0
for i in range(J - 1, -1, -1):
    nxt = g[i + 1]; row = [NEG] * (sg + 2); acc = NEG
    for S in range(top[i + 1], -1, -1):
        row[S] = acc if S <= top[i] else NEG
        acc = lae(acc, nxt[S])
    g[i] = row
def sample_path():
    S = [0]
    for i in range(J):
        lo, hi = S[-1] + 1, top[i + 1]
        sl = g[i + 1][lo: hi + 1]; mx = max(sl)
        S.append(random.choices(range(lo, hi + 1), weights=[math.exp(x - mx) for x in sl])[0])
    return S
yc = {}
def Y(a, b):
    k = (a, b)
    if k not in yc:
        q = 3 ** b; v = xi * pow(2, -a, q) % q
        yc[k] = v - q if v > q // 2 else v
    return yc[k]
black = lambda a, b: 54 * abs(Y(a, b)) < 3 ** b
def apex(a, b):
    while black(a + 1, b): a += 1
    while black(a, b + 1): b += 1
    return (a, b), math.log(3 ** b / (54 * abs(Y(a, b))))

visits = []                   # (size, residence, entry_digit, headroom, prev_size)
time_le = defaultdict(list); vis_le = defaultdict(list)
gb2 = []; gb4 = []; trans = Counter()
hb = lambda h: min(h, 3)
sb = lambda s: 0 if s is None else (1 if s < 2 else 2)
for _ in range(NP):
    S = sample_path()
    a = [m - s for s in S[:J]]; d = [S[i + 1] - S[i] for i in range(J)]
    col = [black(a[i], i + 1) for i in range(J)]
    ap = [apex(a[i], i + 1) if col[i] else None for i in range(J)]
    pv = []; prev = None; i = 0
    tin = Counter()
    while i < J:
        if not col[i]: i += 1; continue
        k = ap[i][0]; s0 = i
        while i < J and col[i] and ap[i][0] == k: i += 1
        size = ap[s0][1]; res = i - s0
        visits.append((size, res, d[s0 - 1] if s0 > 0 else 0, top[s0] - S[s0], prev))
        pv.append((size, res)); prev = size
    for R0 in range(1, 7):
        nv = len(pv)
        vis_le[R0].append(sum(1 for s, _ in pv if s <= R0) / nv if nv else float("nan"))
        time_le[R0].append((sum(r for s, r in pv if s <= R0) / J, sum(r for s, r in pv if s > R0) / J))
    for i in range(J - 1):
        st = (hb(top[i] - S[i]), col[i], sb(ap[i][1] if ap[i] else None))
        st2 = (hb(top[i + 1] - S[i + 1]), col[i + 1], sb(ap[i + 1][1] if ap[i + 1] else None))
        trans[(st, st2)] += 1
    for N0, store in ((2, gb2), (4, gb4)):
        cnt = 0
        for r in range(J // 2 - 1):
            x = S[2 * r + 1]; lo_, hi_ = S[2 * r], min(S[2 * r + 2] - 1, top[2 * r + 1])
            nB = hi_ - lo_
            if 2 <= nB <= N0 and x + 1 <= hi_ and not black(m - x, 2 * r + 2): cnt += 1
        store.append(cnt / (J // 2))

def ci(xs):
    xs = [x for x in xs if x == x]; n = len(xs); mu = sum(xs) / n
    sd = math.sqrt(sum((x - mu) ** 2 for x in xs) / max(n - 1, 1)); return mu, 1.96 * sd / math.sqrt(n)
print(f"J={J} env={mode} paths={NP}: visits {len(visits)} ({len(visits) / NP:.2f}/path)")
print("  XXV  R0: frac of visits with size<=R0 | frac of path time in size<=R0 | in size>R0   (mean +- 95% CI)")
for R0 in range(1, 7):
    v_ = ci(vis_le[R0]); a_ = ci([x for x, _ in time_le[R0]]); b_ = ci([y for _, y in time_le[R0]])
    print(f"       {R0}: {v_[0]:.3f}+-{v_[1]:.3f} | {a_[0]:.4f}+-{a_[1]:.4f} | {b_[0]:.5f}+-{b_[1]:.5f}")
def cond(key, bins, label):
    groups = defaultdict(list)
    for vv in visits:
        kk = key(vv)
        if kk is not None: groups[bins(kk)].append(vv[0])
    print(f"  XXVI {label}: " + "  ".join(f"{k}: n={len(v)} mean={sum(v)/len(v):.2f} P(>=2)={sum(1 for x in v if x >= 2)/len(v):.3f}"
                                         for k, v in sorted(groups.items()) if len(v) >= 20))
cond(lambda v: v[3], lambda h: min(h, 4), "headroom (4 = >=4)")
cond(lambda v: v[2] if v[2] else None, lambda d_: min(d_, 4), "entry digit (4 = >=4)")
cond(lambda v: v[4], lambda s: 0 if s < 1 else (1 if s < 2 else (2 if s < 3 else 3)), "previous size bin (<1,<2,<3,>=3)")
# XXVII autocorrelation of successive visit sizes (within paths, lags 1..10); visits list is path-ordered
sizes = [v[0] for v in visits]; mu = sum(sizes) / len(sizes); var = sum((s - mu) ** 2 for s in sizes) / len(sizes)
# path boundaries: prev_size None marks a path's first visit
starts = [k for k, v in enumerate(visits) if v[4] is None] + [len(visits)]
ac = []
for lag in range(1, 11):
    num = 0.0; n = 0
    for p_ in range(len(starts) - 1):
        seg = sizes[starts[p_]:starts[p_ + 1]]
        for k in range(len(seg) - lag):
            num += (seg[k] - mu) * (seg[k + lag] - mu); n += 1
    ac.append(num / n / var if n else float("nan"))
print("  XXVII autocorr lags 1..10: " + " ".join(f"{x:+.3f}" for x in ac) + f"   (n visits {len(sizes)}, 1/sqrt(n) = {1/math.sqrt(len(sizes)):.3f})")
print("  XXVIII E[e^{tau R}] over visits: " + "  ".join(f"tau={tau}: {sum(math.exp(tau * s) for s in sizes)/len(sizes):.3f}"
                                                     for tau in (0.25, 0.5, 0.75, 0.9)) +
      f"   mean R = {mu:.3f}, mean residence = {sum(v[1] for v in visits)/len(visits):.3f}")
gm2 = ci(gb2); gm4 = ci(gb4)
print(f"  good-block fraction per path (lambda=1, path-level): N0=2 {gm2[0]:.4f}+-{gm2[1]:.4f} (min {min(gb2):.3f}); "
      f"N0=4 {gm4[0]:.4f}+-{gm4[1]:.4f} (min {min(gb4):.3f})")
rows = defaultdict(Counter)
for (s1, s2), c in trans.items(): rows[s1][s2] += c
print("  XLII coarse chain (headroom-bin, black, size-bin) -> P(next black):")
for s1 in sorted(rows):
    tot = sum(rows[s1].values())
    if tot >= 200:
        pb = sum(c for s2, c in rows[s1].items() if s2[1]) / tot
        print(f"     {s1}: n={tot} P(next black)={pb:.4f}")
