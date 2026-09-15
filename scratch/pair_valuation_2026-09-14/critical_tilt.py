"""Critical-tilt round: constants, exact confined-word DP, survivor-count test, extreme values,
record holders vs the exact conditioned survivor model, depth scaling, pair/genealogy of records.
Exact integer DP; floats only for reporting logs and for the conditioned-sampling weights."""
import random
import re
import sys
from math import log2, log, floor, sqrt, exp
rng = random.Random(20260921)
ALPHA = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
I0 = ALPHA * (1 - H2(1 / ALPHA))

# ------------------------------------------------------------------ I-II: constants
p = 1 / ALPHA
tilt = lambda k: p * (1 - p) ** (k - 1)
KL = sum(tilt(k) * log2(tilt(k) / 2.0 ** (-k)) for k in range(1, 400))
Htilt = -sum(tilt(k) * log2(tilt(k)) for k in range(1, 400))
lamstar = log(ALPHA / (2 * (ALPHA - 1)))
print("[I] critical tilt P*(d=k) = (1/alpha)(1-1/alpha)^(k-1):")
print(f"    mean {sum(k*tilt(k) for k in range(1,400)):.10f} (alpha {ALPHA:.10f}); P*(1) {p:.5f}; P*(>=4) {(1-p)**3:.5f}")
print(f"    Shannon entropy {Htilt:.6f} = alpha*H2(1/alpha) = {ALPHA*H2(p):.6f} = alpha - I0 = {ALPHA-I0:.6f}")
print(f"    KL(P* || Geom(1/2)) = {KL:.8f} = I0 = {I0:.8f};  tilt parameter theta = ln(2(1-1/alpha)) = "
      f"{log(2*(1-p)):.6f} = -lambda* = {-lamstar:.6f}")
print("[II] constants:")
print(f"    alpha = {ALPHA:.6f} | I0 = {I0:.6f} | alpha-I0 = {ALPHA-I0:.6f} | H2(1/alpha) = {H2(p):.6f} | "
      f"1-H2(1/alpha) = I0/alpha = {1-H2(p):.6f}")
print(f"    Renyi-2 of Geom(1/2) per digit = -log2(1/3) = {log2(3):.6f};  Renyi-2 of P* = log2(2 alpha - 1) = {log2(2*ALPHA-1):.6f}")
print(f"    survivor-ensemble rates (predicted): Shannon alpha-I0 = {ALPHA-I0:.4f}, Renyi-2 alpha-2 I0 = {ALPHA-2*I0:.4f}, "
      f"min-entropy 1-I0 = {1-I0:.4f}")

# ------------------------------------------------------------------ III, VIII: exact DP
def smax_of(U, r):
    s = floor(U + r * ALPHA)
    while s - U >= 0 and (1 << (s - U)) > 3 ** r:
        s -= 1
    return s


def dp_layers(U, N, checkpoints):
    layer = {0: 1}
    out = {}
    for r in range(1, N + 1):
        sm = smax_of(U, r)
        keys = sorted(layer)
        new, acc, idx = {}, 0, 0
        for Sp in range(r, sm + 1):
            while idx < len(keys) and keys[idx] < Sp:
                acc += layer[keys[idx]]
                idx += 1
            if acc:
                new[Sp] = acc
        layer = new
        if r in checkpoints:
            out[r] = dict(layer)
    return out


def lg(x):  # log2 of big positive int
    b = x.bit_length()
    return b - 60 + log2(x >> (b - 60)) if b > 60 else log2(x)


CKS = [25, 50, 100, 200, 300, 400, 600, 800, 1000, 1200, 1600, 2000, 2400, 3000]
rows = {}
for U in (0, 2):
    L = dp_layers(U, 3000, set(CKS) | set(range(1, 301)))
    rows[U] = L
print("\n[III/VIII] exact DP (U-confined positive words):  log2|W| - (alpha-I0)N ,  log2 P_N + I0 N  (P_N = Geom mass)")
fit = {}
for U in (0, 2):
    xs, yw, yp = [], [], []
    for N in CKS:
        lay = rows[U][N]
        cnt = sum(lay.values())
        mS = max(lay)
        mass_num = sum(c << (mS - S) for S, c in lay.items())
        lW = lg(cnt)
        lP = lg(mass_num) - mS
        q_num = sum(c << (2 * (mS - S)) for S, c in lay.items())
        lQ = lg(q_num) - 2 * mS
        ES = sum(c * S << (mS - S) for S, c in lay.items())
        EpS = 2 ** (lg(ES) - lg(mass_num))  # E_p[S] under p_w = 2^-S / P_N
        Hsh = EpS + lP                      # Shannon entropy = E_p[S] + log2 P_N
        H2r = -(lQ - 2 * lP)
        Hmin = N + lP
        frac = (U + N * ALPHA) % 1
        if N >= 200:
            xs.append(log2(N)); yw.append(lW - (ALPHA - I0) * N); yp.append(lP + I0 * N)
        print(f"   U={U} N={N:5d}: log2|W|/N {lW/N:.5f}  resid {lW-(ALPHA-I0)*N:8.3f} | log2P/N {lP/N:+.5f} "
              f"resid {lP+I0*N:8.3f} | survivor rates: Shannon {Hsh/N:.4f} Renyi2 {H2r/N:.4f} min {Hmin/N:.4f} | frac(U+N a) {frac:.2f}")
    n = len(xs)
    mx = sum(xs) / n
    for name, ys in (("words", yw), ("mass", yp)):
        my = sum(ys) / n
        b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        res = [y - my - b * (x - mx) for x, y in zip(xs, ys)]
        fit[(U, name)] = b
        print(f"   U={U} fit resid ~ slope*log2 N over N in [200,3000]: {name}: slope {b:+.3f} "
              f"(max |residual| {max(abs(r) for r in res):.3f})")

# P_N and |W|(N) for N <= 300 (U = 0) for later use
PN = {}
for N in range(1, 301):
    lay = rows[0][N]
    mS = max(lay)
    PN[N] = (sum(c << (mS - S) for S, c in lay.items()), mS)  # mass = num / 2^mS


def PN_float(N):
    num, mS = PN[N]
    return 2.0 ** (lg(num) - mS)


# ------------------------------------------------------------------ IX/XVI/XVII: survivor counts vs (X/2) P_N
def read_hist(fname, U):
    txt = open(fname).read()
    h = re.search(rf"HIST U={U}:(.*)", txt).group(1)
    return {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", h)}


print("\n[IX] actual survivors #{odd mu < X: exit > N} (U=0)  vs  independent-trials prediction (X/2) P_N")
for k in (24, 28, 32):
    try:
        hist = read_hist(f"hist_2p{k}.out", 0)
    except Exception:
        continue
    X = 2 ** k
    tot = sum(hist.values())
    line = []
    for N in (5, 10, 15, 20, 25, 30, 40, 60, 80, 100, 130, 160, 200):
        surv = sum(c for e, c in hist.items() if e > N)
        pred = (X / 2) * PN_float(N)
        fresh = "F" if ALPHA * N + 1 <= k else " "
        line.append(f"N={N}{fresh}: {surv}/{pred:.1f}={surv/pred:.3f}" if pred > 0 else "")
    print(f"   X=2^{k}: " + "  ".join(line))
print("   (F = fresh-bit regime alpha*N + 1 <= log2 X, where realizer classes are fully resolved)")

# ------------------------------------------------------------------ X-XII: records vs extreme-value prediction
txt32 = open("hist_2p32.out").read() if True else ""
rec = [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"EXIT_RECORDS U=0:(.*)", txt32).group(1))]
try:
    sv = open("glide_sieve.out").read()
    rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"RECORDS:(.*)", sv).group(1))]
except Exception:
    pass
print("\n[X-XII] M_0(X) = max exit over odd mu < X vs extreme-value prediction; 1/I0 =", f"{1/I0:.4f}")
print("   log2X  M_0(X)  M/log2X  M/(log2X)^2   N_pred(median: (X/2)P_N = ln2)   naive log2X/I0   M - N_pred")
Pcache = {}
def PN_any(N):
    return PN_float(N) if N <= 300 else None
for k in range(12, 41, 2):
    X = 2 ** k
    M = max([e for mu, e in rec if mu < X], default=None)
    if M is None:
        continue
    Npred = None
    for N in range(1, 301):
        if (X / 2) * PN_float(N) < log(2):
            Npred = N
            break
    print(f"   {k:5d}  {M:6d}  {M/k:7.3f}  {M/k/k:9.4f}     {Npred if Npred else '>300':>5}          "
          f"{k/I0:7.1f}         {M - Npred if Npred else ''}")

# ------------------------------------------------------------------ VI: record holders vs conditioned survivor model
def v2(n): return (n & -n).bit_length() - 1
def word_to_exit(mu):
    m, S, n, ds, Rs = mu, 0, 0, [], []
    while True:
        x = 3 * m + 1; d = v2(x); m = x >> d; S += d; n += 1; ds.append(d); Rs.append(S - n * ALPHA)
        if (1 << S) > 3 ** n:
            return ds, Rs


def model_sampler(Nexit):
    """Geom(2) words conditioned on: R_k <= 0 for k < Nexit and R_Nexit > 0 (exit exactly at Nexit)."""
    # backward masses B[r][S]: Geom mass of completions from state (r, S)
    sm = [smax_of(0, r) for r in range(Nexit + 1)]
    B = [None] * (Nexit + 1)
    # step Nexit-1 -> Nexit must exit: S' > sm[Nexit]; mass of digits d with S+d > sm[N]: 2^-(sm[N]-S)
    B[Nexit - 1] = {S: 2.0 ** (-(sm[Nexit] - S)) for S in range(Nexit - 1, sm[Nexit - 1] + 1)}
    for r in range(Nexit - 2, -1, -1):
        nxt = B[r + 1]
        cur = {}
        for S in range(r, sm[r] + 1):
            tot = 0.0
            for Sp, w in nxt.items():
                if Sp > S:
                    tot += 2.0 ** (-(Sp - S)) * w
            if tot > 0:
                cur[S] = tot
        B[r] = cur
    def sample():
        S, ds = 0, []
        for r in range(Nexit - 1):
            nxt = B[r + 1]
            opts = [(Sp, 2.0 ** (-(Sp - S)) * w) for Sp, w in nxt.items() if Sp > S]
            tot = sum(w for _, w in opts)
            x = rng.random() * tot
            for Sp, w in opts:
                x -= w
                if x <= 0:
                    break
            ds.append(Sp - S); S = Sp
        # last digit: exit, d > sm[N] - S, Geom tail -> d = (sm[N]-S) + Geom(1/2)
        d = sm[Nexit] - S
        while True:
            d += 1
            if rng.random() < 0.5:
                break
        ds.append(d)
        return ds
    return sample


def emp_stats(ds):
    n = len(ds)
    K = 8
    cnt = [0] * (K + 1)
    for d in ds:
        cnt[min(d, K)] += 1
    ph = [c / n for c in cnt]
    kl = 0.0
    for k in range(1, K + 1):
        q = tilt(k) if k < K else (1 - p) ** (K - 1)
        if ph[k] > 0:
            kl += ph[k] * log2(ph[k] / q)
    ent = -sum(x * log2(x) for x in ph[1:] if x > 0)
    return sum(ds) / n, ph[1], sum(ph[4:]), ent, kl


print("\n[VI] record holders (U=0) vs exact conditioned survivor model at the same exit length N")
print("   mu            N   mean   p1    p>=4  KL(p^||P*) | model(100 samples): KL mean [5%,95%]   p1 mean   rec KL percentile")
big = [(mu, e) for mu, e in rec if e >= 60]
for mu, e in big:
    ds, Rs = word_to_exit(mu)
    mean, p1, p4, ent, kl = emp_stats(ds)
    samp = model_sampler(e)
    kls, p1s = [], []
    for _ in range(100):
        st = emp_stats(samp())
        kls.append(st[4]); p1s.append(st[1])
    kls.sort()
    pct = sum(1 for x in kls if x <= kl) / len(kls)
    print(f"   {mu:<13d} {e:4d} {mean:.3f} {p1:.3f} {p4:.3f}  {kl:.4f}     | {sum(kls)/len(kls):.4f} [{kls[5]:.4f},{kls[94]:.4f}]"
          f"   {sum(p1s)/len(p1s):.3f}     {pct:.2f}")

# ------------------------------------------------------------------ VII: depth scaling
print("\n[VII] depth below the wall at mid-path, -R_{N/2}: conditioned model vs records; scale check")
for N in (50, 100, 200, 400):
    samp = model_sampler(N)
    depths = []
    for _ in range(300 if N <= 200 else 120):
        ds = samp(); S = sum(ds[: N // 2]); depths.append(-(S - (N // 2) * ALPHA))
    md = sum(depths) / len(depths)
    print(f"   model N={N}: mean depth {md:6.2f}; /sqrt(N) {md/sqrt(N):.3f}; /log2 N {md/log2(N):.3f}")
for mu, e in big:
    ds, Rs = word_to_exit(mu)
    d = -Rs[e // 2 - 1]
    print(f"   record {mu}: N={e}, depth {d:6.2f}; /sqrt(N) {d/sqrt(e):.3f}; /log2 N {d/log2(e):.3f}")

# ------------------------------------------------------------------ XIV: pair geometry / genealogy of records
print("\n[XIV] pair geometry of U=0 records with exit >= 100: common word prefix, v2(mu_i - mu_j), orbit relations")
top = [(mu, e) for mu, e in rec if e >= 100]
words = {mu: word_to_exit(mu)[0] for mu, _ in top}
def orbit_set(mu, steps=2000):
    m, seen = mu, {}
    for n in range(steps):
        seen.setdefault(m, n)
        x = 3 * m + 1; m = x >> v2(x)
        if m == 1:
            seen.setdefault(1, n + 1); break
    return seen
orb = {mu: orbit_set(mu) for mu, _ in top}
for i, (a, ea) in enumerate(top):
    for b, eb in top[i + 1:]:
        wa, wb = words[a], words[b]
        cp = 0
        while cp < min(len(wa), len(wb)) and wa[cp] == wb[cp]:
            cp += 1
        # merge: first common orbit value
        common = set(orb[a]) & set(orb[b])
        common.discard(1)
        merge = min(common, key=lambda v: orb[b][v]) if common else None
        rel = f"orbits merge at value {merge} (steps {orb[a][merge]} from a, {orb[b][merge]} from b)" if merge else "no merge before 1"
        if cp >= 3 or merge and orb[b][merge] <= 30:
            print(f"   {a} ~ {b}: common word prefix {cp}, v2(diff) {v2(b - a)}; {rel}")
