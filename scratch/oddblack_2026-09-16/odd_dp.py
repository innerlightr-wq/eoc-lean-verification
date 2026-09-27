"""Odd-cell black count N_odd under the confined law: exact distribution, moments, tilted pressure, and the
predictable black probabilities (P* version Q_r and exact bridge version beta_r).

Setting (identical to gb_dp.py / Lean `goodPair_of_white_step`): J = 2R, sg = floor(J alpha), t = J // 6,
m = sg + t + 1, top[i] = min(floor(i alpha), sg).  Confined law = uniform on compositions with S_i <= top[i],
S_J = sg.  Odd cell of pair block r: (m - S_{2r+1}, 2r+2);  black iff 54 |y| < 3^b  (y = centered 2^{-a} xi mod 3^b,
xi = 1 for the true environment), i.e. iff the three leading balanced-ternary digits of y mod 3^b vanish.
  N_odd = #{r < R : odd cell of block r black}.
  Q_r(S)    = sum_{d>=1} p q^{d-1} black(m - S - d, 2r+2)                (P* one-step predictable probability)
  beta_r(S) = sum_{x} G_{2r+1}(x)/G_{2r}(S) black(m - x, 2r+2)           (exact bridge predictable probability)
Outputs: exact mean/variance (big-int moment DP), exact upper tails (count DP with lumped top bin),
Chernoff/pressure (1/J) log2 E[s^N_odd], the distribution of Q and beta over the path marginal, high-Q occupation,
tilted pressures of A_Q = sum_r Q_r / R and A_beta = sum_r beta_r / R, strip profile, Q autocovariances, and
the conditional memory ratio E[Q_{r+l} | odd cell r black] / E[Q_{r+l}].
usage: python3 odd_dp.py J [env=true|random|file:PATH] [tails]"""
import math, sys, random

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); env = sys.argv[2] if len(sys.argv) > 2 else "true"
DO_TAILS = "tails" in sys.argv[3:]
assert J % 2 == 0
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
DMAX = 60
MOD = 3 ** (J + 2)
if env == "true": xi = 1
elif env == "random":
    random.seed(7000 + J); xi = random.randrange(1, MOD)
    while xi % 3 == 0: xi = random.randrange(1, MOD)
elif env.startswith("file:"): xi = int(open(env[5:]).read().split()[0])
else: raise SystemExit("bad env")

def row_black(b, x_lo, x_hi):
    """black flags for cells (m - x, b), x in [x_lo, x_hi]  (a = m - x decreasing as x increases)."""
    qb = 3 ** b; rr = xi * pow(2, -(m - x_lo), qb) % qb; out = {}
    for x in range(x_lo, x_hi + 1):
        y = rr if rr <= qb // 2 else rr - qb
        out[x] = 54 * abs(y) < qb
        rr = rr * 2 % qb
    return out

# odd-cell rows b = 2r+2, x from 2r+1 to top[2r] + DMAX (unconfined continuation for Q)
blk = [row_black(2 * r + 2, 2 * r + 1, top[2 * r] + DMAX) for r in range(R)]

# ---- exact word-level forward/backward counts
F = [None] * (J + 1); G = [None] * (J + 1)
F[0] = {0: 1}
for i in range(J):
    acc = 0; nxt = {}; prev = F[i]
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += prev.get(S2 - 1, 0)
        if acc: nxt[S2] = acc
    F[i + 1] = nxt
G[J] = {sg: 1}
for i in range(J - 1, -1, -1):
    acc = 0; cur = {}; nx = G[i + 1]
    for S in range(top[i + 1] - 1, i - 1, -1):
        acc += nx.get(S + 1, 0)
        if acc and S <= top[i]: cur[S] = acc
    G[i] = cur
Z = F[J][sg]; assert Z == G[0][0]
LZ = Z.bit_length()
def fl(n):             # big int / Z as float
    if n == 0: return 0.0
    sh = LZ - 60
    return (n >> sh) / (Z >> sh) if sh > 0 else n / Z
pi = lambda i: {S: fl(F[i][S] * G[i][S]) for S in F[i] if S in G[i]}
print(f"J={J} env={env} sg={sg} t={t} m={m}: #confined words = 2^{math.log2(Z):.2f}; pair blocks R = {R}")

# ---- (1) exact mean and variance via moment DP (big ints), black weight at odd times i = 2r+1
M0 = {0: 1}; M1 = {0: 0}; M2 = {0: 0}
for i in range(J):
    n0, n1, n2 = {}, {}, {}; a0 = a1 = a2 = 0
    for S2 in range(i + 1, top[i + 1] + 1):
        a0 += M0.get(S2 - 1, 0); a1 += M1.get(S2 - 1, 0); a2 += M2.get(S2 - 1, 0)
        if a0 == 0: continue
        if (i + 1) % 2 == 1 and blk[i // 2].get(S2, False):   # time i+1 = 2r+1 odd, cell of block r = i//2
            n0[S2] = a0; n1[S2] = a1 + a0; n2[S2] = a2 + 2 * a1 + a0
        else:
            n0[S2] = a0; n1[S2] = a1; n2[S2] = a2
    M0, M1, M2 = n0, n1, n2
assert M0[sg] == Z
mean = fl(M1[sg]); var = fl(M2[sg]) - mean ** 2
print(f"(1) E[N_odd] = {mean:.4f} = {mean / R:.5f} R;  Var = {var:.4f} (Var/R = {var / R:.5f})")

# ---- (2) exact upper tails via count DP (bins 0..K-1 exact, bin K = lumped >= K)
QS = (0.04, 0.05, 0.06, 0.075, 0.10)
if DO_TAILS:
    K = math.ceil(max(QS) * R)
    V = {0: [1] + [0] * K}
    for i in range(J):
        nv = {}; acc = [0] * (K + 1)
        for S2 in range(i + 1, top[i + 1] + 1):
            src = V.get(S2 - 1)
            if src is not None:
                for k in range(K + 1):
                    if src[k]: acc[k] += src[k]
            if not any(acc): continue
            if (i + 1) % 2 == 1 and blk[i // 2].get(S2, False):
                vec = [0] + acc[:K]; vec[K] += acc[K]
            else:
                vec = acc[:]
            nv[S2] = vec
        V = nv
    dist = V[sg]; assert sum(dist) == Z
    out = []
    for qq in QS:
        k = math.ceil(qq * R); c = sum(dist[k:])
        out.append(f"q={qq}: " + ("0" if c == 0 else f"2^-{math.log2(Z) - math.log2(c):.2f} (rate {(math.log2(Z) - math.log2(c)) / J:.4f})"))
    print("(2) exact P(N_odd >= qR): " + "; ".join(out))

# ---- float DP helper: E_conf[prod_i w_i(S_i)] with per-time multiplicative weights, log2 result
def tilted(weight):     # weight(i, S) -> factor applied at time i (after the step into S), i = 1..J
    v = {0: 1.0}; lg = 0.0
    for i in range(J):
        acc = 0.0; nv = {}
        for S2 in range(i + 1, top[i + 1] + 1):
            acc += v.get(S2 - 1, 0.0)
            if acc: nv[S2] = acc * weight(i + 1, S2)
        mx = max(nv.values()); lg += math.log2(mx)
        v = {k: x / mx for k, x in nv.items()}
    return lg + math.log2(v[sg]) - math.log2(Z)

def chernoff_rates(logmgf, qs, params, sign=+1):
    """P(X >= qR) <= s^{-qR} E[s^X]:  rate = max over params of (qR log2 s - log2 E s^X)/J."""
    res = []
    for qq in qs:
        best = max((qq * R * math.log2(s) - logmgf[s]) / J for s in params)
        res.append(best)
    return res

SS = (1.25, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0)
lmg = {s: tilted(lambda i, S, s=s: s if (i % 2 == 1 and blk[(i - 1) // 2].get(S, False)) else 1.0) for s in SS}
print("(3) pressure (1/J) log2 E[s^N_odd]: " + "  ".join(f"s={s}: {lmg[s] / J:.5f}" for s in SS))
print("    Chernoff rate bound for P(N_odd >= qR): " + "  ".join(f"q={qq}: {c:.4f}" for qq, c in zip(QS, chernoff_rates(lmg, QS, SS))))

# ---- (4) predictable probabilities
Qr = []; Br = []
for r in range(R):
    row = blk[r]; qd = {}; bd = {}
    for S in G[2 * r]:
        qd[S] = sum(p * q ** (d - 1) for d in range(1, DMAX + 1) if row.get(S + d, False))
        num = sum(G[2 * r + 1][x] for x in range(S + 1, top[2 * r + 1] + 1) if x in G[2 * r + 1] and row.get(x, False))
        bd[S] = fl(num * Z // G[2 * r][S]) if num else 0.0     # = num / G_{2r}(S)
    Qr.append(qd); Br.append(bd)
# check exact identity E_conf[sum beta_r] = E_conf[N_odd]
EQ = 0.0; EB = 0.0; profQ = []; profB = []; allQ = []; allB = []
for r in range(R):
    w = pi(2 * r); eq = sum(w[S] * Qr[r][S] for S in w); eb = sum(w[S] * Br[r][S] for S in w)
    EQ += eq; EB += eb; profQ.append(eq); profB.append(eb)
    for S in w:
        allQ.append((Qr[r][S], w[S])); allB.append((Br[r][S], w[S]))
print(f"(4) E[sum Q_r]/R = {EQ / R:.5f};  E[sum beta_r]/R = {EB / R:.5f}  (identity: = E[N_odd]/R = {mean / R:.5f})")
def wq(lst, qs):
    lst = sorted(lst); tot = sum(w for _, w in lst); out = []; acc = 0.0; k = 0
    for qq in qs:
        while k < len(lst) and acc + lst[k][1] < qq * tot: acc += lst[k][1]; k += 1
        out.append(lst[min(k, len(lst) - 1)][0])
    return out
for name, lst, tab in (("Q", allQ, Qr), ("beta", allB, Br)):
    med, p90, p99, p999 = wq(lst, (0.5, 0.9, 0.99, 0.999))
    sup_all = max(max(d.values()) for d in tab)
    sup_typ = max(v for v, w in lst if w > 1e-12)
    print(f"    {name}: path-weighted median {med:.4f}, 90% {p90:.4f}, 99% {p99:.4f}, 99.9% {p999:.4f};"
          f" sup over states with mass>1e-12 {sup_typ:.4f}; sup over all confined states {sup_all:.4f}")
    occ = []
    for q0 in (0.1, 0.2, 0.5, 0.8, 0.95):
        occ.append(f"q0={q0}: {sum(w for v, w in lst if v >= q0) / R:.5f}")
    print(f"    E #{{r: {name}_r >= q0}}/R: " + "  ".join(occ))

# ---- (5) strip profile
def seg(prof, a, b): a, b = int(a * R), int(b * R); return sum(prof[a:b]) / max(b - a, 1)
print("(5) strip mean of Q_r by tenths of r: " + " ".join(f"{seg(profQ, k / 10, (k + 1) / 10):.4f}" for k in range(10)))
print("    strip mean of beta_r by tenths:     " + " ".join(f"{seg(profB, k / 10, (k + 1) / 10):.4f}" for k in range(10)))
for eps in (0.05, 0.1, 0.2):
    print(f"    bulk [{eps},{1 - eps}]R: mean Q {seg(profQ, eps, 1 - eps):.5f}, mean beta {seg(profB, eps, 1 - eps):.5f}; "
          f"endpoint blocks carry sum beta = {(sum(profB[:int(eps * R)]) + sum(profB[int((1 - eps) * R):])) / R:.5f} R")

# ---- (6) tilted pressure of A_Q, A_beta (state-only Feynman-Kac: weight e^{tau Q_r(S)} at even times 2r)
TT = (0.5, 1.0, 2.0, 3.0, 5.0, 8.0)
for name, tab in (("A_Q", Qr), ("A_beta", Br)):
    lm = {tau: tilted(lambda i, S, tau=tau: math.exp(tau * tab[i // 2][S]) if (i % 2 == 0 and i // 2 < R) else 1.0)
          for tau in TT}
    # weight applied at time i = 2r (r >= 1); r = 0 state S_0 = 0 contributes e^{tau Q_0(0)} deterministic
    c0 = {tau: tau * tab[0][0] / math.log(2) for tau in TT}
    lm = {tau: lm[tau] + c0[tau] for tau in TT}
    print(f"(6) pressure (1/J) log2 E[exp(tau sum {name[2:]}_r)]: " + "  ".join(f"tau={tau}: {lm[tau] / J:.5f}" for tau in TT))
    rates = []
    for qq in (0.05, 0.06, 0.075, 0.10):
        rates.append(max((qq * R * tau / math.log(2) - lm[tau]) / J for tau in TT))
    print(f"    Chernoff rate bound for P({name} >= q): " + "  ".join(f"q={qq}: {c:.4f}" for qq, c in zip((0.05, 0.06, 0.075, 0.10), rates)))

# ---- (7) autocovariance of Q_r along the bridge, bulk anchors; memory ratio after a black odd cell
def fvec(D):            # big-int dict -> (float dict scaled by 2^-e, e)
    e = max(v.bit_length() for v in D.values()) - 500
    return {k: float(v >> e) if e >= 0 else float(v << -e) for k, v in D.items()}, e
def propagate(vec, i0, i1):      # forward propagation of unnormalized path weights from time i0 to i1
    v = dict(vec)
    for i in range(i0, i1):
        acc = 0.0; nv = {}
        for S2 in range(i + 1, top[i + 1] + 1):
            acc += v.get(S2 - 1, 0.0)
            if acc: nv[S2] = acc
        v = nv
    return v
def expect(vec, eF, i1, f):
    Gf, eG = fvec(G[i1])
    tot = sum(vec[S] * Gf[S] * f(S) for S in vec if S in Gf)
    if tot == 0: return 0.0
    return 2.0 ** (math.log2(tot) + eF + eG - math.log2(Z) if LZ < 1000 else math.log2(tot) + eF + eG - (LZ - 60) - math.log2(Z >> (LZ - 60)))
LAGS = (1, 2, 5, 10, 20)
anchors = list(range(int(0.2 * R), int(0.8 * R) - 20, max(1, R // 40)))
cov = {l: 0.0 for l in LAGS}; mem = {l: [0.0, 0.0] for l in (1, 2, 5, 10)}
for r in anchors:
    i0 = 2 * r
    base, eF = fvec({S: F[i0][S] for S in F[i0] if S in G[i0]})
    vq = {S: base[S] * Qr[r][S] for S in base}
    vb1 = propagate(base, i0, i0 + 1); vb1 = {S: x for S, x in vb1.items() if blk[r].get(S, False)}
    pb = expect(vb1, eF, i0 + 1, lambda S: 1.0) if vb1 else 0.0
    for l in LAGS:
        if r + l >= R: continue
        i1 = 2 * (r + l)
        v = propagate(vq, i0, i1)
        e_xy = expect(v, eF, i1, lambda S: Qr[r + l][S])
        cov[l] += e_xy - profQ[r] * profQ[r + l]
        if l in mem and pb > 0:
            v2 = propagate(vb1, i0 + 1, i1)
            mem[l][0] += expect(v2, eF, i1, lambda S: Qr[r + l][S])
            mem[l][1] += pb * profQ[r + l]
print(f"(7) sum over {len(anchors)} bulk anchors of Cov(Q_r, Q_(r+l)): " + "  ".join(f"l={l}: {cov[l]:+.4e}" for l in LAGS)
      + f"   (anchor-sum of Var-scale E Q_r(1-Q_r) <= {sum(profQ[r] for r in anchors):.4e})")
print("    memory ratio E[Q_(r+l) | odd cell r black] / E[Q_(r+l)]: " + "  ".join(f"l={l}: {mem[l][0] / mem[l][1]:.3f}" for l in mem if mem[l][1]))
