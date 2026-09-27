"""Exact DP for the black indicator along critical confined paths (Parts XIX-XXII, XXIX-XXXIII, XL).

Setting (as in hop_2026-09-15/hops.py): J steps, sg = floor(J alpha), t = J // 6, m = sg + t + 1, eta = 1/54.
State (i, S), i = 0..J-1: cell (m - S, i + 1); B(i,S) = 1{|y(m-S, i+1)| < eta 3^{i+1}} (exact integers).
Confined law: uniform over compositions with S_0 = 0, S_i <= floor(i alpha), S_J = sg (= P* conditioned on C_J).
Shell law: uniform over all compositions of sg into J parts (= P* conditioned on S_J = sg).
Outputs:
  (a) mu_i = P(B_i = 1) along i, strip averages;                         [exact, floats]
  (b) Cov(B_i, B_{i+s}), s = 1,2,5,10,20,50, averaged over anchors;       [exact, floats]
  (c) Var(sum_i B_i) / J;                                                  [exact, floats]
  (d) P(W_J < delta J), W = #white, exact big-integer counts; rate -log2 P / J   [exact]
  (e) one-step black probability beta(i,S) = sum_d P*(d) B(i+1,S+d) (tilted kernel) and its sup over
      black / white states; confined-kernel version;
  (f) k-step all-black probability v_k(i,S) under the tilted kernel; sup over states (Doeblin test).
usage: python3 wc_dp.py J [law=confined|shell]"""
import math, sys
from fractions import Fraction

AL = math.log2(3); r = 1 - 1 / AL
w = lambda d: (1 / AL) * r ** (d - 1)
J = int(sys.argv[1]); law = sys.argv[2] if len(sys.argv) > 2 else "confined"
light = len(sys.argv) > 3 and sys.argv[3] == "light"     # light: only (a), (c), worst case
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) if law == "confined" else sg for i in range(J + 1)]
lo = [i for i in range(J + 1)]                      # S_i >= i (digits >= 1)
# black table: blk[i][S] for lo[i] <= S <= top[i]
blk = []
for i in range(J):
    b = i + 1; q = 3 ** b; row = {}
    a0 = m - lo[i]; rr = pow(2, -a0, q)              # 2^{-a} mod 3^b at S = lo[i]
    for S in range(lo[i], top[i] + 1):
        y = rr if rr <= q // 2 else rr - q
        row[S] = 1 if 54 * abs(y) < q else 0
        rr = rr * 2 % q                              # a -> a - 1
    blk.append(row)

# ---- exact counting forward/backward (big ints): number of admissible paths through (i, S)
F = [dict() for _ in range(J + 1)]; F[0][0] = 1
for i in range(J):
    acc = 0; prev = F[i]
    for S2 in range(lo[i + 1], top[i + 1] + 1):
        acc += prev.get(S2 - 1, 0)                   # prefix sum over S < S2
        if acc: F[i + 1][S2] = acc
G = [dict() for _ in range(J + 1)]; G[J][sg] = 1
for i in range(J - 1, -1, -1):
    acc = 0; nxt = G[i + 1]
    for S in range(top[i + 1] - 1, lo[i] - 1, -1):
        acc += nxt.get(S + 1, 0)                     # suffix sum over S < S2 <= top[i+1]
        if acc and S <= top[i]: G[i][S] = acc
Z = F[J].get(sg, 0)
assert Z == G[0][0] and Z > 0
print(f"J={J} law={law} sg={sg} t={t} m={m}: #paths = 2^{math.log2(Z):.2f}")

def prob(num):  # exact big-int ratio -> float (handles huge ints)
    return float(Fraction(num, Z))

# (a) mu_i
mu = []
for i in range(J):
    s = sum(F[i][S] * G[i][S] for S in F[i] if S in G[i] and blk[i].get(S, 0))
    mu.append(prob(s))
thirds = [sum(mu[k * J // 3:(k + 1) * J // 3]) / (J // 3) for k in range(3)]
print(f"(a) mean mu_i = {sum(mu) / J:.5f} (2 eta = {2 / 54:.5f}); by thirds {[round(x, 5) for x in thirds]}; "
      f"max mu_i = {max(mu):.4f} at i = {mu.index(max(mu))}; min = {min(mu):.4f}")

if light:
    pass
# (b) two-point covariances: P(B_i=1, B_{i+s}=1) via exact propagation of counts
def joint(i, s):
    vec = {S: F[i][S] for S in F[i] if blk[i].get(S, 0) and S in G[i]}
    for k in range(s):
        new = {}; acc = 0; ii = i + k
        for S2 in range(lo[ii + 1], top[ii + 1] + 1):
            acc += vec.get(S2 - 1, 0)
            if acc: new[S2] = acc
        vec = new
    return prob(sum(c * G[i + s][S] for S, c in vec.items() if blk[i + s].get(S, 0) and S in G[i + s]))
bulk = range(J // 10, (9 * J) // 10)
covs = {}
if light: bulk = range(0)
for s_ in (1, 2, 5, 10, 20, 50):
    if s_ >= (8 * J) // 10: continue
    tot = 0.0
    for i in bulk:
        if i + s_ < J and mu[i] > 0 and mu[i + s_] > 0:
            tot += joint(i, s_) - mu[i] * mu[i + s_]
    covs[s_] = tot
ind = sum(x * (1 - x) for x in mu[J // 10:(9 * J) // 10])
if not light: print("(b) C(s) = sum over bulk anchors of Cov(B_i, B_{i+s}): " +
      "  ".join(f"s={s_}: {c:+.3e}" for s_, c in covs.items()) + f"   (bulk sum of mu_i(1-mu_i) = {ind:.3e})")

# (c) variance of N_B = sum_i B_i via moment DP (exact big ints: F0, F1 = sum N, F2 = sum N^2 over paths)
F0 = {0: 1}; F1 = {0: 0}; F2 = {0: 0}
for i in range(J):
    for S in list(F0):
        if blk[i].get(S, 0):
            F2[S] += 2 * F1[S] + F0[S]; F1[S] += F0[S]
    n0 = {}; n1 = {}; n2 = {}; a0 = a1 = a2 = 0
    for S2 in range(lo[i + 1], top[i + 1] + 1):
        a0 += F0.get(S2 - 1, 0); a1 += F1.get(S2 - 1, 0); a2 += F2.get(S2 - 1, 0)
        if a0: n0[S2] = a0; n1[S2] = a1; n2[S2] = a2
    F0, F1, F2 = n0, n1, n2
EN = Fraction(F1[sg], F0[sg]); EN2 = Fraction(F2[sg], F0[sg]); var = EN2 - EN * EN
print(f"(c) E[N_B] = {float(EN):.3f} ({float(EN)/J:.5f} J); Var(N_B) = {float(var):.3f}; Var/J = {float(var)/J:.4f}"
      f"  (independent benchmark sum mu_i(1-mu_i)/J = {sum(x*(1-x) for x in mu)/J:.4f})")

# (d) worst case and exact distribution of the black count N_B (W = J - N_B)
best = {0: 0}
for i in range(J):
    for S in best: best[S] += blk[i].get(S, 0)
    new = {}; run = -1
    for S2 in range(lo[i + 1], top[i + 1] + 1):
        v_ = best.get(S2 - 1)
        if v_ is not None and v_ > run: run = v_
        if run >= 0 and S2 in G[i + 1]: new[S2] = run
    best = new
BMAX = best[sg]
print(f"(d) worst case over ALL admissible paths: max #black = {BMAX} ({BMAX / J:.4f} J), i.e. W_J >= {J - BMAX} "
      f"({(J - BMAX) / J:.4f} J) deterministically")
if light:
    sys.exit(0)
K = BMAX + 1
cur = {0: [1] + [0] * K}
for i in range(J):
    for S in cur:
        if blk[i].get(S, 0):
            v_ = cur[S]; cur[S] = [0] + v_[:K - 1] + [v_[K - 1] + v_[K]]
    new = {}; acc = [0] * (K + 1)
    for S2 in range(lo[i + 1], top[i + 1] + 1):
        v_ = cur.get(S2 - 1)
        if v_: acc = [x + y for x, y in zip(acc, v_)]
        if S2 in G[i + 1] and any(acc): new[S2] = acc[:]
    cur = new
dist = cur[sg]; assert sum(dist) == Z and dist[K] == 0
out = []
for q in (0.05, 0.1, 0.15, 0.2, 0.3):
    kk = math.ceil(q * J)
    c = sum(dist[kk:])
    out.append(f"q={q}: " + ("0" if c == 0 else f"2^-{math.log2(Z) - math.log2(c):.1f} (rate {(math.log2(Z) - math.log2(c)) / J:.3f})"))
print("    P(N_B >= q J) exact: " + "; ".join(out))
print("    so P(W_J < delta J) = 0 exactly for every delta <= " + f"{(J - BMAX) / J:.4f}")

# (e) one-step black probability under the tilted kernel (confinement ignored) and the confined kernel
DMAX = 25                                           # P*(d >= 25) < 1e-10
def beta(i, S):
    return sum(w(d) * blk[i + 1].get(S + d, 0) for d in range(1, DMAX))
def beta_conf(i, S):
    num = den = 0.0
    for d in range(1, DMAX):
        S2 = S + d
        if S2 in G[i + 1]:
            wt = w(d) * float(Fraction(G[i + 1][S2], G[i + 1][max(G[i + 1], key=G[i + 1].get)]))
            den += wt; num += wt * blk[i + 1].get(S2, 0)
    return num / den if den else 0.0
sb = sw = 0.0; sbc = 0.0; arg_b = None
wsum = 0.0; mean_b = 0.0
for i in range(J - 1):
    for S in F[i]:
        if S not in G[i]: continue
        bt = beta(i, S)
        if blk[i].get(S, 0):
            if bt > sb: sb = bt; arg_b = (i, S)
        else:
            sw = max(sw, bt)
        pw = prob(F[i][S] * G[i][S]); wsum += pw; mean_b += pw * bt
print(f"(e) tilted one-step black prob: sup over black states {sb:.4f} (at {arg_b}), sup over white states {sw:.4f}; "
      f"path-averaged {mean_b / wsum:.4f}")
if arg_b:
    print(f"    confined-kernel value at that state: {beta_conf(*arg_b):.4f}")

# (f) k-step all-black probability under the tilted kernel: v_k(i,S) = sum_d w(d) B(i+1,S+d) v_{k-1}(i+1,S+d)
KMAX = 12
v = [dict() for _ in range(J)]                        # v[i][S] for current k
for i in range(J):
    for S in range(lo[i], top[i] + 1): v[i][S] = 1.0
sups = []
for k in range(1, KMAX + 1):
    nv = [dict() for _ in range(J)]
    for i in range(J - 1):
        for S in range(lo[i], top[i] + 1):
            nv[i][S] = sum(w(d) * blk[i + 1].get(S + d, 0) * v[i + 1].get(S + d, 0.0) for d in range(1, DMAX)
                           if S + d <= top[i + 1])
    v = nv
    best = 0.0; arg = None; relbest = 0.0
    for i in range(J - k):
        for S, val in v[i].items():
            if val > best: best = val; arg = (i, S)
            if S in F[i] and S in G[i] and prob(F[i][S] * G[i][S]) > 1e-6 and val > relbest: relbest = val
    sups.append((k, best, arg, relbest))
print("(f) sup_state P*(next k cells all black): " +
      "  ".join(f"k={k}: {bst:.3e}" for k, bst, arg, rb in sups))
print("    restricted to states with path mass > 1e-6: " + "  ".join(f"k={k}: {rb:.3e}" for k, bst, arg, rb in sups))
print(f"    Doeblin eps_k = 1 - sup = " + "  ".join(f"{1 - bst:.4f}" for k, bst, arg, rb in sups[:6]))
