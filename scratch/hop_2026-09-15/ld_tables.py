"""Parts VII-XI: large-digit probabilities, binary-KL rates, confinement comparison, exact large-digit statistics.

Tilted law P*(d = k) = (1/alpha) r^{k-1}, r = 1 - 1/alpha, alpha = log2 3.
Confined law (as in triangle_2026-09-15/triangles.py, mode paths): S_0 = 0, S_{i+1} in (S_i, min(floor((i+1)alpha), sg)],
S_n = sg = floor(n alpha); uniform over such compositions = P* conditioned on C_n (P* weight depends only on the sum).
Shell law: P* conditioned on S_n = sg only.  N = N_{>=6}(n) = #{i : d_i >= 6}.
Exact float DP over (S, N) with the geometric kernel (running sums)."""
import math

AL = math.log2(3); r = 1 - 1 / AL; LN2 = math.log(2)
print(f"alpha = {AL:.6f}, r = 1 - 1/alpha = {r:.6f}")
print("\nPart VII: p_{d0} = P*(d >= d0) = r^{d0-1}")
p = {d0: r ** (d0 - 1) for d0 in range(2, 11)}
for d0 in (5, 6, 7, 8):
    print(f"  d0={d0}: p = {p[d0]:.6f}   (1/p = {1 / p[d0]:.1f})")


def kl2(q, pp):  # binary relative entropy in bits
    t = 0.0
    if q > 0: t += q * math.log2(q / pp)
    if q < 1: t += (1 - q) * math.log2((1 - q) / (1 - pp))
    return t


print("\nPart VIII: I(q || p_{d0}) in bits (Chernoff: P*(N_{>=d0}(n) >= qn) <= 2^{-n I}, q > p)")
qs = (0.005, 0.01, 0.02, 0.05, 0.1, 0.2)
print("   d0 \\ q " + "".join(f"{q:>9}" for q in qs))
for d0 in (5, 6, 7, 8):
    print(f"   {d0:4d}    " + "".join(f"{kl2(q, p[d0]):9.4f}" if q > p[d0] else f"{'  (q<p)':>9}" for q in qs))

w = lambda d: (1 / AL) * r ** (d - 1)


def dp(n, confined, d0=6, K=None):
    K = K or max(20, n // 3)
    sg = math.floor(n * AL)
    top = [min(math.floor(i * AL), sg) if confined else sg for i in range(n + 1)]
    ws = [0.0] + [w(d) for d in range(1, d0)]; wd0 = w(d0)
    cur = [[0.0] * (K + 1) for _ in range(sg + 1)]; cur[0][0] = 1.0
    for i in range(n):
        new = [[0.0] * (K + 1) for _ in range(sg + 1)]; T = [0.0] * (K + 1)
        for S2 in range(1, top[i + 1] + 1):
            src = cur[S2 - d0] if S2 - d0 >= 0 else None
            T = [r * x + (src[c] * wd0 if src is not None else 0.0) for c, x in enumerate(T)]
            row = new[S2]
            for dd in range(1, d0):
                if S2 - dd >= 0:
                    sr = cur[S2 - dd]; wv = ws[dd]
                    for c in range(K + 1): row[c] += sr[c] * wv
            for c in range(K): row[c + 1] += T[c]
            row[K] += T[K]
        cur = new
    return cur[sg]


print("\nPart IX: P*(C_n) (confined + endpoint sg) and n^{3/2} P*(C_n); P*(S_n = sg) and n^{1/2} P*(S_n = sg)")
res = {}
for n in (60, 100, 150, 200, 300):
    dc = dp(n, True); ds = dp(n, False); res[n] = (dc, ds)
    Pc, Ps = sum(dc), sum(ds)
    print(f"  n={n:4d}: P*(C_n) = {Pc:.4e}, n^1.5 P = {Pc * n ** 1.5:.4f} | P*(S_n=sg) = {Ps:.4e}, n^0.5 P = {Ps * n ** 0.5:.4f}")

print("\nPart XI: N_{>=6}(n)/n — mean and tails under confined / shell-only / iid P*")
p6 = p[6]
for n in (60, 100, 150, 200, 300):
    dc, ds = res[n]
    rows = []
    for name, dist0 in (("confined", dc), ("shell", ds)):
        tot = sum(dist0); dist = [x / tot for x in dist0]
        mean = sum(c * x for c, x in enumerate(dist))
        tails = {q: sum(x for c, x in enumerate(dist) if c >= q * n) for q in (0.02, 0.05, 0.1)}
        rows.append((name, mean / n, tails))
    # iid binomial
    from math import comb
    bt = {q: sum(comb(n, k) * p6 ** k * (1 - p6) ** (n - k) for k in range(math.ceil(q * n), n + 1)) for q in (0.02, 0.05, 0.1)}
    rows.append(("iid P*", p6, bt))
    for name, m, t in rows:
        print(f"  n={n:4d} {name:9s} mean N/n = {m:.5f}   P(N/n>=0.02) = {t[0.02]:.3e}  P(N/n>=0.05) = {t[0.05]:.3e}"
              f"  P(N/n>=0.1) = {t[0.1]:.3e}")
    for q in (0.05, 0.1):
        tot = sum(dc); tail = sum(x for c, x in enumerate(dc) if c >= q * n) / tot
        print(f"        confined rate -log2 P(N/n>={q})/n = {-math.log2(max(tail, 1e-300)) / n:.4f}"
              f"   vs I(q||p6) = {kl2(q, p6):.4f};  poly-transfer bound ratio P_conf/P* <= 1/P*(C_n) = {1 / tot:.1f}")
