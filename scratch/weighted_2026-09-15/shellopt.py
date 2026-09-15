"""Parts XXIII-XXV: shellwise optimization of the A=0.7 chain at exact finite K (c=U=0).
For every fresh prefix shell sigma (<= s_{j0} < K) and word shell s in [K, s_N]:
  Haar(s,sigma) = |P_sigma| |V_{sigma,s}| 2^{K-1-s}
  trivial constant  c_triv = 2^{s+1-K}
  Fourier constant  c_F(gamma) = 1 + eps,  eps^2 = (1+(sigma+1)/2) * 2^t * [#dyadic shells ~ (sigma+2)] * 2^t A / |V|,
                    A = 2^{-2 gamma j0} (assumed avg |Phi/P|^2 on every dyadic frequency shell)
Weighted constant C(gamma) = sum_{s,sigma} min(c_triv, c_F) Haar / sum Haar.  Report gamma* with C(gamma*) = 2 (and =K),
the Haar fraction handled by Fourier, and the hardest shell."""
import math
al = math.log2(3)
def counts_prefix(c, J):
    b = [math.floor(c + j * al) for j in range(J + 2)]
    cur = {0: 1.0}
    for i in range(J):
        new = {}
        for S, v in cur.items():
            for d in range(1, b[i + 1] - S + 1): new[S + d] = new.get(S + d, 0.0) + v
        cur = new
    return cur, b
def counts_suffix(c, J, sig, L, tmax):
    b = [math.floor(c + j * al) for j in range(J + L + 2)]
    cur = {0: 1.0}
    for i in range(L):
        new = {}
        for S, v in cur.items():
            for d in range(1, tmax - S + 1):
                if sig + S + d <= b[J + i + 1]: new[S + d] = new.get(S + d, 0.0) + v
        cur = new
    return cur
def run(K, A=0.7, c=0):
    J = math.floor((K - 1 - c) / al); N = math.floor(A * K)
    P, b = counts_prefix(c, J); sN = math.floor(c + N * al); L = N - J
    rows = []
    for sig, Pc in P.items():
        if sig >= K or Pc == 0: continue
        V = counts_suffix(c, J, sig, L, sN - sig)
        for s in range(K, sN + 1):
            t = s - sig; Vc = V.get(t, 0.0)
            if Vc == 0: continue
            H = Pc * Vc * 2.0 ** (K - 1 - s)
            rows.append((sig, s, t, Pc, Vc, H))
    Htot = sum(r[5] for r in rows)
    def C(gamma):
        tot = 0.0; fmass = 0.0
        for sig, s, t, Pc, Vc, H in rows:
            ct = 2.0 ** (s + 1 - K)
            eps = math.sqrt((1 + (sig + 1) / 2) * (sig + 2) * 4.0 ** t * 2.0 ** (-2 * gamma * J) / Vc)
            cf = 1 + eps
            if cf < ct: fmass += H
            tot += min(ct, cf) * H
        return tot / Htot, fmass / Htot
    def solve(target):
        lo, hi = 0.0, 2.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if C(mid)[0] <= target: hi = mid
            else: lo = mid
        return hi
    g2 = solve(2.0); gK = solve(float(K))
    # hardest shell at gamma*: the (sigma,s) whose Fourier constant is largest among those where Fourier is used
    worst = None
    for sig, s, t, Pc, Vc, H in rows:
        eps = math.sqrt((1 + (sig + 1) / 2) * (sig + 2) * 4.0 ** t * 2.0 ** (-2 * g2 * J) / Vc)
        if 1 + eps < 2.0 ** (s + 1 - K):
            contrib = eps * H / Htot
            if worst is None or contrib > worst[0]: worst = (contrib, sig, s, t)
    Cg, fm = C(g2)
    # Haar-weighted mean of the naive per-pair requirement (2t - log2|V|)/(2J)
    naive = sum(H * (2 * t - math.log2(Vc)) / (2 * J) for sig, s, t, Pc, Vc, H in rows) / Htot
    print(f"K={K}: j0={J} N={N} s_N={sN}  pairs={len(rows)}  gamma*(C=2)={g2:.4f}  gamma*(C=K)={gK:.4f}  Fourier-handled Haar fraction={fm:.4f}"
          f"  Haar-mean naive req {naive:.4f}  hardest shell (sigma,s,t)={worst[1:] if worst else None}")
for K in (100, 200, 400, 800):
    run(K)
