"""Equidistribution horizon.  For X = 2^K (odd seeds 1 <= mu < X, count 2^(K-1)):
  S_X(N,c) = #{mu < X : exit > N}  (exact, complete sieve histograms),   M_X(N,c) = 2^(K-1) p_N(c),
  Q = S/M,  E = Q - 1.
Fresh-bit threshold: every confined word has S_N + 1 <= K  <=>  s_N(c) + 1 <= K  => Q = 1 exactly.
Noise model (seeds as clustered Poisson): sd(Q) = sqrt(D / M), D = Palm cluster size (c=0: 5.9,
c=1: 12.2, c=2: 22.3) for prefix intervals [0, X).
Horizons for tolerance eps:
  A_raw   = sup{N/K : |E| <= eps}                                   (literal definition; noisy)
  A_first = (first N with |E| > eps at 3 consecutive depths) - 1, over K  (stable exit)
  A_noise = N/K where 2 sd(Q) = eps                                  (pure-noise prediction)
usage: python3 horizon.py c histfile KMIN KMAX"""
import json, re, sys
from math import log2, sqrt
c, hf, KMIN, KMAX = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
D = {0: 5.9, 1: 12.2, 2: 22.3}[c]
T = json.load(open("pn_table.json"))[str(c)]
lp = {r["N"]: r["lP"] for r in T}
sN = {r["N"]: r["sN"] for r in T}
H = {}
for line in open(hf):
    m = re.match(r"HIST k=(\d+):(.*)", line)
    if m:
        H[int(m.group(1))] = {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", m.group(2))}
def S_of(K):
    cnt = {}
    for k in range(K):
        for e, v in H.get(k, {}).items():
            cnt[e] = cnt.get(e, 0) + v
    emax = max(cnt)
    S, acc = {}, 0
    for e in range(emax + 1, 0, -1):
        acc += cnt.get(e, 0)
        S[e - 1] = acc
    return S
eps_list = [0.001, 0.003, 0.01, 0.03, 0.05]
rows = []
print(f"c={c}: horizon table (A = N / log2 X)")
print("  K  N_fresh  A_fresh | " + "  ".join(f"eps={e}: raw/first/noise" for e in eps_list))
allQ = {}
for K in range(KMIN, KMAX + 1):
    S = S_of(K)
    Nf = max(N for N in sN if sN[N] + 1 <= K)
    Q = {}
    for N in range(1, 1400):
        M = 2.0 ** (K - 1 + lp[N])
        if M < 0.5 or N not in S:
            break
        Q[N] = (S.get(N, 0) / M, M)
    allQ[K] = Q
    out = []
    for eps in eps_list:
        ok = [N for N, (q, M) in Q.items() if abs(q - 1) <= eps]
        raw = max(ok) / K if ok else 0
        first = None
        Ns = sorted(Q)
        for i, N in enumerate(Ns[:-2]):
            if all(abs(Q[Ns[i + j]][0] - 1) > eps for j in range(3)):
                first = (N - 1) / K
                break
        if first is None:
            first = Ns[-1] / K
        noise = next((N for N in Ns if 2 * sqrt(D / Q[N][1]) > eps), Ns[-1]) / K
        out.append(f"{raw:5.2f}/{first:5.2f}/{noise:5.2f}")
    print(f" {K:2d}  {Nf:5d}   {Nf / K:5.3f}  | " + "   ".join(out))
json.dump({str(K): {str(N): v for N, v in Q.items()} for K, Q in allQ.items()}, open(f"Q_c{c}.json", "w"))
