"""On-orbit multiplicity with the barrier shift handled exactly (Haar model, finite N).
E_on(c,N) = (1/p_N) sum_{t=1}^{N-1} sum_S f_t(S) min(1, 2^{S - t alpha}) Psi(t,S),
f_t(S) = Geom(2) mass of confined length-t prefixes with sum S;  Psi(t,S) = probability that the
common future increments Phi_u satisfy Phi_u <= min(K_{t+u} - S, K_u) for u <= N-t (x and y = T^t x)
and Phi_u <= K_u for N-t < u <= N (y only).  For c = 0, min = K_u and E_on = sum_t W_0(t)/3^t."""
import sys
from math import floor, log2
c, N = int(sys.argv[1]), int(sys.argv[2])
A = log2(3)
def K(j):
    s = floor(c + j * A)
    while (1 << (s - c)) > 3 ** j: s -= 1
    return s
Ks = [0] + [K(j) for j in range(1, 2 * N + 2)]
def surv(bar):
    """P(Geom(2) partial sums Phi_u <= bar[u], u = 1..len-1), Phi_0 = 0."""
    cur = {0: 1.0}
    for u in range(1, len(bar)):
        top = bar[u]
        keys = sorted(cur)
        new, acc, idx = {}, 0.0, 0
        # Phi_u = Phi_{u-1} + d, d >= 1:  P(Phi_u = v) = sum_{w < v} cur[w] 2^-(v-w)
        run = 0.0
        prev = None
        lo = keys[0] + 1
        for v in range(lo, top + 1):
            # run(v) = sum_{w<v} cur[w] 2^{-(v-w)} = (run(v-1) + cur.get(v-1,0)) / 2
            run = (run + cur.get(v - 1, 0.0)) / 2
            if run > 1e-300: new[v] = run
        cur = new
        if not cur: return 0.0
    return sum(cur.values())
# forward confined prefix masses f_t(S)
f = [{0: 1.0}]
for t in range(1, N + 1):
    prev, cur = f[-1], {}
    for v in range(t, Ks[t] + 1):
        cur[v] = sum(m * 2.0 ** -(v - w) for w, m in prev.items() if w < v)
    f.append(cur)
pN = sum(f[N].values())
tot = 0.0
for t in range(1, N):
    for S, m in f[t].items():
        w = m * min(1.0, 2.0 ** (S - t * A))
        if w < 1e-14 * pN: continue
        bar = [0] + [min(Ks[t + u] - S, Ks[u]) if u <= N - t else Ks[u] for u in range(1, N + 1)]
        tot += w * surv(bar)
print(f"c={c} N={N}: E_on = {tot / pN:.4f}   (naive sum_t W_c(t)/3^t would ignore the barrier shift)")
