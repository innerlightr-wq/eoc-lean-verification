"""Part III: optimize the split depth j0 = beta*K at fixed A (top word shell, top prefix shell).
Asymptotic bits per K: t = alpha(A-beta), log2|P| = h*beta, log2|V| = H2(1/alpha)*t,
required -log2 delta_req = t - log2|V| = (1-H2)t,   random -log2 delta = log2|P| - t,
margin = random - required (bits/K); smoothed-route pointwise rate needed = 0.525 t/(beta) per step... computed exactly.
Also an exact instance at K=100 (c=0) with DP counts."""
import math
al = math.log2(3); I0 = 0.0793186; h = al - I0
H2 = lambda p: -p*math.log2(p) - (1-p)*math.log2(1-p)
hv = H2(1/al)
A = 0.7
print(f"A={A}: alpha A - 1 = {al*A-1:.4f};  H2(1/alpha) = {hv:.6f};  h = {h:.5f}")
print(" beta=j0/K   t/K     log2|P|/K  req(-log2 d)/K  rand(-log2 d)/K  margin/K  need rate(bits/step, avg)  need rate(every h)")
for beta in [0.37, 0.40, 0.45, 0.50, 0.55, 0.60, 1/al]:
    t = al*(A-beta); P = h*beta; req = (1-hv)*t; rnd = P - t
    rate = (1 + (1-hv)) / 2 * t / beta   # |Phi/P|^2 * 2^t <= 2^{-(1-hv)t}
    every = (1-hv)/2 * t / beta
    print(f"  {beta:.4f}   {t:.4f}   {P:.4f}      {req:.5f}         {rnd:.4f}         {rnd-req:+.4f}     {rate:.4f}                    {every:.5f}")
# exact instance
def counts(c, J, sig):
    b = [math.floor(c + j*al) for j in range(400)]
    pre = {0: 1}
    for i in range(J):
        new = {}
        for S, v in pre.items():
            for d in range(1, b[i+1]-S+1): new[S+d] = new.get(S+d, 0) + v
        pre = new
    return pre.get(sig, 0), b
def vcount(c, j0, sig, L, t):
    b = [math.floor(c + j*al) for j in range(400)]
    cur = {0: 1}
    for i in range(L):
        new = {}
        for S, v in cur.items():
            for d in range(1, t+1):
                if sig + S + d <= b[j0+i+1]: new[S+d] = new.get(S+d, 0) + v
        cur = new
    return cur.get(t, 0)
for K in (100, 200, 400):
    c = 0; N = math.floor(A*K); b = [math.floor(c + j*al) for j in range(N+2)]
    j0 = max(j for j in range(1, N) if b[j] < K)
    sig = b[j0]; sN = b[N]; t = sN - sig; n = sN + 1 - K
    P, _ = counts(c, j0, sig); V = vcount(c, j0, sig, N-j0, t)
    req = V / 2**t; rnd = 2**t / P
    print(f"K={K}: N={N} j0={j0} sigma={sig} s_N={sN} t={t} n={n}: log2|P|={math.log2(P):.1f} |V|={V} (log2 {math.log2(V):.2f})"
          f"  delta_req=(C-1)^2*{req:.3e}  delta_random={rnd:.3e}  margin bits={math.log2(req/rnd):.1f}")
