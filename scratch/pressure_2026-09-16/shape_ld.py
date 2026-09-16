"""Shape-only good-block large deviations: exact generating function, pressure, Legendre rate, and the
RIGOROUS finite-J bound (cycle lemma + generating-function Chernoff + contact martingale), compared with the
exact DP tail probabilities of gb_dp.py (scratch/whitecount_2026-09-16/GB.txt).

Setting (J = 2R even, sg = floor(J alpha), top[i] = min(floor(i alpha), sg)):
  C_J   = compositions d_1..d_J >= 1 with S_J = sg and S_i <= top[i]  (the confined word set, uniform law);
  u_r   = d_{2r+1} + d_{2r+2} (pair sum), G'   = #{r : 3 <= u_r <= N0+1}          (uncapped shape count);
  G_sh  = #{r : 2 <= |B_r| <= N0}, |B_r| = min(S_{2r+2}-1, top[2r+1]) - S_{2r}   (gb_dp 'shape' count);
  K     = #{i <= J : S_i = top[i]}  (barrier contacts).
Lemmas (PROVED MATH, see REPORT.md):
  (L1) cycle lemma: |C_J| >= binom(sg-1, J-1) / J.
  (L2) sum over ALL compositions of t^{G'} x^{S_J} = F_t(x)^R,  F_t(x) = sum_{u>=2} (u-1) t^{[3<=u<=N0+1]} x^u.
  (L3) on C_J: G_sh >= G' - K.
  (L4) P*(S_i <= top[i] for all i, K >= k) <= p^k, p = 1/alpha (memoryless geometric digits; martingale).
  => P_conf(G_sh <= a) <= J t^{-(a+k-1)} x^{-sg} F_t(x)^R / binom(sg-1,J-1) + p^k / (|C_J| p^J q^{sg-J}).
usage: python3 shape_ld.py"""
import math

AL = math.log2(3); p = 1 / AL; q = 1 - p
LN2 = math.log(2)

def F(t, x, N0):
    base = x * x / (1 - x) ** 2
    return base - (1 - t) * sum((u - 1) * x ** u for u in range(3, N0 + 2))

def golden(f, lo, hi, it=70):            # minimize a unimodal function on [lo, hi]
    g = (math.sqrt(5) - 1) / 2
    a, b = lo, hi
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd: b, d, fd = d, c, fc; c = b - g * (b - a); fc = f(c)
        else: a, c, fc = c, d, fd; d = a + g * (b - a); fd = f(d)
    x = (a + b) / 2
    return x, f(x)

def free(t, N0):        # inf over x of ln F_t(x) - 2 alpha ln x  (convex in ln x); returns (x*, value)
    s, v = golden(lambda s: math.log(F(t, math.exp(s), N0)) - 2 * AL * s, -12, -1e-9)
    return math.exp(s), v

def psi(t, N0):          # asymptotic pressure per PAIR (nats): lim (1/R) ln E_conf[t^{G'}]   (see report)
    return free(t, N0)[1] - free(1.0, N0)[1]

def rate_pair(g, N0):    # Legendre transform: I(g) = sup_{t<=1} [-psi(t) - g ln(1/t)]  (nats per pair)
    lt, v = golden(lambda lt: psi(math.exp(lt), N0) - g * lt, -30, 0.0)
    return -v, math.exp(lt)

def lbinom2(n, k):       # exact log2 binomial
    c = math.comb(n, k); return math.log2(c) if c < 2 ** 1000 else (c.bit_length() - 1 + math.log2(c / 2 ** (c.bit_length() - 1)))

def log2_int(n):
    e = n.bit_length() - 1
    return e + math.log2(n / 2 ** e) if e < 1000 else e + math.log2((n >> (e - 52)) / 2 ** 52)

def rigorous_bound(J, N0, g, logC=None):
    """min over (k, t, x) of the two-term bound for P_conf(G_sh < gR); returns log2 of the bound.
    logC = exact log2 |C_J| if known (else the cycle-lemma lower bound is used)."""
    R = J // 2; sg = math.floor(J * AL); a = math.ceil(g * R) - 1
    lb = lbinom2(sg - 1, J - 1)
    lC = logC if logC is not None else lb - math.log2(J)
    best = None
    for k in range(1, R + 1):
        t2 = (k * math.log2(p)) - (lC + J * math.log2(p) + (sg - J) * math.log2(q))   # log2 of term 2
        if best is not None and t2 > best + 5: continue
        def f1(lt):   # log2 term 1 minimized over x for this t
            t = math.exp(lt)
            s, v = golden(lambda s: R * math.log(F(t, math.exp(s), N0)) - sg * s, -12, -1e-9, 120)
            return (math.log2(J) - (a + k - 1) * lt / LN2 + v / LN2 - lb)
        lt, v1 = golden(f1, -30, 0.0, 120)
        tot = max(v1, t2) + math.log2(1 + 2 ** (-abs(v1 - t2)))
        if best is None or tot < best: best, arg = tot, (k, math.exp(lt))
    return best, arg

if __name__ == "__main__":
    for N0 in (2, 4):
        pg = sum((u - 1) * p * p * q ** (u - 2) for u in range(3, N0 + 2))
        print(flush=True); print(f"N0={N0}: p_g = P*(3 <= u <= N0+1) = {pg:.5f}   (DP shape-only mean: 0.2940 R / 0.5366 R)")
        print("   pressure per step (bits) (1/J)log2 E[t^G] -> psi(t)/(2 ln2):  " +
              "  ".join(f"t={t}: {psi(t, N0) / (2 * LN2):+.5f}" for t in (0.1, 0.25, 0.5, 0.75, 0.9)))
        print("   Legendre rate per step (bits) I(g)/(2 ln2):  " +
              "  ".join(f"g={g}: {rate_pair(g, N0)[0] / (2 * LN2):.4f}" for g in (0.02, 0.05, 0.1, 0.15, 0.2, 0.25)))
        # contact-adjusted asymptotic rigorous rate: min(I(g+eps)/2, eps*log2(alpha)/2), optimized over eps
        for g in (0.05, 0.1, 0.2):
            best = max((min(rate_pair(g + e, N0)[0] / (2 * LN2), e * math.log2(AL) / 2), e)
                       for e in [i / 400 for i in range(1, int(400 * (pg - g)))])
            print(f"   rigorous asymptotic rate at g={g}: c = {best[0]:.4f} bits/step (eps = {best[1]:.3f})")
