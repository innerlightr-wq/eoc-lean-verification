"""Exact check of the 3-block run rigidity (big integers).
Block r at step i_r = 3r with entry S_r, M_r = m - S_r - 1, psi_r = (3^{-(i_r+3)} mod 2^{M_r}) / 2^{M_r}.
lambda psi_r = N_r + e_r / 2^{M_r} (e_r centered).  Claims:
 (A) if 27 | e_r then e_{r+1} = e_r / 27 (any u_r);
 (B) if |e_r|/2^{M_r} < 2^{-u_r-1}/27 and 27 does not divide e_r then ||lambda psi_{r+1}|| >= 1/54."""
import random, math
al = math.log2(3)
def cen(x, M): x %= 1 << M; return x - (1 << M) if x >= 1 << (M - 1) else x
random.seed(5); fa = fb = testsA = testsB = 0
for _ in range(20000):
    J = random.choice([60, 90, 120]); c = 0; b = [math.floor(c + j * al) for j in range(J + 4)]
    sig = b[J]; t = random.randint(5, 25); m = sig + t + 1
    lam = random.randint(1, 1 << (t + random.randint(0, 20)))
    r = random.randint(0, J // 3 - 2); i = 3 * r
    S = random.randint(i, b[i]); u = random.randint(3, min(12, b[i + 3] - S)) if b[i + 3] - S >= 3 else None
    if u is None: continue
    M = m - S - 1; M2 = M - u
    if M2 < 2: continue
    x1 = pow(3, -(i + 3), 1 << M); x2 = pow(3, -(i + 6), 1 << M2)
    e1 = cen(lam * x1, M); e2 = cen(lam * x2, M2)
    if e1 % 27 == 0:
        testsA += 1
        if e2 != e1 // 27: fa += 1
    elif abs(e1) / 2**M < 2**(-u - 1) / 27:
        testsB += 1
        if abs(e2) / 2**M2 < 1 / 54: fb += 1
print(f"(A) 27|e_r => e_(r+1)=e_r/27: {testsA} tests, {fa} failures;  (B) tiny & 27 not | e_r => ||next|| >= 1/54: {testsB} tests, {fb} failures")
# kappa_u: max f_u on ||x|| >= tau_u = 2^{-u-1}/27 and on ||x|| >= 1/54
import cmath
def f(qs, x): return abs(sum(cmath.exp(2j * math.pi * q * x) for q in qs)) ** 2 / len(qs) ** 2
for u in range(4, 10):
    qs = [3 * 2**a + 2**b for a in range(u - 1) for b in range(a + 1, u - 1)]
    tau = 2**(-u - 1) / 27
    k1 = max(f(qs, tau + k * (0.5 - tau) / 20000) for k in range(20001))
    k2 = max(f(qs, 1 / 54 + k * (0.5 - 1 / 54) / 20000) for k in range(20001))
    print(f"  u={u}: kappa(tau_u={tau:.2e}) = {k1:.4f}   kappa(1/54) = {k2:.4f}")
