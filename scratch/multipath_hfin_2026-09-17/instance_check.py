"""COMPUTATIONAL certificate: all numerical hypotheses of FinalChain.exceptional_bound_of_frontier_and_scalar
(except the arithmetic frontier Prop inside ExplicitPairData) for one concrete instance.
Exact integers/rationals except: floor(j*log2 3) via 60-digit Decimal (margin checked), and the three real inequalities
with log/rpow (checked in log2 form with explicit float margins >= 1e-6 relative)."""
from decimal import Decimal, getcontext
from fractions import Fraction as F
from math import comb, log2, log, floor
getcontext().prec = 80
LOG2_3 = Decimal(3).ln() / Decimal(2).ln()
def bU(U, j):
    v = Decimal(j) * LOG2_3 + U
    f = int(v)
    assert v - f > Decimal('1e-40') and f + 1 - v > Decimal('1e-40')
    return f
U = 0
j0 = 10 ** 12                 # even
d = F(1, 108); N0 = 133; eta = F(1, 1000)
thetap = F(1, 6) + eta
ca = F(0); cb = F(0); Awin = F(2)          # window K <= Awin*log2 j + 1  (frontier parameter)
Cc = 2 + F(3, 5) * ca + F(4, 5) * Awin + (2 + F(3, 5) * cb + F(4, 5)) / 8
b = bU(U, j0)
checks = []
def ok(name, cond): checks.append((name, bool(cond))); print(("OK  " if cond else "FAIL"), name)
ok("300 <= j0, 2 | j0", j0 >= 300 and j0 % 2 == 0)
ok("hlarge: (3C/(theta'-1/6))^2 <= j0", (3 * Cc / (thetap - F(1, 6))) ** 2 <= j0)
# budget: Kb + floor(31 j/100) + floor(sigma/(N0+2)) <= j/2 for all sigma <= b
Kb = j0 // 2 - (31 * j0) // 100 - b // (N0 + 2)
n = -(-(thetap * j0 + F(1, 10 ** 6) * j0).numerator // (thetap * j0 + F(1, 10 ** 6) * j0).denominator)  # ceil
k = Kb - n
ok("k + n <= Kb, k > 0", k > 0 and k + n <= Kb)
nu = F(n, j0)
# gamma: gamma j log 2 <= 8 k d^2 / N0  and  theta' + gamma <= nu  and gamma j <= j/300 - delta
gamma_max_rate = 8 * k * d * d / N0 / j0 / F(693148, 10 ** 6)     # log 2 < 0.693148
gamma = min(gamma_max_rate, nu - thetap) * F(999, 1000)
ok("gamma*j*log2 <= 8 k d^2/N0 (log2 < 0.693148)", gamma * j0 * F(693148, 10 ** 6) <= 8 * k * d * d / N0)
ok("theta' + gamma <= nu", thetap + gamma <= nu)
print(f"   b_U(j0) = {b}, Kb = {Kb}, k = {k}, n = {n}, gamma = {float(gamma):.4e}, gamma*j0 = {float(gamma*j0):.3f}")
# choose L, xs (binary search on L; hnum worst case checked over all t with sigma = b maximal and x ranging)
gj = float(gamma * j0)
from math import lgamma
def log2comb(n, k): return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / log(2)
def try_L(L):
    N = j0 + L; B = bU(U, N); M0 = B - b + 1
    if not (L < M0): return None
    K = b + 1
    q = F(b - j0, b - 1)
    def fbar(y): return float(q) * (M0 + y) / (M0 + y - L)
    logP = 0.0; xs = None
    for y in range(0, 40 * L + 400):
        logP += log2(fbar(y))
        rho = fbar(y + 1)
        if rho < 1 and log2(N) + logP - log2(1 - rho) <= (K - (B + 1)) - 1e-3:
            xs = y; break
    if xs is None: return None
    # hnum: lhs increases with sigma, so take sigma = b; t ranges over [L, B - b + xs]
    worst = -1e18
    for t in range(L, B - b + xs + 1):
        lhs = log2(1 + (b + 1) / 2) + log2(b + t + 1) + 2 + 2 * t + log2(L)
        rhs = log2comb(t - 1, L - 1) + gj
        worst = max(worst, lhs - rhs)
    return (L, xs, N, B, K, worst) if worst <= -1e-3 else None
lo, hi = 1, int(gj / 4)
assert try_L(lo) is not None and try_L(hi) is None
while hi - lo > 1:                      # binary search for the largest feasible L (feasible set checked to be an interval at endpoints)
    mid = (lo + hi) // 2
    if try_L(mid) is not None: lo = mid
    else: hi = mid
best = try_L(lo)
print("   largest feasible L:", best[:2] if best else None, flush=True)
L, xs, N, B, K, worst = best
ok(f"hnum on all good pairs (max lhs-rhs in log2 = {worst:.3f})", worst < 0)
ok("hL: L < B - b + 1", L < B - b + 1)
ok("K <= b_U(N), b_U(j0) < K", b < K <= B)
delta = xs
ok("region: b_0(j0) <= sigma + delta for sigma >= b - xs (U=0)", bU(0, j0) <= b - xs + delta)
ok("gamma*j <= j/300 - delta", gamma * j0 <= j0 // 300 - delta)
ok("63 sigma + 37 <= 100 j for sigma <= b", 63 * b + 37 <= 100 * j0)
ok("U <= sigma", U <= b - xs)
A = F(N, K)
I0 = log2(3) * (1 - 0.9499555)
print(f"   instance: j0={j0}, L={L}, N={N}, K={K}, xs={xs}, A=N/K={float(A):.12f}, 1/alpha={1/log2(3):.12f}")
print(f"   exponent 1 - I0*A = {1 - I0*float(A):.12f}  vs baseline H2(1/alpha) = 0.9499555 ; gain = {I0*(float(A) - 1/log2(3)):.3e}")
print("ALL NUMERIC HYPOTHESES OK" if all(c for _, c in checks) else "SOME FAIL")
