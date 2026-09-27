"""Rational barriers b_beta(j) = floor(j p/q) vs the true b_alpha(j) = floor(j*log2 3).

Parts IV-VII: exact continued-fraction data, agreement length, disagreement counts, and the
contact interpretation.  All comparisons are EXACT: floor(j*alpha) is computed from a
high-precision rational lower/upper bracket for alpha and only used when the bracket determines
the floor unambiguously (asserted), so no floating-point rounding enters the combinatorics.
usage: python3 cf.py [NMAX]"""
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 120
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200000

# --- exact-enough bracket for alpha = log2 3 -------------------------------------------------
AL = (Decimal(3).ln() / Decimal(2).ln())
ALF = F(int(AL * 10**60), 10**60)          # rational lower bound, 60 digits
ALF_HI = ALF + F(1, 10**60)

def floor_alpha(j: int) -> int:
    lo = (ALF * j).__floor__()
    hi = (ALF_HI * j).__floor__()
    assert lo == hi, "bracket too coarse"
    return lo

# --- continued fraction of alpha ---------------------------------------------------------------
x = AL
a = []
for _ in range(20):
    i = int(x); a.append(i); x = x - i
    if x == 0: break
    x = 1 / x
p0, q0, p1, q1 = 1, 0, a[0], 1
conv = [(p1, q1)]
for ai in a[1:]:
    p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
    conv.append((p1, q1))

print(f"alpha = log2 3, continued fraction {a[:16]}")
print("\nPART IV -- exact convergent data")
print("      p/q        side   eps = |alpha - p/q|      q^2*eps    1/eps      first j with floors differing")
rows = []
for (p, q) in conv[1:11]:
    beta = F(p, q)
    eps = abs(ALF - beta)
    side = "above" if beta > ALF_HI else ("below" if beta < ALF else "?")
    first = None
    for j in range(1, NMAX + 1):
        if floor_alpha(j) != (p * j) // q:
            first = j; break
    rows.append((p, q, side, eps, first))
    print(f"  {p:>9}/{q:<7} {side:5s}  {float(eps):.6e}   {float(q*q*eps):8.4f}  {float(1/eps):12.1f}   "
          f"{first if first else '> ' + str(NMAX)}")

print("\nPART V/VI -- agreement length L_agree and disagreement density |D(N)|/N")
print("      p/q       L_agree     q      q^2       1/eps    L_agree/q   L_agree/(1/eps)   |D(N)|/N  (N=%d)   N*eps" % NMAX)
for (p, q, side, eps, first) in rows:
    L = (first - 1) if first else NMAX
    dis = sum(1 for j in range(1, NMAX + 1) if floor_alpha(j) != (p * j) // q)
    print(f"  {p:>9}/{q:<7} {L:>8}  {q:>6}  {q*q:>8}  {float(1/eps):10.1f}   {L/q:9.2f}   "
          f"{L*float(eps):12.4f}   {dis/NMAX:.6f}   {NMAX*float(eps):.4f}")

print("\nPART VII -- contact interpretation: disagreement forces ||j*alpha|| <= j*eps")
print("  (PROVED (MATH): floors differ => an integer lies weakly between j*alpha and j*beta)")
print("      p/q      #disagree   max ||j alpha||   max (j*eps) over those j   implication holds")
for (p, q, side, eps, first) in rows[:8]:
    beta = F(p, q)
    worst = F(0); worstb = F(0); ok = True
    cnt = 0
    for j in range(1, min(NMAX, 60000) + 1):
        if floor_alpha(j) != (p * j) // q:
            cnt += 1
            fa = ALF * j
            nrm = min(fa - fa.__floor__(), fa.__floor__() + 1 - fa)
            bd = j * eps
            worst = max(worst, nrm); worstb = max(worstb, bd)
            if nrm > bd: ok = False
    print(f"  {p:>9}/{q:<7} {cnt:>9}   {float(worst):.3e}      {float(worstb):.3e}            {ok}")
