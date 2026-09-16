"""End-to-end parameter budget for the reduced chain (Parts L-LII).

Chain requirement (EOC/WhiteContraction.lowFreqDecay_of_criticalWhiteCount):
    kappa(d,N0)^{2k} + rho <= C * 2^{-gamma*j0},   rho = rho1 + rho2,
    kappa(d,N0) = 1 - 2(1-cos(pi d))/N0.
Shape side (EOC/ShapeTail.shapeTail_of_tightTail):  (k+n) + T + sigma/(N0+2) <= R = j0/2,
    rho1 = P_conf(#tight >= T)  (TightTail, OPEN).
Odd side (OddBlack.criticalWhiteCount_of_shape_and_oddPressure): M <= rho2 * ((1+s)/2)^n.

Given N0 and a target gamma, this computes the k forced by the contraction, the block budget left for
T, and whether T sits above the measured tight mean 0.4005 R with margin.
usage: python3 budget.py"""
import math

ETA = 1 / 54
D = ETA / 2                     # d = eta/2, the repo's Tao-cell phase separation
ALPHA = math.log2(3)
TIGHT_MEAN = 0.4005             # measured exactly by tight.py (J=200, exact confined DP)
RATE = {0.42: 0.00110, 0.45: 0.00701, 0.48: 0.01850, 0.50: 0.02867, 0.55: 0.06522, 0.60: 0.11770}

def kappa(N0):
    return 1 - 2 * (1 - math.cos(math.pi * D)) / N0

print(f"d = eta/2 = {D:.6f}, 1 - cos(pi d) = {1-math.cos(math.pi*D):.3e}")
print("\n  N0    kappa        -log2 kappa    k/R needed per unit gamma*J   sigma/((N0+2)R)   max T/R (k/R=0.1)")
for N0 in (4, 6, 8, 10, 14, 20, 30):
    kap = kappa(N0)
    lk = -math.log2(kap)
    # kappa^{2k} <= 2^{-gamma j0}, j0 = 2R  =>  k >= gamma*2R/(2*lk) = gamma*R/lk
    kR_per_gamma = 1 / lk        # k/R = gamma / lk
    loss = 2 * ALPHA / (N0 + 2)  # sigma/((N0+2)R) with sigma ~ 2*alpha*R
    print(f"  {N0:3d}   {kap:.7f}   {lk:.3e}     {kR_per_gamma:10.1f} * gamma        "
          f"{loss:.4f}          {1 - 0.1 - loss:7.4f}")

print("\nfeasible interior points (need T/R > tight mean 0.4005 with margin, and k/R + n/R + T/R + loss <= 1):")
print("  N0   T/R    rate(bits/digit)   loss    k/R+n/R available   max gamma (at k/R = available/2)")
for N0 in (6, 10, 14, 20):
    loss = 2 * ALPHA / (N0 + 2)
    for TR in (0.45, 0.50, 0.55, 0.60):
        avail = 1 - TR - loss
        if avail <= 0.02: continue
        lk = -math.log2(kappa(N0))
        gamma_max = (avail / 2) * lk          # k/R = gamma/lk  =>  gamma = (k/R)*lk
        print(f"  {N0:3d}  {TR:.2f}   {RATE.get(TR, float('nan')):.5f}          {loss:.4f}   "
              f"{avail:8.4f}          {gamma_max:.3e}")
print("\nNote: gamma only needs to be > 0; rho1 = 2^{-rate*J} must beat C*2^{-gamma*j0}, i.e. rate > gamma.")
