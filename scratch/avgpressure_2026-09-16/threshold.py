"""Sufficient pressure thresholds implied by the PROVED (LEAN) chain in EOC/AverageOddDark.lean.

Lean hypotheses (per unit of word length j, asymptotically; floors only help for large j):
  block budget  K/j <= Kmax(N0) = 1/2 - 31/100 - 317/(200 (N0+2))      (shapeTail_allEven_budget + barrier_lt)
  split         k + n <= K,  n >= nu j,  k = kap j
  pressure      theta < theta' ,  theta' + gamma <= nu * log2((1+s)/2)     (criticalWhiteCount_rate)
  good blocks   gamma * j * ln 2 <= 8 k d^2 / N0                            (lowFreqDecay_of_averagePressure)
  ShapeTail     gamma <= 1/300
So the sufficient condition on the averaged pressure is  theta(s) < (Kmax(N0) - kap) * log2((1+s)/2).
Pressure inputs are the COMPUTATIONAL values of earlier rounds (Tao-black count, eta = 1/54, which bounds
N_odd at d = 1/108 at lambda = 1 via OddBlack.nodd_one_le_ntao).
"""
from math import log2, log

def Kmax(N0): return 0.5 - 0.31 - 317 / (200 * (N0 + 2))

S = [1.5, 2, 3, 4, 6]
# true environment, global pressure, J = 1200 (oddblack_2026-09-16/CONSTANTS.txt), bits per step
TRUE1200 = {1.25: 0.00645, 1.5: 0.01278, 2: 0.02500, 2.5: 0.03665, 3: 0.04796, 4: 0.07072, 6: 0.11125}
print("Kmax(N0):", {N0: round(Kmax(N0), 4) for N0 in (4, 10, 20, 30, 50, 100, 1000)})
print("\nsup sufficient theta (kap -> 0):  theta_max = Kmax(N0) * log2((1+s)/2)")
print("   s  " + "".join(f"  N0={N0:<5d}" for N0 in (10, 30, 100, 1000)) + "   measured true J=1200")
for s in S:
    L = log2((1 + s) / 2)
    print(f"{s:4}  " + "".join(f"  {Kmax(N0) * L:8.4f}" for N0 in (10, 30, 100, 1000))
          + f"   {TRUE1200[s]:.4f}")
print("\nratio theta(s)/log2((1+s)/2) that must stay below Kmax - kap (true env J=1200):")
for s, th in sorted(TRUE1200.items()):
    print(f"  s={s}: {th / log2((1 + s) / 2):.4f}")
print("\nconcrete Lean schedules at s = 3 (L = 1): N0=30 K=7j/50 -> theta < 0.14 - kap ;"
      " N0=100 K=17j/100 -> theta < 0.17 - kap")
d = 1 / 108
print("\nbest rate gamma = min(1/300, nu*L - theta', 8 kap d^2/(N0 ln 2)), d = 1/108, s = 3, theta' = theta:")
for N0, K in ((30, 0.14), (100, 0.17)):
    for theta in (0.048, 0.10, 0.137, 0.14, 0.15):
        best = (0, None)
        for i in range(1, 2000):
            kap = K * i / 2000
            nu = K - kap
            g = min(1 / 300, nu - theta, 8 * kap * d * d / (N0 * log(2)))
            if g > best[0]:
                best = (g, kap)
        print(f"  N0={N0:3d} theta={theta:.3f}: gamma={best[0]:.3e}" + (f" at k/j={best[1]:.4f}" if best[1] else "  (infeasible)"))
