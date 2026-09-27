"""Extend AL13 Table 5.2: dim_H C(1, 2^a) for even a (odd a gives {0}), plus reachable state counts.
Also checks the carry-collapse bound  #states C(1,2^{a_1},...,2^{a_k}) <= #states C(1,2^{a_max})  on all pairs a<b<=16."""
import math, sys, time
from automata import build_stationary, spectral_radius
t0=time.time()
print(" a   states  beta       dim_H C(1,2^a)")
for a in range(2, 31, 2):
    order, edges = build_stationary([2 ** a])
    beta = spectral_radius(order, edges, iters=20000, tol=1e-12)
    print(f"{a:2d} {len(order):8d}  {beta:.6f}  {math.log(beta,3):.6f}   ({time.time()-t0:.0f}s)")
    sys.stdout.flush()
    if time.time()-t0 > 1500: break
