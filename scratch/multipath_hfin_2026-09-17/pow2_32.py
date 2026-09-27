import math, time
from automata import build_stationary, spectral_radius
t0=time.time()
order, edges = build_stationary([2 ** 32])
beta = spectral_radius(order, edges, iters=20000, tol=1e-12)
print(f"a=32 states={len(order)} beta={beta:.6f} dim={math.log(beta,3):.6f} ({time.time()-t0:.0f}s)")
