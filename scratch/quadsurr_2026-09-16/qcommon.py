"""shared: build a Geom with a swapped barrier, and the exact additive block weights.

Reuses the verified engine scratch/transient_2026-09-16/tcommon.py unchanged.
The barrier swap follows scratch/ratbarrier_2026-09-16/pressure_swap.py exactly:
  G = tcommon.Geom(J);  G.top = [min(bar(i), G.sg) for i in range(J+1)]
so the 3-adic environment (blackness, modulus 3^{2r+2}) and the chain weights are
untouched -- ONLY which cells are read changes.
"""
import sys, math, os
sys.path.insert(0, "/home/elias/GitHub/eoc-lean-verification/scratch/transient_2026-09-16")
import tcommon as T                                    # noqa: E402
from tcommon import Geom, FastEnv, cell_xrange, row_values, row_black_list, ETA_DEN  # noqa

DIR = os.path.dirname(os.path.abspath(__file__))
THETA_MAX = 0.137


def geom_with(J, bar):
    G = Geom(J)
    G.top = [min(bar(i), G.sg) for i in range(J + 1)]
    return G


def weights(G, lam, s=3.0):
    """exact additive block weights w_r = (a_r - a_{r+1})/2 ; a_r = log2 max_S M(r)[S]."""
    Rend = G.R - 1
    env = FastEnv(G, lam, s)
    V = env.ones(Rend)
    a = [0.0] * (Rend + 1)
    for r in range(Rend - 1, -1, -1):
        V = env.apply_T(r, V)
        mx = max(V)
        a[r] = math.log2(mx) if mx > 0 else -1e9
    return [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)], Rend


def longrun(w, Rend):
    """mean of w over r in [2, Rend-20) -- the convention fixed by the previous round."""
    seg = w[2:Rend - 20]
    return sum(seg) / len(seg), seg
