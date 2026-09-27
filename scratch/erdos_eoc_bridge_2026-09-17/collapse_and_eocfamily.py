"""(1) Carry-collapse lemma check: #states C(1,2^{a_1..a_k}) <= #states C(1,2^{a_max}) (and the tuple of carries is a
function of the top carry: floor(2^a t) = floor(floor(2^b t)/2^{b-a})).
(2) Part XVII: Cantor intersections along EOC-like exponent sets.  EOC columns inside a window are z_r = x_{2r} + i_r
with consecutive differences g = i + k (two Geom>=1 steps); only even exponent differences can give positive
dimension (2^a = 2 mod 3 for odd a).  We tabulate dim C(1, 2^{a_1}, ..., 2^{a_k}) over ALL exponent sets with
a_k <= 16 and report the fraction with positive dimension, per k."""
import math, itertools, random
from automata import build_stationary, spectral_radius, dim_C
viol = 0; checked = 0
for b in range(2, 17, 2):
    nb = len(build_stationary([2 ** b])[0])
    for a in range(2, b, 2):
        n2 = len(build_stationary([2 ** a, 2 ** b])[0]); checked += 1
        if n2 > nb: viol += 1
print(f"carry collapse: {checked} pairs checked, violations {viol}")
for k in (1, 2, 3, 4):
    tot = pos = 0; best = (0, None)
    for S in itertools.combinations(range(2, 17, 2), k):
        d, nv, beta = dim_C([2 ** a for a in S]); tot += 1
        if d > 1e-9: pos += 1
        if d > best[0]: best = (d, S)
    print(f"k={k} multipliers (plus 1), even exponents <= 16: {pos}/{tot} have positive dimension; max dim {best[0]:.6f} at exponents {best[1]}")
