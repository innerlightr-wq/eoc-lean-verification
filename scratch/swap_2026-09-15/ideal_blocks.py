"""Ideal-equidistribution rates (per prefix step) under the critical-tilt digit law p_d=(1/a)(1-1/a)^{d-1}:
 swap: pair (d,e) -> |cos(pi*Delta)| if d!=e (Delta uniform) else 1
 blk2: pair total u -> |sum_{d=1}^{u-1} e(2^{d-1} x)|/(u-1), x uniform (phases at S+d double in d)
 threshold versions: best eta for 'factor <= kappa(eta) on good set'."""
import math, cmath, random
a = math.log2(3); p = [0] + [(1/a)*(1-1/a)**(d-1) for d in range(1, 40)]
random.seed(1); X = [random.random() for _ in range(20000)]
# swap
E_sw = sum(p[d]*p[e]*(2/math.pi if d != e else 1) for d in range(1, 30) for e in range(1, 30))
# blk2: weight of total u is P(u)=sum_{d+e=u} p_d p_e; E over x of ratio
Pu = {u: sum(p[d]*p[u-d] for d in range(1, u)) for u in range(2, 40)}
def ratio(u, x): return abs(sum(cmath.exp(2j*math.pi*(2**(d-1))*x) for d in range(1, u)))/(u-1)
E_b2 = sum(Pu[u]*sum(ratio(u, x) for x in X[:4000])/4000 for u in range(2, 20))
print(f"ideal full-product rates: swap {-math.log2(E_sw)/2:.4f}  blk2 {-math.log2(E_b2)/2:.4f} bits/step (measured: swap ~0.158, blk2 ~0.25)")
# geometric-mean (typical path) versions
G_sw = sum(p[d]*p[e]*(-1 if d != e else 0) for d in range(1, 30) for e in range(1, 30))
G_b2 = sum(Pu[u]*sum(math.log2(max(ratio(u, x), 1e-12)) for x in X[:4000])/4000 for u in range(2, 20))
print(f"ideal geometric-mean rates: swap {-G_sw/2:.4f}  blk2 {-G_b2/2:.4f} bits/step")
