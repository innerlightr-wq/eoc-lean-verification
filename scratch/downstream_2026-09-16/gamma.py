"""Best LowFreqDecay rate gamma allowed by the Lean hypotheses of FrontierRegion.lowFreqDecay_of_sparsityAt,
and the heuristic conditional exponent improvement.  Exact rational/float arithmetic, no search over j (asymptotic j).
Constraints (per unit j, j -> infinity): Kb/j <= 1/2 - 31/100 - (sigma/j)/(N0+2);  k/j + n/j <= Kb/j;
n/j >= nu >= theta' + gamma (s = 3, log2((1+s)/2) = 1);  theta' > 1/6 (limit theta' -> 1/6);
gamma <= 8 (k/j) d^2 / (N0 ln 2);  gamma <= 1/300 - delta/j (shape tail rate).  sigma/j <= alpha."""
import math
AL = math.log2(3); H = -(1/AL)*math.log2(1/AL) - (1-1/AL)*math.log2(1-1/AL); I0 = AL*(1-H)
def gmax(d, sig=AL):
    best = (0, None)
    for N0 in range(2, 2000):
        slack = 0.5 - 0.31 - sig/(N0+2) - 1/6          # = k/j + gamma  at the optimum
        if slack <= 0: continue
        c = 8*d*d/(N0*math.log(2))                     # gamma <= c * k/j,  k/j = slack - gamma
        g = min(c*slack/(1+c), 1/300)
        if g > best[0]: best = (g, N0)
    return best
print(f"alpha={AL:.7f} H2(1/alpha)={H:.7f} I0={I0:.7f}")
for d in (1/108, 1/54, 1/20, 1/10, 1/4, 1/2):
    g, N0 = gmax(d)
    lo, hi = I0/((2-H)*(AL+2.1)*AL) , (1-H)/((2-H)*AL)    # conservative (t up to (alpha+2.1)L) and model-1 (t = alpha L)
    print(f"d=1/{1/d:.0f}: gamma_max={g:.3e} (N0={N0}); heuristic eps_exp in [{lo*g:.2e}, {hi*g:.2e}]"
          f"  (coefficients {lo:.4f}..{hi:.4f}); exponent <= {H - lo*g:.10f}")
