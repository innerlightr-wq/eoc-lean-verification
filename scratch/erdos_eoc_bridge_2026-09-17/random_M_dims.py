"""Control for POW2_DIMS: dim_H C(1,M) for random M = 1 mod 3 with the same number of ternary digits as 2^a
(a = 16, 20, 24), versus the independent-digit heuristic beta = 2*(2/3) = 4/3, dim = log3(4/3) = 0.261860.
Also k = 2 random multipliers (heuristic beta = 2*(2/3)^2 = 8/9 < 1 => dim 0)."""
import math, random, sys
from automata import build_stationary, spectral_radius
random.seed(20260917)
print("heuristic log3(4/3) =", round(math.log(4/3,3),6))
for a in (16, 20, 24):
    nd = math.floor(a*math.log(2,3))+1
    ds=[]
    for trial in range(8):
        while True:
            M = random.randrange(3**(nd-1), 3**nd)
            if M % 3 == 1: break
        order, edges = build_stationary([M])
        beta = spectral_radius(order, edges, iters=20000, tol=1e-12)
        ds.append(math.log(beta,3) if beta>1+1e-12 else 0.0)
    print(f"{nd} ternary digits (like 2^{a}): dims " + " ".join(f"{d:.4f}" for d in ds) + f"  mean {sum(ds)/len(ds):.4f}")
    sys.stdout.flush()
for nd in (8, 11, 14):
    pos=0; mx=0
    for trial in range(40):
        Ms=[]
        while len(Ms)<2:
            M=random.randrange(3**(nd-1),3**nd)
            if M%3==1: Ms.append(M)
        order, edges = build_stationary(Ms)
        beta = spectral_radius(order, edges, iters=20000, tol=1e-12)
        d = math.log(beta,3) if beta>1+1e-9 else 0.0
        pos += d>1e-6; mx=max(mx,d)
    print(f"k=2 random multipliers with {nd} digits: {pos}/40 positive dimension, max {mx:.4f}")
