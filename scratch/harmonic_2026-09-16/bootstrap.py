"""Bootstrap contraction test (Parts XIII-XV): does tightening the barrier c actually move the frontier?

r_min(N,c) = least odd seed whose orbit word is c-confined (R_j <= c for all j <= N) to depth N.
The injective-harmonic ceiling replaces c = 1 by c = (1/(6 ln2)) ln(1+2C) at N = C m (0.387 at C = 2,
0.264 at C = 1, 0.167 at C = 1/2).  If r_min(N,c) were strongly c-dependent, the bootstrap map C -> F(C)
would contract and give L_1(m) = o(m).  This measures the dependence exactly, by exhaustive scan.

Also: the moving-ceiling version, where the barrier for seed m at step j is exactly B_m(j) =
(1/(6 ln2)) ln(1 + 2j/m) -- the true non-descent constraint under distinctness -- giving
  Lharm(m) = max N with R_j <= B_m(j) for all j <= N,
and the frontier r_min^harm(N) = least odd m with Lharm(m) >= N.
usage: python3 bootstrap.py XMAX"""
import math, sys

AL = math.log2(3); LN2 = math.log(2)
X = int(sys.argv[1]) if len(sys.argv) > 1 else 3000000
NCAP = 300
CS = [1.0, 0.5, 0.387, 0.264, 0.167, 0.0]

def Lc(m, c):
    x = m; S = 0
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a
        if S - j * AL > c: return j - 1
        x = v >> a
    return NCAP

def Lharm(m):
    x = m; S = 0
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a
        if S - j * AL > math.log(1 + 2 * j / m) / (6 * LN2): return j - 1
        x = v >> a
    return NCAP

best = {c: {} for c in CS}      # c -> N -> least seed
bestH = {}
m = 3
while m <= X:
    for c in CS:
        L = Lc(m, c)
        for N in range(1, L + 1):
            if N not in best[c]: best[c][N] = m
    L = Lharm(m)
    for N in range(1, L + 1):
        if N not in bestH: bestH[N] = m
    m += 2

print(f"r_min(N,c) for several barriers c  (exhaustive odd scan to {X})")
hdr = "   N  " + "".join(f"  c={c:<10}" for c in CS) + "   moving B_m(j)"
print(hdr)
Nmax = min(max(best[1.0]), 60)
for N in range(2, Nmax + 1):
    row = f"{N:5d} "
    for c in CS:
        v = best[c].get(N)
        row += f"  {v if v else '>X':<11}"
    row += f"   {bestH.get(N, '>X')}"
    print(row)

print("\nratio r_min(N,c)/r_min(N,1) (the bootstrap gain factor):")
print("   N  " + "".join(f"  c={c:<8}" for c in CS[1:]))
for N in range(5, Nmax + 1, 5):
    base = best[1.0].get(N)
    if not base: continue
    row = f"{N:5d} "
    for c in CS[1:]:
        v = best[c].get(N)
        row += f"  {v/base:<9.3f}" if v else "  >X       "
    print(row)

print("\nlog2 r_min(N,c) / N  (exponential rate of the frontier):")
print("   N  " + "".join(f"  c={c:<8}" for c in CS) + "  harm")
for N in range(10, Nmax + 1, 5):
    row = f"{N:5d} "
    for c in CS:
        v = best[c].get(N)
        row += f"  {math.log2(v)/N:<9.4f}" if v else "  >X       "
    v = bestH.get(N)
    row += f"  {math.log2(v)/N:.4f}" if v else "  >X"
    print(row)
