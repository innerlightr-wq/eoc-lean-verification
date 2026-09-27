"""Per-state local bad density (Parts XXII-XXIII, XXXVII): for Haar-random local residues W, the probability that
a K-window started at a fixed state is bad, P(P_K >= theta), and its decay rate kappa = -log2 P / K.
usage: python3 density.py J K samples [theta_list]"""
import math, random, sys
exec(open('perstate.py').read().split('random.seed(5)')[0].replace("sys.argv[3]", "'0.4'").replace(
     "J = int(sys.argv[1]); K = int(sys.argv[2])", "J = int(sys.argv[1]); K = int(sys.argv[2])"))
NS = int(sys.argv[3])
random.seed(101 + K)
S0 = (2 * r0 + top[2 * r0]) // 2
vals = []
MOD = 3 ** DEPTH
for _ in range(NS):
    W = random.randrange(1, MOD)
    while W % 3 == 0: W = random.randrange(1, MOD)
    v = MK_from_W(W, S0)
    if v > float('-inf'): vals.append(v)
vals.sort(); n = len(vals)
print(f"J={J} K={K} r0={r0} S0={S0}: {n} Haar local residues: mean {sum(vals)/n:.4f} median {vals[n//2]:.4f} "
      f"95% {vals[int(0.95*n)]:.4f} max {vals[-1]:.4f}")
for th in (0.08, 0.10, 0.12):
    c = sum(1 for v in vals if v >= th)
    if c: print(f"   P(P_K >= {th}) = {c}/{n} = {c/n:.4f}, kappa = -log2 P / K = {-math.log2(c/n)/K:.4f}")
    else: print(f"   P(P_K >= {th}) = 0/{n} (kappa >= {math.log2(n)/K:.4f})")
