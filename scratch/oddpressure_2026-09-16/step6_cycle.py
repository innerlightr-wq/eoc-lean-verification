"""STEP 6 -- concatenation / long-product growth.

(6B) Along ONE realized environment the "max cycle mean of log local pressure" over a window of
L blocks is exactly
      Lambda(r0,L) = (1/(2L)) log2 max_S M_L(r0)[S],
because T is a (sub)probability kernel at s = 1 (sum_u (u-1) p^2 q^{u-2} = 1), so M_L is the
sup-norm growth of the L-fold product.  We compute it exactly (floating point arithmetic in the
operator, exact 3-adic input) for the adversarial environment and for the true low-frequency ones,
and compare with the K = 32 CW value of the single worst unit.

usage: python3 step6_cycle.py
"""
import json, math
from common import Geom, Env

J, SV, K = 400, 3.0, 32
G = Geom(J)
XA = int(open("ADV_xi_400_8.txt").read().split()[0])
envs = [("adversary depth<=8", XA), ("true lam=1", 1), ("lam=5", 5), ("lam=1025", 1025)]
print(f"J={J} R={G.R} s={SV}: long-product growth Lambda(r0,L) = (1/2L) log2 max_S M_L(r0)[S]  (bits/step)")
print("theta_max = 0.137\n")
res = {}
for name, XI in envs:
    env = Env(G, XI, SV)
    row = []
    for L in (8, 16, 32, 48, 64, 96, 128, 160, 190):
        r0 = 5
        if r0 + L >= G.R - 1:
            continue
        V = env.MK(r0, L)
        mx = max(V.values())
        row.append((L, math.log2(mx) / (2 * L)))
    res[name] = row
    print(f"  {name:22s} " + "  ".join(f"L={L}:{v:.4f}" for L, v in row))

print("\n  same, anchored at r0=1 (whole available chain):")
for name, XI in envs:
    env = Env(G, XI, SV)
    out = []
    for L in (32, 64, 128, 190):
        V = env.MK(1, L)
        out.append((L, math.log2(max(V.values())) / (2 * L)))
    print(f"  {name:22s} " + "  ".join(f"L={L}:{v:.4f}" for L, v in out))
    res[name + " @r0=1"] = out

# CW at the worst unit for growing K, same anchor
print("\n  CW(r0=5,K) = log2(M_2K/M_K)[S]/(2K) as K grows (adversary):")
env = Env(G, XA, SV)
line = []
for KK in (8, 16, 32, 48, 64, 80):
    if 5 + 2 * KK >= G.R - 1:
        continue
    v, S, _ = env.cw_at(5, KK)
    line.append((KK, v, S))
print("   " + "  ".join(f"K={KK}:{v:.4f}(S={S})" for KK, v, S in line))
res["cw_growth_adv"] = [[KK, v] for KK, v, S in line]

env1 = Env(G, 1, SV)
line1 = []
for KK in (8, 16, 32, 48, 64, 80):
    if 5 + 2 * KK >= G.R - 1:
        continue
    v, S, _ = env1.cw_at(5, KK)
    line1.append((KK, v, S))
print("  CW(r0=5,K) for the true environment lam=1:")
print("   " + "  ".join(f"K={KK}:{v:.4f}(S={S})" for KK, v, S in line1))
res["cw_growth_true"] = [[KK, v] for KK, v, S in line1]
json.dump(res, open("cycle.json", "w"))
print("\nwrote cycle.json")
