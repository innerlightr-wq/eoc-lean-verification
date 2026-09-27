"""PART V: is there a deterministic pressure-from-counting INEQUALITY?

Task 5 of the quadratic round showed black density is not a sufficient statistic in the
variance sense (R^2 = 0.21 for a single block).  But a rigorous upper bound does not need
R^2 -- it needs the UPPER ENVELOPE of cumulative pressure given the cumulative black count:

        sum_{r in W} w_r   <=   A * B_W  +  B0 * |W|  +  C           (*)

If (*) holds with A*rho + B0 < theta for the achievable black density rho, then a black-counting
hypothesis would imply the averaged-pressure bound (Part VII wrapper).

This script computes, over every window of every corpus environment, the pair
(B_W, sum w) and extracts the exact upper envelope, then finds the best (A, B0, C).
usage: python3 envelope.py"""
import json, math, os, sys

CORP = json.load(open("/home/elias/GitHub/eoc-lean-verification/scratch/transient_2026-09-16/corpus.json"))
THETA = 0.137
MARGIN = 20

# corpus entries carry w (block weights) and nblack (per-block black-cell count)
envs = []
for c in CORP:
    w = c["w"][2:c["Rend"] - MARGIN]
    nb = c["nblack"][2:2 + len(w)]
    if len(nb) == len(w):
        envs.append((c["J"], c["lam"], w, nb))
print(f"environments: {len(envs)}  (J, lam) e.g. {[(e[0], e[1]) for e in envs[:6]]}")
tot = sum(len(e[2]) for e in envs)
print(f"total blocks: {tot}")

# black density actually realised
allnb = [x for _, _, _, nb in envs for x in nb]
print(f"mean black cells per block: {sum(allnb)/len(allnb):.4f}")

print("\n=== upper envelope of (sum w - theta*L) against (B_W - rho*L) ===")
for L in (1, 2, 4, 8, 16, 24, 32, 64):
    pts = []
    for J, lam, w, nb in envs:
        n = len(w)
        cw = [0.0]; cb = [0]
        for i in range(n):
            cw.append(cw[-1] + w[i]); cb.append(cb[-1] + nb[i])
        for a in range(0, n - L + 1):
            pts.append((cb[a + L] - cb[a], cw[a + L] - cw[a]))
    if not pts: continue
    # exact upper envelope: for each B value the max of sum w
    env = {}
    for B, S in pts:
        if B not in env or S > env[B]: env[B] = S
    Bs = sorted(env)
    # best linear upper bound S <= A*B + B0*L + C with C = 0 forced first (two-parameter fit
    # by taking the max over B of (S - A*B)/L for a grid of A)
    best = None
    for A in [i / 200 for i in range(0, 121)]:
        B0 = max((env[B] - A * B) for B in Bs) / L
        val = A * (sum(allnb) / len(allnb)) + B0     # predicted per-block bound at mean density
        if best is None or val < best[0]:
            best = (val, A, B0)
    val, A, B0 = best
    mx = max(env[B] - THETA * L for B in Bs)
    print(f"  L={L:3d}: envelope max(sum w - theta L) = {mx:+8.4f} ; best linear bound "
          f"A={A:.3f} B0={B0:+.4f} -> per-block bound at mean density = {val:+.4f} "
          f"({'BELOW' if val < THETA else 'ABOVE'} theta={THETA})")

print("\n=== how tight is the bound as a function of the window black count? ===")
L = 24
pts = []
for J, lam, w, nb in envs:
    n = len(w)
    cw = [0.0]; cb = [0]
    for i in range(n):
        cw.append(cw[-1] + w[i]); cb.append(cb[-1] + nb[i])
    for a in range(0, n - L + 1):
        pts.append((cb[a + L] - cb[a], cw[a + L] - cw[a]))
env = {}
for B, S in pts:
    if B not in env or S > env[B]: env[B] = S
print(f"  L = {L}: (black count B in window) -> (max sum w), and theta*L = {THETA*L:.3f}")
for B in sorted(env)[:24]:
    n_at = sum(1 for b, _ in pts if b == B)
    print(f"    B={B:4d}  max sum w = {env[B]:+8.4f}   excess over theta*L = {env[B]-THETA*L:+8.4f}   (n={n_at})")
