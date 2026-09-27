"""Cross-check tcommon.FastEnv against the previous round's common.Env, and against
the published maxima in oddpressure_2026-09-16/SCAN_400_K16.txt."""
import time
import common as C
import tcommon as T

print("== engine agreement (common.Env vs tcommon.FastEnv) ==")
worst = 0.0
for J in (200, 400):
    G0, G1 = C.Geom(J), T.Geom(J)
    for LAM in (1, 5, 7, 11, 1025):
        e0 = C.Env(G0, LAM, 3.0)
        e1 = T.FastEnv(G1, LAM, 3.0)
        for K in (8, 16):
            for r0 in (1, 5, 30, 60):
                if r0 + 2 * K >= G0.R - 1:
                    continue
                a = e0.cw_at(r0, K)[0]
                b = e1.cw_at(r0, K)[0]
                worst = max(worst, abs(a - b))
print(f"  max |CW_old - CW_new| over 80 checks = {worst:.3e}   (float assoc. only)")

print("\n== sweep vs per-anchor agreement ==")
G = T.Geom(400)
env = T.FastEnv(G, 11, 3.0)
t = time.time()
sw = env.pressure_sweep(16)
tsw = time.time() - t
w2 = 0.0
for j in list(sw)[::17]:
    w2 = max(w2, abs(sw[j][0] - env.cw_at(j, 16)[0]))
print(f"  max |sweep - direct| = {w2:.3e};  sweep of {len(sw)} anchors took {tsw:.1f}s")

print("\n== published maxima, J=400 stride-1, K=16 / 24 (oddpressure SCAN_400_K16.txt) ==")
pub = {(1, 16): 0.1739, (1, 24): 0.1196, (5, 16): 0.1593, (5, 24): 0.1454,
       (7, 16): 0.1400, (11, 16): 0.1835, (11, 24): 0.1334, (101, 16): 0.1375,
       (1025, 16): 0.1501}
for (LAM, K), v in sorted(pub.items()):
    env = T.FastEnv(G, LAM, 3.0)
    sw = env.pressure_sweep(K)
    mx = max(sw.values())
    print(f"  lam={LAM:5d} K={K}: new max {mx[0]:.4f} at r0={max(sw,key=lambda j:sw[j][0])}"
          f"   published {v:.4f}   {'OK' if abs(mx[0]-v)<5e-4 else 'MISMATCH'}")
