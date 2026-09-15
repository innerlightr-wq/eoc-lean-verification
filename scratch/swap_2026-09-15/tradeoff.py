import math
al = math.log2(3); hv = -(1/al)*math.log2(1/al) - (1-1/al)*math.log2(1-1/al)
A = 0.7; t_over_j0 = al*(al*A - 1)          # t/j0 at the horizon split
req_L2 = (2 - hv) / 2 * t_over_j0           # bulk (odd g) requirement, bits/step
req_one = (1 - hv) / 2 * t_over_j0          # budget of a single frequency
print(f"A=0.7: t/j0={t_over_j0:.4f}; bulk requirement {req_L2:.4f} bits/step; single-frequency budget {req_one:.5f} bits/step")
print("graded by v2(g)=a (a/t = fraction): rate needed = ((2-hv) t - a)/(2 j0):",
      ", ".join(f"a/t={x:.2f}:{((2-hv) - x)/2*t_over_j0:.4f}" for x in (0, 0.25, 0.5, 0.75, 1.0)))
sw = 0.539/2   # swappable pairs per step (limit)
print("\n eta   -log2cos(pi eta)   rho needed (good swappable pairs/step) for bulk | for single-freq   max bad-run B (single-freq) ")
for eta in (0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4):
    g = -math.log2(math.cos(math.pi*eta))
    rho_b, rho_1 = req_L2/g, req_one/g
    B1 = sw*g/req_one - 1
    print(f" {eta:.2f}   {g:.4f}            {rho_b:8.4f} (={rho_b/sw:.2f} of swappable)     {rho_1:.4f} (={rho_1/sw:.3f})     B <= {B1:.1f}")
best = max(((1-2*e)*(-math.log2(math.cos(math.pi*e))), e) for e in [i/1000 for i in range(1, 500)])
print(f"\nideal equidistribution, single threshold: max_eta (1-2eta)(-log2 cos pi eta) = {best[0]:.4f} at eta={best[1]:.3f} -> rate {sw*best[0]:.4f} bits/step (bulk need {req_L2:.4f})")
print(f"ideal equidistribution, full product E|cos|=2/pi: rate {sw*-math.log2(2/math.pi):.4f} bits/step; geometric mean (E log|cos| = -1 bit): {sw*1:.4f}")
