"""Focused λ=1 experiment: propagated pinned product versus disjoint-window sup products.

This uses exactly the geometric operators from pressure_exact_2026-09-16/geo.py.  It is a
diagnostic, not a proof: floating point arithmetic and four finite j values are used.
"""
import json
import math
import sys

sys.path.insert(0, "scratch/pressure_exact_2026-09-16")
from pexact import Instance
from geo import apply, global_geo, make_ops


def disjoint_sup_log(I, K, s=3.0):
    p, q = make_ops(I, s)
    total = 0.0
    rates = []
    r0 = 0
    while r0 < I.R:
        r1 = min(r0 + K, I.R)
        f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
        for r in range(r1 - 1, r0 - 1, -1):
            f = apply(I, r, f, s, p, q, 2 * r + 2)
        lg = math.log2(max(f))
        total += lg
        rates.append(lg / (2 * (r1 - r0)))
        r0 = r1
    return total, rates


def run(j):
    t = j // 6
    I = Instance(j, t, lam=1, D=108, mode="auto")
    K = max(1, math.floor(7 * math.log2(j)))
    pinned = global_geo(I, 3.0, pinned=True)
    unpinned = global_geo(I, 3.0, pinned=False)
    sup, rates = disjoint_sup_log(I, K)
    dangerous = sum(r > 0.10 for r in rates)
    return {
        "j": j, "t": t, "K_pair_blocks": K, "windows": len(rates),
        "pinned_rate_per_j": pinned / j,
        "unpinned_rate_per_j": unpinned / j,
        "product_sup_rate_per_j": sup / j,
        "sup_minus_pinned_per_j": (sup - pinned) / j,
        "ratio_log2": sup - pinned,
        "max_window_rate": max(rates),
        "mean_window_rate": sum(rates) / len(rates),
        "dangerous_fraction": dangerous / len(rates),
    }


if __name__ == "__main__":
    data = [run(j) for j in (400, 800, 1600, 3200, 6400)]
    with open("scratch/endpoint_pressure_2026-09-17/propagated_state.json", "w") as f:
        json.dump(data, f, indent=2)
    for x in data:
        print(json.dumps(x, sort_keys=True))
