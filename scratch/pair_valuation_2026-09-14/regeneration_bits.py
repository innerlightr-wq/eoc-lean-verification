"""Paper App. D.9 regeneration statistics, recomputed via the (verified) collapse identity:
   chi_j = n mod 2^{S_j},  X_j = n >> S_j,  M_j = v2(X_j),  K_j = X_j mod 2^{d_{j+1}},
   failure at step j+1  <=>  K_j != 0,   v2(a-u) = M_{j+1} + d_{j+1} - M_j,  H_tr = F_j + M_j.
Seed sizes are NOT stated in the paper; several sizes are reported."""
import random, sys
from math import log2
rng = random.Random(1)
def v2(n): return (n & -n).bit_length() - 1
def lg(x):  # log2 of a positive big int
    b = x.bit_length()
    return b - 53 + log2(x >> (b - 53)) if b > 53 else log2(x)
for B, NT in ((64, 40000), (400, 10000), (800, 10000)):
    ev = big = pin_big = regen = regen_pin = 0
    maxmargin = 0.0
    for _ in range(NT):
        n = rng.getrandbits(B) | 1 | (1 << (B - 1))
        m, S = n, 0
        j = 0
        while True:
            x = 3 * m + 1; d = v2(x); m = x >> d
            if j >= 1:
                X = n >> S
                if X == 0:
                    break                      # pinned: no failures ever again
                K = X & ((1 << d) - 1)
                if K:                          # failure at step j+1
                    ev += 1
                    chi = n & ((1 << S) - 1)
                    F = S - lg(chi)
                    M = v2(X)
                    H = F + M
                    X1 = n >> (S + d)
                    pinning = X1 == 0
                    if H >= 8:
                        big += 1
                        pin_big += pinning
                        va = float("inf") if pinning else v2(X1) + d - M
                        if va > H:
                            regen += 1
                            regen_pin += pinning
                            if not pinning:
                                maxmargin = max(maxmargin, va - H)
            S += d; j += 1
    print(f"B={B:4d} bits, {NT} seeds: failures={ev} ({ev/NT:.1f}/traj); H>=8: {big} ({big/NT:.2f}/traj, "
          f"{pin_big} are the pinning failure); v2(a-u)>H: {regen} (ratio {regen/max(big,1):.2e}; "
          f"{regen_pin} at pinning; max finite margin {maxmargin:.2f})")
