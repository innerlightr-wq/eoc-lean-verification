"""Track B (ratio extremizer) and Track A (escape-precision / certificate) measurements.

Track B: ratio records L_1(m)/m, seeds with ratio > 1 and > 1/2, shellwise maxima
  M_k = max_{2^k <= m < 2^{k+1}} L_1(m),  H_k = max L_1(m)/m on that shell.
Track A: escape precision — each seed's escape prefix determines a residue class mod 2^{S_escape}; a class with
  2^S <= X covers several seeds of [1,X] ("shared"), one with 2^S > X covers only that seed.  The fraction of
  seeds needing a private deep class measures the compressibility of an initial-interval covering certificate.
usage: python3 tracks.py XMAX"""
import math, sys
from collections import defaultdict

AL = math.log2(3); X = int(sys.argv[1]); NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]

ratio_records = []; bestratio = 0.0
gt1 = []; gt_half = 0
Mk = defaultdict(int); Hk = defaultdict(float)
esc_shared = 0; esc_private = 0; esc_hist = defaultdict(int)
m = 3
while m <= X:
    x = m; S = 0; j = 0
    while j < NCAP:
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j + 1]:
            S += a; j += 1        # S at the escape step
            break
        S += a; j += 1; x = v >> a
    L = j - 1                      # L_1(m) = confined length (escape at step j)
    r = L / m
    if r > bestratio: bestratio = r; ratio_records.append((m, L, r))
    if L > m: gt1.append((m, L))
    if L > m / 2: gt_half += 1
    k = m.bit_length() - 1
    if L > Mk[k]: Mk[k] = L
    if r > Hk[k]: Hk[k] = r
    # escape precision: class modulus 2^S vs the scan bound
    esc_hist[min(S, 60)] += 1
    if (1 << S) <= X: esc_shared += 1
    else: esc_private += 1
    m += 2

print(f"scan to X = {X}")
print(f"Track B: global max L_1(m)/m = {bestratio:.6f}")
print("  ratio records (m, L_1, ratio):")
for mm, L, r in ratio_records:
    print(f"    {mm:9d}  {L:4d}  {r:.6f}")
print(f"  seeds with L_1(m) > m: {len(gt1)} -> {gt1[:12]}{' ...' if len(gt1) > 12 else ''}")
print(f"  seeds with L_1(m) > m/2: {gt_half}")
print("\n  shellwise: k, 2^k, M_k = max L_1, H_k = max L_1/m, M_k/k")
for k in sorted(Mk):
    if 2 ** k <= X:
        print(f"    {k:3d}  {2**k:11d}   {Mk[k]:4d}   {Hk[k]:.6f}   {Mk[k]/k if k else 0:6.2f}")
print(f"\nTrack A: escape-class precision among odd m <= {X}")
print(f"  seeds whose escape class modulus 2^S <= X (shared class): {esc_shared} "
      f"({esc_shared/(esc_shared+esc_private):.4f})")
print(f"  seeds needing a private class (2^S > X): {esc_private} "
      f"({esc_private/(esc_shared+esc_private):.4f})")
tot = esc_shared + esc_private
cum = 0
print("  distribution of escape modulus exponent S (cumulative fraction):")
for S in sorted(esc_hist):
    cum += esc_hist[S]
    if S % 2 == 0 and S <= 40:
        print(f"    S <= {S:2d}: {cum/tot:.4f}")
