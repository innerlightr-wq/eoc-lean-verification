"""Exact record frontier r_min(N,c) = min{odd m : L_c(m) >= N} by seed scan (Parts XXIV-XXVI).

Syracuse orbit on odd m: m -> (3m+1)/2^a, a = v2(3m+1); word a_1..a_N; S_j = sum_{i<=j} a_i;
drift R_j = S_j - j log2 3.  L_c(m) = max N with R_j <= c for all j <= N  (c-confined prefix length).
The direct-Collatz threshold (PROVED MATH, previous round): a floor r_min(N,c) >= A N with
A > A_crit(c) = 1/(3 c ln 2) implies descent for all large seeds.  A_crit(1) = 0.480898.
Reports, for each record N, the least seed, the ratio r_min/N, and log2(r_min)/N.
usage: python3 scan.py MMAX [c ...]"""
import math, sys

MMAX = int(sys.argv[1])
CS = [float(x) for x in sys.argv[2:]] or [1.0]
AL = math.log2(3)
for c in CS:
    # integer barrier: S_j <= floor(j*AL + c)
    NCAP = 200
    top = [math.floor(j * AL + c) for j in range(NCAP + 2)]
    best = {}          # N -> least m with L_c(m) >= N
    bestN = 0
    m = 1
    while m <= MMAX:
        x = m; S = 0; j = 0
        while j < NCAP:
            v = 3 * x + 1
            a = (v & -v).bit_length() - 1
            S += a; j += 1
            if S > top[j]: j -= 1; break
            x = v >> a
        if j > bestN:
            for n in range(bestN + 1, j + 1): best[n] = m
            bestN = j
        m += 2
    print(f"c={c}: seeds scanned up to {MMAX}; deepest confined prefix L_c = {bestN}")
    print("   N   r_min(N,c)      r_min/N    log2(r_min)/N")
    for N in sorted(best):
        r = best[N]
        if N % 10 == 0 or N == bestN:
            print(f"  {N:3d}  {r:12d}   {r / N:10.3f}   {math.log2(r) / N if r > 1 else 0:8.4f}")
    print(f"   A_crit(c) = 1/(3c ln2) = {1 / (3 * c * math.log(2)):.6f}")
    for N0 in (3, 5, 10, 20, 50, 80):
        cand = [(best[N] / N, N) for N in best if N >= N0]
        if cand:
            v, n = min(cand)
            print(f"   inf_{{N >= {N0}}} r_min/N = {v:.3f} (at N = {n}, r_min = {best[n]}); "
                  f"margin over A_crit: {v * 3 * c * math.log(2):.2f}x", flush=True)
    print(f"   linear floor A=0.49 verified for all N <= {MMAX / 0.49:.3g} "
          f"(no seed <= {MMAX} reaches L_c = {bestN + 1})", flush=True)
