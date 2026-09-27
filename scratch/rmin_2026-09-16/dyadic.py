"""Dyadic frontier: r_min(2^k,1) vs 2^k, and max L_1(m)/m (Parts XLIX-LII, LXI-LXII)."""
import math, sys
MMAX = int(sys.argv[1]); c = 1.0; AL = math.log2(3)
NCAP = 300; top = [math.floor(j * AL + c) for j in range(NCAP + 2)]
best = {}; bestN = 0; maxratio = (0.0, 0); m = 1
while m <= MMAX:
    x = m; S = 0; j = 0
    while j < NCAP:
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a; j += 1
        if S > top[j]: j -= 1; break
        x = v >> a
    if j > bestN:
        for n in range(bestN + 1, j + 1): best[n] = m
        bestN = j
    if j / m > maxratio[0]: maxratio = (j / m, m, j)
    m += 2
print(f"seeds <= {MMAX}: deepest L_1 = {bestN}")
print("  k   2^k      r_min(2^k,1)        holds 2^k <= r_min?")
for k in range(1, 26):
    N = 2 ** k
    if N <= bestN: r = best[N]; note = "exact"
    elif N <= MMAX: r = f"> {MMAX}"; note = "from scan exhaustiveness"
    else: r = "?"; note = "beyond verified range"
    ok = (isinstance(r, int) and r >= N) or (isinstance(r, str) and r.startswith(">") and N <= MMAX)
    print(f"  {k:2d}  {N:8d}   {str(r):>12}   {'YES' if ok else ('NO' if isinstance(r,int) else '?')}   ({note})")
print(f"  max L_1(m)/m over odd m <= {MMAX}: {maxratio[0]:.4f} at m = {maxratio[1]} (L_1 = {maxratio[2]})")
print(f"  A=1 form needs L_1(m) < m; A=1/2 form needs L_1(m) < 2m; A_crit needs L_1(m) < 2.079 m")
fits = [(N, best[N]) for N in sorted(best) if N >= 20]
if fits:
    import statistics
    sl = [math.log2(r) / N for N, r in fits]
    print(f"  log2(r_min)/N over N >= 20: min {min(sl):.4f} max {max(sl):.4f} (exponential growth)")
