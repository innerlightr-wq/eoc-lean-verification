"""GATE 36 calibration: within a fixed shell (N, S) the map word -> chi_N is injective
(repo `realizerCongruence`; the transport note's D.7 calls it the coarse residue map).
chi_N is odd in [1, 2^S), so at most 2^{eps N - 1} words can have chi_N < 2^{eps N}.
Shell size = C(S-1, N-1) compositions.  Hence the exceptional fraction is exponentially small.
"""
import math, itertools
from math import comb
alpha = math.log2(3)

def chi_of(S_list, N):
    SN = S_list[N]
    C = sum(3**(N-1-i) * (1 << S_list[i]) for i in range(N))
    return (-C * pow(pow(3, N, 1 << SN), -1, 1 << SN)) % (1 << SN)

print("injectivity of word -> chi_N within a fixed shell (N, S)")
print(f"{'N':>3} {'S':>3} {'#words':>8} {'#distinct chi':>14} {'injective?':>11} {'min log2 chi/S':>15}")
for (N, S) in [(5,8),(6,9),(6,10),(7,11),(8,12),(8,13),(9,14)]:
    words = [c for c in itertools.product(range(1,6), repeat=N) if sum(c)==S]
    chis = []
    mn = 1.0
    for c in words:
        Sl=[0]
        for d in c: Sl.append(Sl[-1]+d)
        x = chi_of(Sl, N); chis.append(x)
        if x > 0: mn = min(mn, math.log2(x)/S)
    ok = len(set(chis)) == len(chis)
    print(f"{N:>3} {S:>3} {len(words):>8} {len(set(chis)):>14} {str(ok):>11} {mn:>15.4f}"
          f"   (shell C(S-1,N-1)={comb(S-1,N-1)})")

print("\nasymptotic calibration at the confined shell S = alpha N:")
h = -( (1/alpha)*math.log2(1/alpha) + (1-1/alpha)*math.log2(1-1/alpha) )
print(f"  H2(1/alpha) = {h:.6f};  log2 C(S-1,N-1) ~ alpha*H2(1/alpha)*N = {alpha*h:.6f} N")
print(f"  bad words (chi < 2^{{eps N}}) <= 2^{{eps N - 1}}, so bad fraction <= 2^{{(eps - {alpha*h:.4f})N}}")
print(f"  => exponentially small for every eps < {alpha*h:.4f}")
print(f"  Open Problem E only needs log2 r >= I0*N with I0 = alpha(1-H2) = {alpha*(1-h):.6f}")
print(f"  So the TYPICAL word beats the target by a factor {alpha*h/(alpha*(1-h)):.1f}; the whole")
print(f"  difficulty of Open Problem C/E is the worst case, which pigeonhole cannot reach.")
