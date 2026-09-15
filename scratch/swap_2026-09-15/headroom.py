"""Parts VIII-IX: under the uniform measure on c-confined prefixes of length j0 ending at the top shell,
 (a) expected number of steps spent at headroom k = b(i+1) - S_i, k = 1..5 (total over the prefix),
 (b) expected number of swappable pairs (pairs (2k,2k+1) with d != e and both orders admissible),
 (c) min over states (i even, headroom >= 3, i <= j0-12) of P(next pair is (1,2) or (2,1) | S_i).
Exact rational-free DP with Python floats on counts (big ints)."""
import math
al = math.log2(3)
def run(c, J):
    b = [math.floor(c + j * al) for j in range(J + 3)]; sig = b[J]
    pre = [dict() for _ in range(J + 1)]; pre[0][0] = 1
    for i in range(J):
        for S, v in pre[i].items():
            for d in range(1, b[i + 1] - S + 1): pre[i + 1][S + d] = pre[i + 1].get(S + d, 0) + v
    suf = [dict() for _ in range(J + 1)]; suf[J][sig] = 1
    for i in range(J - 1, -1, -1):
        for S in range(0, b[i] + 1):
            v = sum(suf[i + 1].get(S + d, 0) for d in range(1, b[i + 1] - S + 1))
            if v: suf[i][S] = v
    P = pre[J][sig]
    occ = [0.0] * 8
    for i in range(J):
        for S, v in pre[i].items():
            k = b[i + 1] - S
            if 1 <= k <= 7 and suf[i].get(S, 0): occ[k] += v * suf[i][S] / P
    swp = 0.0; minp = 1.0
    for i in range(0, J - 1, 2):
        for S, v in pre[i].items():
            cs = suf[i].get(S, 0)
            if not cs: continue
            w = v * cs / P; ps = 0.0; p12 = 0.0
            for d in range(1, b[i + 1] - S + 1):
                for e in range(1, b[i + 2] - S - d + 1):
                    q = suf[i + 2].get(S + d + e, 0) / cs
                    if d != e and S + e <= b[i + 1]: ps += q
                    if (d, e) in ((1, 2), (2, 1)): p12 += q
            swp += w * ps
            if b[i + 1] - S >= 3 and i <= J - 12: minp = min(minp, p12)
    return occ, swp, minp
for c, J in [(0, 30), (0, 60), (0, 100), (0, 150), (0, 200), (0, 300), (1, 150), (2, 150)]:
    occ, swp, minp = run(c, J)
    print(f"c={c} j0={J}: E#steps at headroom 1..5 = " + " ".join(f"{occ[k]:.2f}" for k in range(1, 6))
          + f"   E#swappable pairs = {swp:.1f} of {J//2} ({swp/(J//2):.3f})   min P((1,2)|(2,1) | headroom>=3) = {minp:.4f}")
