"""Occupation statistics of the uniform measure on P_{j0,sigma} (c-confined prefixes, S_{j0}=sigma):
  - forced steps: headroom b(i+1) - S_i = 1 (only digit 1 allowed)
  - swappable pairs (2k+off, 2k+1+off): digits d != e and both orders admissible
  - pair-divergence profile: fraction of ordered pairs (P,Q), P != Q, whose first difference is at step i
Exact big-integer DP."""
import math, sys
al = math.log2(3)
def run(c, J, sig=None, off=0):
    b = [math.floor(c + j * al) for j in range(J + 2)]
    if sig is None: sig = b[J]
    pre = [dict() for _ in range(J + 1)]; pre[0][0] = 1
    for i in range(J):
        for S, v in pre[i].items():
            for d in range(1, b[i + 1] - S + 1): pre[i + 1][S + d] = pre[i + 1].get(S + d, 0) + v
    suf = [dict() for _ in range(J + 1)]; suf[J][sig] = 1
    for i in range(J - 1, -1, -1):
        for S in range(0, b[i] + 1):
            v = sum(suf[i + 1].get(S + d, 0) for d in range(1, b[i + 1] - S + 1))
            if v: suf[i][S] = v
    P = pre[J].get(sig, 0)
    forced = 0.0
    for i in range(J):
        for S, v in pre[i].items():
            if b[i + 1] - S == 1 and suf[i].get(S, 0): forced += v * suf[i][S] / P
    # swappable pairs
    swp = 0.0; npairs = 0
    for i in range(off, J - 1, 2):
        npairs += 1
        for S, v in pre[i].items():
            for d in range(1, b[i + 1] - S + 1):
                for e in range(1, b[i + 2] - S - d + 1):
                    if d != e and S + e <= b[i + 1]:
                        swp += v * suf[i + 2].get(S + d + e, 0) / P
    # divergence profile
    tot = P * (P - 1); prof = []
    for i in range(J):
        acc = 0
        for S, v in pre[i].items():
            cs = [suf[i + 1].get(S + d, 0) for d in range(1, b[i + 1] - S + 1)]
            acc += v * (sum(cs) ** 2 - sum(x * x for x in cs))
        prof.append(acc / tot)
    return P, forced / J, swp / npairs, prof
for c, J in [(0, 30), (0, 60), (0, 100), (0, 200), (1, 100), (2, 100)]:
    P, f, s, prof = run(c, J)
    # late-split mass: fraction of off-diagonal pairs diverging within last L steps
    late = [sum(prof[J - L:]) for L in (1, 2, 4, 8, 16)]
    print(f"c={c} j0={J}: log2|P|={math.log2(P):.2f}  forced-step fraction={f:.4f}  swappable-pair fraction={s:.4f}"
          f"  first-divergence mass in last 1,2,4,8,16 steps: " + " ".join(f"{x:.2e}" for x in late)
          + f"  (early half: {sum(prof[:J//2]):.4f})")
