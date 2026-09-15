"""E_P 2^{-r(P)} = (#swap classes)/|P| for c-confined prefixes of length j0 at the top shell (pairs (2k,2k+1)).
This is the full-group value of the class-averaged swap-cube L^2 bound; its rate -log2(.)/(2 j0) is the
amplitude rate the swap-cube route delivers if interval averages match full-group averages."""
import math
al = math.log2(3)
def run(c, J, gap=0):
    b = [math.floor(c + j * al) for j in range(J + 3)]; sig = b[J] - gap
    cnt = [dict() for _ in range(J + 1)]; g = [dict() for _ in range(J + 1)]
    cnt[J][sig] = 1.0; g[J][sig] = 1.0
    i = J
    if J % 2 == 1:
        i = J - 1
        for S in range(0, b[i] + 1):
            v = sum(cnt[J].get(S + d, 0) for d in range(1, b[J] - S + 1))
            if v: cnt[i][S] = v; g[i][S] = v
    i -= 2
    while i >= 0:
        for S in range(0, b[i] + 1):
            vc = vg = 0.0
            for d in range(1, b[i + 1] - S + 1):
                for e in range(1, b[i + 2] - S - d + 1):
                    x = cnt[i + 2].get(S + d + e, 0)
                    if not x: continue
                    vc += x
                    sw = d != e and S + e <= b[i + 1]
                    vg += g[i + 2][S + d + e] * (0.5 if sw else 1.0)
            if vc: cnt[i][S] = vc; g[i][S] = vg
        i -= 2
    P = cnt[0][0]; C = g[0][0]
    return P, C
need = 0.0911
for c, J in [(0, 30), (0, 60), (0, 100), (0, 150), (0, 200), (0, 300), (0, 400), (1, 200), (2, 200)]:
    P, C = run(c, J)
    rate = -math.log2(C / P) / (2 * J)
    print(f"c={c} j0={J}: log2|P|={math.log2(P):.1f}  log2 #classes={math.log2(C):.1f}  E 2^-r = 2^{math.log2(C/P):.1f}  -> amplitude rate {rate:.4f} bits/step (need {need})")
