"""Exceptional 3-block states under the uniform confined prefix measure (top shell):
fraction of blocks with |C| = 1 (W == 1), with |C| < |Q_u| (headroom-truncated), and E[log2 |C|]; plus |V| for c=1, j0=60."""
import math
al = math.log2(3)
def run(c, J):
    b = [math.floor(c + j * al) for j in range(J + 4)]; sig = b[J]
    pre = [dict() for _ in range(J + 1)]; pre[0][0] = 1
    for i in range(J):
        for S, v in pre[i].items():
            for d in range(1, b[i + 1] - S + 1): pre[i + 1][S + d] = pre[i + 1].get(S + d, 0) + v
    suf = [dict() for _ in range(J + 1)]; suf[J][sig] = 1
    for i in range(J - 1, -1, -1):
        for S in range(0, b[i] + 1):
            v = sum(suf[i + 1].get(S + d, 0) for d in range(1, b[i + 1] - S + 1))
            if v: suf[i][S] = v
    P = pre[J][sig]; triv = trunc = elog = 0.0; nbl = 0
    for i in range(0, J - 2, 3):
        nbl += 1
        for S, v in pre[i].items():
            if not suf[i].get(S): continue
            for u in range(3, b[i + 3] - S + 1):
                ce = suf[i + 3].get(S + u, 0)
                if not ce: continue
                C = sum(1 for S1 in range(S + 1, min(b[i + 1], S + u - 2) + 1) for S2 in range(S1 + 1, min(b[i + 2], S + u - 1) + 1))
                if C == 0: continue
                w = v * C * ce / P
                if C == 1: triv += w
                if C < math.comb(u - 1, 2): trunc += w
                elog += w * math.log2(C)
    return triv / nbl, trunc / nbl, elog / nbl
for c, J in [(0, 30), (0, 60), (0, 120), (0, 240), (1, 120), (2, 120)]:
    tr, tc, el = run(c, J)
    print(f"c={c} j0={J}: trivial blocks (|C|=1) {tr:.3f}   headroom-truncated {tc:.3f}   E log2|C| = {el:.3f} bits/block ({el/3:.3f}/step)")
# |V| for c=1 geometry j0=60
c = 1; b = [math.floor(c + j * al) for j in range(300)]; J = 60; sig = b[J]; K = sig + 1; N = math.floor(0.7 * K); t = b[N] - sig
cur = {0: 1}
for i in range(N - J):
    new = {}
    for S, v in cur.items():
        for d in range(1, t + 1):
            if sig + S + d <= b[J + i + 1]: new[S + d] = new.get(S + d, 0) + v
    cur = new
print(f"c=1 j0=60: sigma={sig} K={K} N={N} t={t} |V|={cur.get(t,0)}")
