"""Deterministic worst case of bad shape blocks over ALL confined class paths (max-plus DP, exact).

Class path = even prefix sums S_0 = 0 < S_2 < ... < S_J = sg, S_{2r} <= floor(2r alpha).  Pair block r (pair sum
u = S_{2r+2} - S_{2r}) has SHAPE if 2 <= |B_r| <= N0 (B_r = {x : S_{2r} < x < S_{2r+2}, x <= floor((2r+1) alpha)});
a shape block is BAD if no admissible x with x+1 in B_r has a Tao-white cell (m - x, 2r+2) at eta = 1/54.
For theta in a grid, computes  max over class paths of  (#bad - theta * #shape)  and the (#bad, #shape) of a maximizer.
If this max stays O(1) as J grows then every confined class path has #good >= (1 - theta) #shape - O(1).
usage: python3 block_worst.py J N0"""
import math, sys

AL = math.log2(3)
J, N0 = int(sys.argv[1]), int(sys.argv[2]); assert J % 2 == 0
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
R = J // 2
white = []
for r in range(R):
    b = 2 * r + 2; q = 3 ** b; x0 = b - 1; rr = pow(2, -(m - x0), q); row = {}
    for x in range(x0, top[2 * r + 1] + 2):
        y = rr if rr <= q // 2 else rr - q
        row[x] = 54 * abs(y) >= q; rr = rr * 2 % q
    white.append(row)

def run(theta):
    NEG = None
    V = {sg: (0.0, 0, 0)}                               # value-to-go from (2r, S): (score, #bad, #shape)
    for r in range(R - 1, -1, -1):
        cap = top[2 * r + 1]; newV = {}
        for S in range(2 * r, top[2 * r] + 1):
            best = None
            for S2 in range(S + 2, top[2 * r + 2] + 1):
                if S2 not in V: continue
                hi = min(S2 - 1, cap); nB = hi - S
                if nB <= 0: continue
                shape = 2 <= nB <= N0
                bad = shape and not any(white[r].get(x, False) for x in range(S + 1, hi))
                sc, nb, ns = V[S2]
                cand = (sc + (1.0 if bad else 0.0) - (theta if shape else 0.0), nb + bad, ns + shape)
                if best is None or cand[0] > best[0]: best = cand
            if best is not None: newV[S] = best
        V = newV
    return V[0]

print(f"J={J} N0={N0}: pair blocks R={R}")
for theta in (0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 1.0):
    sc, nb, ns = run(theta)
    print(f"  theta={theta}: max(#bad - theta #shape) = {sc:.2f}   maximizer: #bad={nb}, #shape={ns}"
          + (f", bad fraction {nb/ns:.3f}" if ns else ""))
