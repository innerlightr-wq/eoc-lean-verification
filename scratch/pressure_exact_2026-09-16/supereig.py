"""Super-eigenvector test for the odd-dark class operator with state-only weights h(l,x) = beta^(sigma-x).
Certificate (same mechanism as ShapeCertificate): sum_P s^N <= beta^sigma * prod_l M_l, with
M_l = max_x sum_y W_l(x,y) beta^{-(y-x)};  pressure bound = (log2 of that - log2|shellP|)/j.
Exact rational beta = 27/10 (close to alpha/(alpha-1) = 2.7095); all sums exact Fractions."""
import sys, math
from fractions import Fraction as Fr
from pexact import Instance, barrier, log2ratio

def bound(I, s, beta):
    top = I.top; tot = 0.0; worst = []
    for r in range(I.R):
        cap = top[2 * r + 1]; H = I.H[r]; best = Fr(0)
        for x in range(2 * r, top[2 * r] + 1):
            acc = Fr(0)
            for y in range(x + 2, top[2 * r + 2] + 1):
                v = min(y - 1, cap)
                if v - 1 < x: continue
                hv = H[v - 1]; W = (v - x) + (s - 1) * (hv - H[x])
                acc += W * beta ** (-(y - x))
            best = max(best, acc)
        lb = math.log2(best.numerator) - math.log2(best.denominator)
        tot += lb; worst.append(lb)
    return tot, worst

j = int(sys.argv[1]); lam = int(sys.argv[2]); t = j // 6
beta = Fr(27, 10)
I = Instance(j, t, lam=lam, D=108, mode='auto')
Z1 = I.moment(1); Z3 = I.moment(3)
for s in (1, 3):
    tot, worst = bound(I, s, beta)
    b = (tot + I.sg * math.log2(27 / 10) - math.log2(Z1)) / j
    print(f"j={j} lam={lam} s={s}: state-only certificate bound {b:.4f} bits/step "
          f"(exact pressure {log2ratio(Z3, Z1)/j if s == 3 else 0:.4f}); mean log2 M_l = {tot/I.R:.4f}, max {max(worst):.4f}")
