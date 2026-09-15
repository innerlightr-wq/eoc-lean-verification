"""Part XI-XIII check: for a deep block (3^{n} > |I|), is 27 | e_r a function of lam mod 27^k?  e_r = cres(lam*3^{-n} mod 2^M).
Exact: 27^k | e_r  <=>  lam = -2^M f (mod 3^{n+3k}) with f = cres_3(-lam 2^{-M} mod 3^n) -- modulus 3^{n+3k}, not 27^k."""
import math
m, t = 107, 11; H = 1 << t
for (n, M) in [(6, 97), (15, 83), (30, 59), (45, 35)]:
    w = pow(3, -n, 1 << M)
    def e(l):
        x = (l * w) % (1 << M); return x - (1 << M) if x > (1 << (M - 1)) else x
    for k in (1, 2):
        mod = 27 ** k; frac = []
        for a in range(1, mod):
            ls = [l for l in range(a, H, mod)]
            if ls: frac.append(sum(1 for l in ls if e(l) % 27 == 0) / len(ls))
        mixed = sum(1 for f in frac if 0 < f < 1)
        print(f"n={n:2d} M={M} 3^n {'<=' if 3 ** n <= H else '> '} 2^t: classes lam mod 27^{k}: {mixed}/{len(frac)} mixed; overall P(27|e)={sum(1 for l in range(1, H) if e(l) % 27 == 0) / (H - 1):.4f}")
