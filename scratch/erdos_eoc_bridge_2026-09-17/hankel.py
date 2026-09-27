"""Part XXVIII: can n -> digit_D(2^{-n} mod 3^{D+1}) be computed by a SMALL weighted automaton / matrix product
state reading the digits of the exponent n?  By the Carlyle-Paz / Fliess theorem, the minimal dimension of a linear
representation (over a field) reading n in mixed radix (2,3,3,...,3), low digit first, is >= rank of the Hankel matrix
H_i[p][s] = f(p + 2*3^i*s)  (p < 2*3^i, s < 3^{D-i}) at every cut i.  Ranks over GF(P) are lower bounds for ranks
over Q (integer matrices).  f = indicator [digit_D = c] (c = 0,1,2) and f = [top three balanced digits zero] (black)."""
import sys
PR = 2_147_483_647
def rank_mod(M):
    M = [row[:] for row in M]; r = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % PR: piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], PR - 2, PR)
        M[r] = [x * inv % PR for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(a - f * b) % PR for a, b in zip(M[i], M[r])]
        r += 1
    return r
for D in range(3, 10):
    mod = 3 ** (D + 1); per = 2 * 3 ** D
    inv2 = pow(2, -1, mod)
    vals = [0] * per; x = 1
    for n in range(per):
        vals[n] = x; x = x * inv2 % mod
    dig = [(v // 3 ** D) % 3 for v in vals]
    H = (mod - 1) // 2
    black = [int(((v + H) % mod) // 3 ** (D - 2) == 13) for v in vals]   # digits D-2..D of (v - 1/2) are 111 (b = D+1)
    out = [f"D={D}:"]
    for i in range(0, D):
        P_ = 2 * 3 ** i; S_ = 3 ** (D - i)
        if P_ * S_ != per: continue
        if min(P_, S_) > 800: out.append(f"i={i}:skip"); continue
        rk = []
        for name, f in (("d=0", [int(d == 0) for d in dig]), ("black", black)):
            Mx = [[f[p + P_ * s] for s in range(S_)] for p in range(P_)]
            if P_ > S_: Mx = [list(col) for col in zip(*Mx)]
            rk.append(rank_mod(Mx))
        out.append(f"i={i}:rk{rk}/min{min(P_, S_)}")
    print(" ".join(out)); sys.stdout.flush()
