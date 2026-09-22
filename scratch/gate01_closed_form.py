"""GATE 0/1: reduce the cancellation object to closed form.

Claimed derivation, to be tested against the paper's definitions computed directly:

  A_{j,inf} = 2^{-S_j} ( Z - 3^{-j} C_j ),   Z := sum_{i>=0} 2^{S_i} 3^{-(i+1)}
  T_j       = 2^{-S_j} ( -3^{-j} C_j - chi_j )
  X_j       = T_j - A_{j,inf} = -(chi_j + Z) / 2^{S_j}
  Z         = -n_0                              (the seed, as a 2-adic integer)
  => chi_j  = n_0 mod 2^{S_j}
  => X_j    = floor( n_0 / 2^{S_j} )
  => M_j    = v2( floor(n_0 / 2^{S_j}) )  =  zero-run of n_0 starting at bit S_j
  => M_j    = infinity  as soon as  2^{S_j} > n_0
"""
import math

def v2(n):
    if n == 0: return None
    r = 0
    while n % 2 == 0: n //= 2; r += 1
    return r

def check(n0, N=60, pad=400):
    ds = [0]; ms = [n0]; m = n0
    for _ in range(N):
        t = 3*m+1; d = v2(t); m = t >> d
        ds.append(d); ms.append(m)
    S = [0]*(N+1)
    for j in range(1, N+1): S[j] = S[j-1] + ds[j]
    P = S[N] + pad; M2 = 1 << P
    inv3 = pow(3, -1, M2); inv3p = [pow(inv3, k, M2) for k in range(N+2)]
    C = [0]*(N+1)
    for j in range(N): C[j+1] = 3*C[j] + (1 << S[j])

    # Z computed directly from its defining series, to the available precision
    Z = 0
    for i in range(N+1):
        if S[i] >= P: break
        Z = (Z + (1 << S[i]) * inv3p[i+1]) % M2
    err_Z = (Z + n0) % (1 << min(S[N], P-5))
    out = []
    for j in range(1, N):
        Sj = S[j]
        if Sj + 40 > P: break
        xi = (-C[j] * inv3p[j]) % M2
        chi = xi % (1 << Sj)
        T = xi >> Sj
        # A_{j,inf} from its OWN defining series (paper's definition), to precision 2^lim
        A = 0; D = 0
        for r in range(0, N-j):
            A = (A + (1 << D) * inv3p[j+1+r]) % M2
            D += ds[j+1+r]
            if D >= P - Sj: break
        lim = min(P - Sj, D)
        Xpaper = (T - A) % (1 << lim)
        Xclaim = (n0 >> Sj)                      # claimed closed form
        agree = (Xpaper % (1 << lim)) == (Xclaim % (1 << lim))
        chi_ok = (chi == n0 % (1 << Sj))
        out.append((j, Sj, agree, chi_ok, Xpaper, Xclaim, lim))
    return err_Z, out

bad_Z = bad_X = bad_chi = 0; tot = 0; tested = 0
for n0 in range(1, 4000, 2):
    errZ, rows = check(n0, N=45)
    tested += 1
    if errZ != 0: bad_Z += 1; print("Z mismatch", n0, errZ)
    for (j, Sj, agree, chi_ok, Xp, Xc, lim) in rows:
        tot += 1
        if not agree: bad_X += 1
        if not chi_ok: bad_chi += 1
print(f"seeds tested: {tested}")
print(f"Z = -n_0                 : mismatches {bad_Z}")
print(f"chi_j = n_0 mod 2^S_j    : mismatches {bad_chi} / {tot}")
print(f"X_j = floor(n_0/2^S_j)   : mismatches {bad_X} / {tot}")

# consequence: how many failures does a genuine orbit have?
print("\nfailures along a genuine orbit (K_j != 0 <=> M_j < d_{j+1}):")
print(f"{'n0':>7} {'log2 n0':>8} {'#j with S_j<=log2 n0':>21} {'#failures':>10} {'last failure j':>15}")
for n0 in [7, 27, 97, 871, 6171, 77031, 837799]:
    ds = [0]; m = n0
    for _ in range(400):
        t = 3*m+1; d = v2(t); m = t >> d; ds.append(d)
    S = [0]
    for j in range(1, len(ds)): S.append(S[-1] + ds[j])
    nf = 0; last = None; nfin = 0
    for j in range(1, 300):
        if (n0 >> S[j]) == 0: break          # M_j = infinity from here on
        nfin += 1
        Mj = v2(n0 >> S[j])
        if Mj is not None and Mj < ds[j+1]: nf += 1; last = j
    print(f"{n0:>7} {math.log2(n0):>8.2f} {nfin:>21} {nf:>10} {str(last):>15}")
