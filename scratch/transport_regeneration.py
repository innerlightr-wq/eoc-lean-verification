"""Transport / regeneration coordinates on genuine accelerated-Collatz orbits.

Implements the definitions of the transport-deficit note directly:
  xi_j = -C_j 3^{-j}          (Z_2, via residues mod 2^P)
  chi_j = xi_j mod 2^{S_j},   xi_j = chi_j + 2^{S_j} T_j
  K_j(d) = (T_j - 3^{-(j+1)}) mod 2^d
  F_j = S_j - log2 chi_j,  M_j = v2(T_j - A_{j,inf}),  H_j = F_j + M_j
  E_j = S_j - log2 r(D_j),  r(D_j) = m_0 mod 2^{S_j+1}
"""
import math, sys
from fractions import Fraction

def v2(n):
    if n == 0: return None
    r = 0
    while n % 2 == 0: n //= 2; r += 1
    return r

def orbit(m0, N):
    """Return (ds, ms) with ds[1..N] the valuations, ms[0..N] the odd iterates."""
    ds = [0]; ms = [m0]; m = m0
    for _ in range(N):
        t = 3*m + 1; d = v2(t); m = t >> d
        ds.append(d); ms.append(m)
    return ds, ms

def analyse(m0, N, pad=260, verbose=False):
    ds, ms = orbit(m0, N)
    S = [0]*(N+1)
    for j in range(1, N+1): S[j] = S[j-1] + ds[j]
    P = S[N] + pad
    M2 = 1 << P
    inv3 = pow(3, -1, M2)

    # carry C_j:  C_0 = 0, C_{j+1} = 3 C_j + 2^{S_j}
    C = [0]*(N+1)
    for j in range(N): C[j+1] = 3*C[j] + (1 << S[j])

    rows = []
    for j in range(1, N+1):
        Sj = S[j]
        xi = (-C[j] * pow(inv3, j, M2)) % (1 << Sj) if Sj <= P else None
        # need xi mod 2^{S_j} and the tail T_j mod 2^{P-S_j}
        xi_full = (-C[j] * pow(inv3, j, M2)) % M2
        chi = xi_full % (1 << Sj)
        T = (xi_full >> Sj)                      # tail state mod 2^{P-S_j}
        Tprec = P - Sj
        d_next = ds[j+1] if j < N else None
        # exact realizer of the length-j prefix
        r = m0 % (1 << (Sj + 1))
        beta = 1 if r < (1 << Sj) else 0
        # A_{j,m}: sum_{rr=0}^{m-1} 2^{D_rr} 3^{-(j+1+rr)}, D_rr = d_{j+1}+..+d_{j+rr}
        A = 0; D = 0; m_used = 0
        for rr in range(0, N-j):
            A = (A + (1 << D) * pow(inv3, j+1+rr, M2)) % M2
            D += ds[j+1+rr]; m_used += 1
            if D >= Tprec or D > Sj + 200: break
        X = (T - A) % (1 << min(Tprec, D))       # mismatch, valid to precision min(Tprec,D)
        Mj = v2(X); valid_M = (Mj is not None and Mj < min(Tprec, D))
        K = ((T - pow(inv3, j+1, M2)) % (1 << d_next)) if d_next else None
        F = Sj - math.log2(chi) if chi > 0 else None
        E = Sj - math.log2(r) if r > 0 else None
        g = Sj - (r.bit_length() - 1) if r > 0 else None
        rows.append(dict(j=j, S=Sj, d=ds[j], dn=d_next, chi=chi, T=T, Tprec=Tprec,
                         r=r, beta=beta, F=F, E=E, g=g, M=Mj, validM=valid_M,
                         K=K, D=D, A=A))
    return ds, ms, S, rows, M2, inv3

# ---------------------------------------------------------------- checks
def run(seeds, N=60):
    stats = dict(lemma1=0, cor3=0, gap=0, bridge=0, perfect=0, Hcons=0, failmap=0,
                 pos=0, n=0, Gpos=0, Gposdeep=0, minpartial=0.0)
    worst_partial = {}
    Gevents = []
    for m0 in seeds:
        ds, ms, S, rows, M2, inv3 = analyse(m0, N)
        H0 = None; partial = 0.0
        for i, R in enumerate(rows):
            stats['n'] += 1
            Sj, chi, r, beta, F, E, g, Mj = R['S'], R['chi'], R['r'], R['beta'], R['F'], R['E'], R['g'], R['M']
            # Lemma 1: chi odd, 1 <= chi < 2^S  =>  F > 0
            assert chi % 2 == 1 and 1 <= chi < (1 << Sj), (m0, R['j'], 'lemma1')
            assert F > 0
            stats['lemma1'] += 1
            # Corollary 3
            if beta == 1:
                assert abs(E - F) < 1e-9, (m0, R['j'], E, F)
            else:
                assert -1 < E <= 0 + 1e-12, (m0, R['j'], E)
            assert chi == r % (1 << Sj)
            stats['cor3'] += 1
            # discrete gap vs E:  E <= g < E+1
            assert E <= g < E + 1 + 1e-12, (m0, R['j'], E, g)
            stats['gap'] += 1
            if not R['validM']: continue
            H = F + Mj
            # THE BRIDGE: g <= ceil(H)
            assert g <= math.ceil(H - 1e-12), (m0, R['j'], g, H)
            stats['bridge'] += 1
            assert H > 0; stats['pos'] += 1
            if H0 is None: H0 = H
            # one-step budget law
            if i + 1 < len(rows) and rows[i+1]['validM']:
                R2 = rows[i+1]; H2 = R2['F'] + R2['M']
                if R['K'] == 0:
                    assert abs(H2 - H) < 1e-9, (m0, R['j'], 'Hcons', H, H2)
                    stats['Hcons'] += 1
                else:
                    delta = R['dn'] - (R2['F'] - F)
                    G = H2 - H
                    partial += G
                    worst_partial[m0] = min(worst_partial.get(m0, 0.0), partial)
                    # Prop 33 at a genuine FIRST failure (v2(K) == M_j)
                    if v2(R['K']) == Mj:
                        a = R['T'] - R['A']; u = R['K']
                        au = v2(((a >> Mj) - (u >> Mj)) % (1 << 200))
                        if au is not None and au < 190:
                            assert abs(G - (au - delta)) < 1e-9, (m0, R['j'], 'failmap', G, au-delta)
                            stats['failmap'] += 1
                            if G > 0:
                                stats['Gpos'] += 1
                                Gevents.append((m0, R['j'], H, G))
                                if H >= 8: stats['Gposdeep'] += 1
        if H0 is not None and m0 in worst_partial:
            stats['minpartial'] = min(stats['minpartial'], worst_partial[m0] + H0)
    return stats, Gevents

if __name__ == '__main__':
    seeds = [m for m in range(3, 4001, 2)]
    st, Gev = run(seeds, N=45)
    for k, v in st.items(): print(f"{k:12s} {v}")
    print(f"\npositive-G events: {len(Gev)}; max G = {max((g for _,_,_,g in Gev), default=0):.3f}")
    Gev.sort(key=lambda t: -t[3])
    print("top budget-increasing failures (m0, j, H_pre, G):")
    for e in Gev[:8]: print(f"   {e[0]:6d} {e[1]:3d}  H={e[2]:7.3f}  G={e[3]:7.3f}")
