"""GATE 34 rows I must not assert without checking: EVENTUALLY PERIODIC and ONE-DEFECT.

Claim (report SS I, AF): such words have a FIXED rational anchor -Z = P/Q with |P|,|Q| bounded
in N, hence a bounded-height relation 2^{S_N} | P - Q*chi, hence rho_N -> 0.

Test: rationally reconstruct (P,Q) from chi_N at one depth, then CHECK the same (P,Q) works
at every larger depth.  If the height stays fixed while S_N grows, rho_N -> 0 is confirmed.
"""
import math
from fractions import Fraction
alpha = math.log2(3)

def C_of(S,N): return sum(3**(N-1-i) * (1 << S[i]) for i in range(N))
def chi_of(S,N):
    SN=S[N]; C=C_of(S,N)
    return (-C * pow(pow(3,N,1<<SN), -1, 1<<SN)) % (1<<SN)

def ratrecon(x, M):
    """find small P,Q with P = Q*x mod M, via the extended-Euclid / lattice method"""
    a0,a1 = M, x % M
    s0,s1 = 0, 1
    lim = math.isqrt(M)
    while a1 > lim:
        q = a0//a1
        a0,a1 = a1, a0-q*a1
        s0,s1 = s1, s0-q*s1
    return a1, s1          # a1 = s1*x mod M, i.e. P = a1, Q = s1 (P - Q*x = 0 mod M)

def build(word, N):
    S=[0]
    for k in range(N): S.append(S[-1]+word[k%len(word)] if False else 0)
    return S

def build_word(seq):
    S=[0]
    for d in seq: S.append(S[-1]+d)
    return S

print("EVENTUALLY PERIODIC:  preperiod P0, then period B repeated")
for P0, Bl in [((3,1), (1,2)), ((2,2,3), (2,1,1,2)), ((1,1,1,4), (1,2))]:
    print(f"  preperiod {P0}  period {Bl}")
    ref = None
    for reps in [6, 10, 14, 18]:
        seq = list(P0) + list(Bl)*reps
        N=len(seq); S=build_word(seq); SN=S[N]
        chi = chi_of(S,N)
        P,Q = ratrecon(chi, 1<<SN)
        h = math.log2(max(abs(P),abs(Q))) if max(abs(P),abs(Q))>0 else 0
        ok = (P - Q*chi) % (1<<SN) == 0
        frac = Fraction(P,Q) if Q!=0 else None
        if ref is None: ref = frac
        print(f"    reps={reps:3d} N={N:3d} S_N={SN:4d}  P/Q={str(frac):>14}  h={h:6.2f}  "
              f"h/S_N={h/SN:.4f}  relation holds: {ok}  same anchor as first: {frac==ref}")

print("\nONE-DEFECT: periodic word with a single digit changed near the start")
for Bl, pos, newd in [((1,2), 3, 3), ((2,1,1,2), 5, 1)]:
    print(f"  period {Bl}, defect at index {pos} -> {newd}")
    ref=None
    for reps in [6, 10, 14, 18]:
        seq = [Bl[k%len(Bl)] for k in range(len(Bl)*reps)]
        seq[pos] = newd
        N=len(seq); S=build_word(seq); SN=S[N]
        chi=chi_of(S,N); P,Q = ratrecon(chi, 1<<SN)
        h=math.log2(max(abs(P),abs(Q))) if max(abs(P),abs(Q))>0 else 0
        ok=(P-Q*chi)%(1<<SN)==0
        frac=Fraction(P,Q) if Q!=0 else None
        if ref is None: ref=frac
        print(f"    reps={reps:3d} N={N:3d} S_N={SN:4d}  P/Q={str(frac):>16}  h={h:6.2f}  "
              f"h/S_N={h/SN:.4f}  relation holds: {ok}  same anchor as first: {frac==ref}")

print("\nCONTROL - the same reconstruction on a STURMIAN (aperiodic) word:")
ref=None
for N in [16, 32, 64, 96]:
    S=[math.floor(alpha*j) for j in range(N+1)]; SN=S[N]
    chi=chi_of(S,N); P,Q=ratrecon(chi, 1<<SN)
    h=math.log2(max(abs(P),abs(Q))) if max(abs(P),abs(Q))>0 else 0
    frac=Fraction(P,Q) if Q!=0 else None
    if ref is None: ref=frac
    print(f"    N={N:3d} S_N={SN:4d}  h={h:7.2f}  h/S_N={h/SN:.4f}  same anchor as first: {frac==ref}")
print("  -> the reconstructed anchor CHANGES with N and h/S_N stays ~1/2: no fixed rational anchor.")
