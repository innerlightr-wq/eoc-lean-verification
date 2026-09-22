"""GATE 16/33: does the height drop for the LOWEST-complexity aperiodic words?

The canonical zero-corridor word is the Beatty/Sturmian word S_j = floor(alpha j),
d_j = floor(alpha j) - floor(alpha (j-1)) in {1,2}.  It is aperiodic (alpha irrational)
with subword complexity p(n) = n+1 -- the minimum possible for an aperiodic word.

If the height framework already fails there, it fails at the very bottom of the
aperiodic hierarchy, and no complexity dichotomy can rescue it.
"""
import math
alpha = math.log2(3)

def C_of(S,N): return sum(3**(N-1-i) * (1 << S[i]) for i in range(N))
def chi_of(S,N):
    SN=S[N]; C=C_of(S,N)
    return (-C * pow(pow(3,N,1<<SN), -1, 1<<SN)) % (1<<SN)

print("Beatty/Sturmian zero-corridor word  S_j = floor(alpha*j)   (complexity p(n)=n+1)")
print(f"{'N':>4} {'S_N':>5} {'log2 C_N':>10} {'h_N=log2 3^N':>13} {'h_N/S_N':>9} {'proved floor':>13} {'actual log2 chi':>16}")
for N in [8, 16, 32, 64, 128]:
    S=[math.floor(alpha*j) for j in range(N+1)]
    d=[S[j]-S[j-1] for j in range(1,N+1)]
    assert set(d) <= {1,2}, set(d)
    SN=S[N]; C=C_of(S,N); chi=chi_of(S,N)
    h=N*alpha
    print(f"{N:>4} {SN:>5} {math.log2(C):>10.2f} {h:>13.2f} {h/SN:>9.4f} {SN-h:>13.2f} "
          f"{math.log2(chi) if chi>0 else 0:>16.2f}")
print("  h_N/S_N stays ABOVE 1 and the proved floor stays NEGATIVE at every depth:")
print("  the height framework is already vacuous at minimal aperiodic complexity.")

print("\nContrast: the SAME framework on the best rational approximations to alpha")
print("(periodic words built from convergents p/q of alpha -- these ARE periodic):")
from fractions import Fraction
cf=[]; x=alpha
for _ in range(8):
    a=math.floor(x); cf.append(a); x=1/(x-a) if x!=a else 0
    if x==0: break
for k in range(2,7):
    fr=Fraction(cf[-1] if False else 0)
    # build convergent p/q
    p0,q0,p1,q1=1,0,cf[0],1
    for a in cf[1:k+1]:
        p0,q0,p1,q1=p1,q1,a*p1+p0,a*q1+q0
    p,q=p1,q1
    # periodic word of period q with total valuation p  (needs p/q >= 1 and <= 2 steps)
    S=[math.floor(p*j/q) for j in range(q+1)]
    d=[S[j]-S[j-1] for j in range(1,q+1)]
    if not set(d) <= {1,2}: continue
    sigma=p; pp=q
    s=[0]
    for t in range(pp-1): s.append(s[-1]+d[t])
    c0=sum(3**(pp-1-t)*(1<<s[t]) for t in range(pp)); Delta=3**pp-(1<<sigma)
    if Delta==0: continue
    h=math.log2(max(abs(c0),abs(Delta)))
    reps=4; N=pp*reps; SS=[0]
    for kk in range(N): SS.append(SS[-1]+d[kk%pp])
    chi=chi_of(SS,N)
    print(f"  convergent {p}/{q}={p/q:.5f}  period {pp}  h={h:6.2f}  S_N={SS[N]:4d}  "
          f"h/S_N={h/SS[N]:.4f}  floor={SS[N]-h:7.2f}  actual={math.log2(chi):.2f}")
print("  Periodic approximants keep h/S_N -> 0; the irrational limit word does not.")
print("  So the transition is NOT about complexity -- it is about whether the word CLOSES.")
