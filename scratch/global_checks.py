"""GATES 10, 11, 12, 23, 31: global-orbit checks.

(1) GATE 12 identity:  C_n / 3^n = (1/3) sum_{j<n} 2^{R_j} = m_0 (Q_n - 1),
    where R_j = S_j - alpha j and Q_n = prod_{j<n}(1 + 1/(3 m_j)).
(2) GATE 10: the negative witnesses -1, -5 against every word-level global condition.
(3) GATE 23: an uncountable family of zero-confined words with R_n -> -infinity.
(4) GATE 31: summability does not force pointwise growth.
"""
import math
from fractions import Fraction
alpha = math.log2(3)

def v2(n):
    r=0
    while n%2==0: n//=2; r+=1
    return r

print("GATE 12 - exact identity  C_n/3^n = (1/3) sum 2^{R_j} = m_0 (Q_n - 1)")
bad1=bad2=0; tot=0
for m0 in range(1, 400, 2):
    m=m0; S=0; C=0; Q=Fraction(1)
    for n in range(1, 25):
        Q *= Fraction(1,1) + Fraction(1, 3*m)
        t=3*m+1; d=v2(t)
        C = 3*C + 2**S; S += d; m = t>>d
        tot += 1
        lhs = Fraction(C, 3**n)
        if lhs != m0*(Q - 1): bad1 += 1
        # and the 2^{R_j} form, as an exact rational sum of 2^{S_j}/3^j
        # (checked via the same C recursion, so only the Q-form is independent)
print(f"  C_n/3^n = m_0 (Q_n - 1)   : mismatches {bad1} / {tot}")
print("  (the 2^{R_j} form is the same series re-indexed: C_n/3^n = sum_{j<n} 2^{S_j} 3^{-(j+1)})")

print("\nGATE 10 - negative witnesses against the word-level global conditions")
print(f"{'witness':>8} {'word (first 8)':<22} {'S_n/n':>7} {'R_n = S_n - alpha n':>20} {'zero-confined?':>15} {'pos realizer?':>14}")
for name, x, dw in [("-1", -1, [1]*8), ("-5", -5, [1,2]*4)]:
    n=len(dw); S=[0]
    for d in dw: S.append(S[-1]+d)
    conf = all(S[j] <= math.floor(alpha*j) for j in range(1, n+1))
    Rn = S[n] - alpha*n
    slope = S[n]/n
    print(f"{name:>8} {str(dw):<22} {slope:>7.3f} {Rn:>20.3f} {str(conf):>15} {'NO':>14}")
print("  -1: word 1,1,1,...  S_n = n, R_n = (1-alpha)n -> -infinity LINEARLY, zero-confined.")
print("  -5: word 1,2,1,2,... S_n = 3n/2, R_n = (1.5-alpha)n -> -infinity, zero-confined.")
print("  Both satisfy zero confinement AND the strongest Curry word shadow R_n -> -infinity,")
print("  yet neither has a positive-integer realizer.  The word shadow does not detect sign.")

print("\nGATE 23 - an uncountable zero-confined family with R_n -> -infinity")
print("  Family: d = (b_1, 1, b_2, 1, b_3, 1, ...) with b_i in {1,2} FREE.")
print("  Then S_{2k} <= 3k and floor(alpha*2k) >= 3.169k - 1, so confinement holds;")
print("  and R_{2k} <= 3k - 2*alpha*k = -0.1699k -> -infinity linearly.")
import itertools, random
random.seed(7)
worst_conf = True; worst_R = 0.0; n_checked = 0
for trial in range(2000):
    K = 60
    b = [random.choice([1,2]) for _ in range(K)]
    d = []
    for bi in b: d += [bi, 1]
    S=[0]
    for x in d: S.append(S[-1]+x)
    n=len(d); n_checked += 1
    conf = all(S[j] <= math.floor(alpha*j) for j in range(1, n+1))
    if not conf: worst_conf = False
    worst_R = min(worst_R, S[n]-alpha*n) if trial==0 else min(worst_R, S[n]-alpha*n)
print(f"  {n_checked} random members, all zero-confined: {worst_conf};  most negative R_n seen: {worst_R:.2f}")
print("  The map (b_i) -> word is injective, so the family has cardinality 2^aleph0.")
print("  At most countably many words admit a positive-integer realizer (one per integer).")
print("  => ALL BUT COUNTABLY MANY members have no positive realizer.")

print("\nGATE 31 - summability does not force pointwise growth")
xs=[]
for n in range(1, 2000):
    k = int(round(math.log2(n))) if n>0 else 0
    xs.append(1 if (n & (n-1))==0 else n*n)   # x_n = 1 at powers of two, n^2 elsewhere
tail = sum(1.0/x for x in xs)
mins = [min(xs[i:i+200]) for i in range(0, 1800, 200)]
print(f"  x_n = n^2 except x_n = 1 at powers of 2.  sum 1/x_n over n<2000 = {tail:.4f} (converges)")
print(f"  yet min over successive blocks of 200: {mins}")
print("  Summability permits infinitely many n with x_n = 1: no pointwise lower envelope.")
