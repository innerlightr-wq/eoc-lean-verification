"""GATES 4,6,12,13,20,32,35,36,45,46: actual positive-orbit lifetime.

Conventions (launch paper, Def 11.2): for odd m, accelerated orbit m_0 = m,
m_{i+1} = (3 m_i + 1)/2^{d_{i+1}},  S_i = sum_{j<=i} d_j,  R_i = S_i - i*alpha.
L = length of the injective initial segment.  A = max_{0<=i<=L} R_i.

Identities tested:
  (a) orbit floor:  log2 m_i = log2 m - R_i + E_i,   E_i = log2 prod(1+1/(3 m_j))
  (b) AUTOMATIC CORRIDOR:  R_i <= log2 m + E_i     (from m_i >= 1)
      integer form: 2^{S_i} <= 3^i m + C_i
  (c) growth envelope:  m_i + 1 <= (3/2)^i (m+1),  integer form 2^i (m_i+1) <= 3^i (m+1)
  (d) valuation bound:  2^{d_i} <= 3 m_{i-1} + 1
"""
import math
alpha = math.log2(3)

def v2(n):
    r=0
    while n%2==0: n//=2; r+=1
    return r

def run(m):
    """returns L, A, maxE, ratio, argmin index, and identity-violation counts"""
    m0=m; mi=m; S=0; C=0; E=0.0
    seen={m}
    L=0; A=0.0; maxE=0.0
    bad_a=bad_b=bad_c=bad_d=0
    minv=m; argmin=0
    i=0
    while True:
        # record state i
        R = S - i*alpha
        A = max(A, R)
        # (a) orbit floor
        if abs(math.log2(mi) - (math.log2(m0) - R + E)) > 1e-7: bad_a += 1
        # (b) automatic corridor
        if R > math.log2(m0) + E + 1e-9: bad_b += 1
        if (1 << S) > 3**i * m0 + C: bad_b += 1          # exact integer form
        # (c) growth envelope, integer form
        if (1 << i) * (mi + 1) > 3**i * (m0 + 1): bad_c += 1
        if mi < minv: minv, argmin = mi, i
        maxE = max(maxE, E)
        if mi == 1 and i > 0: break
        # step
        t = 3*mi + 1; d = v2(t)
        if (1 << d) > t: bad_d += 1                       # (d) 2^d <= 3m+1
        E += math.log2(1 + 1/(3*mi))
        C = 3*C + (1 << S); S += d
        mi = t >> d; i += 1
        if mi in seen: break
        seen.add(mi)
        if i > 4000: break
    L = i
    denom = math.log2(m0) + max(A, 1.0)
    return L, A, maxE, L/denom, argmin, (bad_a, bad_b, bad_c, bad_d)

print("Identity checks over odd m < 60001")
ba=bb=bc=bd=0; n=0
best=[]
for m in range(3, 60001, 2):
    L, A, maxE, ratio, argmin, bads = run(m)
    ba+=bads[0]; bb+=bads[1]; bc+=bads[2]; bd+=bads[3]; n+=1
    best.append((ratio, m, L, A, maxE, argmin))
print(f"  seeds: {n}")
print(f"  (a) orbit-floor identity        violations: {ba}")
print(f"  (b) AUTOMATIC corridor R_i <= log2 m + E_i (and integer form): violations {bb}")
print(f"  (c) growth envelope 2^i(m_i+1) <= 3^i(m+1) : violations {bc}")
print(f"  (d) 2^{{d_i}} <= 3 m_{{i-1}}+1               : violations {bd}")

best.sort(reverse=True)
print(f"\nGATE 46 - worst L/(log2 m + A) over odd m < 60001")
print(f"{'m':>8} {'L':>5} {'log2 m':>8} {'A':>8} {'max E':>7} {'L/(log2m+A)':>12} {'argmin':>7}")
for r,m,L,A,E,am in best[:10]:
    print(f"{m:>8} {L:>5} {math.log2(m):>8.2f} {A:>8.2f} {E:>7.3f} {r:>12.4f} {am:>7}")

print(f"\nGATE 32/35/36 - where does the orbit minimum occur?")
tail = sum(1 for r,m,L,A,E,am in best if am != L)
print(f"  seeds whose minimum is NOT at the final index: {tail} / {n}")
print("  (every convergent orbit ends at m=1, which is its minimum: h = L, Gate 36 branch B)")

print(f"\nGATE 32 - is A close to log2 m + E ?  (equality when the orbit reaches m_i = 1)")
import statistics
gaps=[(math.log2(m)+E) - A for r,m,L,A,E,am in best]
print(f"  mean (log2 m + E) - A = {statistics.mean(gaps):.6f},  max = {max(gaps):.6f}, min = {min(gaps):.6f}")
