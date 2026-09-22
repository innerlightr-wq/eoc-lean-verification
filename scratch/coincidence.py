"""WHY tau_0 = sigma empirically -- and what it would take to break it.

At n = tau_0:  R_n > 0, and tau_0 < sigma iff m_n >= m_0 iff R_n <= E_n.
Under zero confinement for j < n, GATE 13 gives m_j > m_0, so
      E_n <= (1/(3 ln2)) * sum_{j<n} 1/m_j  <=  0.4809 * n / m_0.
And S_n integral with R_n > 0 gives  R_n >= 1 - frac(alpha n).
Hence strictness forces

      m_0  <=  0.4809 * n / (1 - frac(alpha*n))          (*)

while m_0 must also realize a 0-confined word of length n, so m_0 >= r_min(n,0).
So strictness at depth n requires   r_min(n,0)  <=  0.4809 n/(1-frac(alpha n)).
"""
import math
alpha = math.log2(3)
def v2(n):
    r=0
    while n&1==0: n>>=1; r+=1
    return r

# r_min(n,0) = least odd m whose orbit is 0-confined through step n
LIM = 3_000_000
best = {}
for m0 in range(3, LIM, 2):
    mi=m0; S=0; n=0
    while True:
        t=3*mi+1; d=v2(t); S+=d; mi=t>>d; n+=1
        if S - alpha*n > 0: break
        if n not in best: best[n]=m0
        if n > 200 or mi==1: break

print(f"{'n':>4} {'r_min(n,0)':>12} {'1-frac(a n)':>12} {'bound (*)':>14} {'strictness possible?':>21}")
poss=0
for n in sorted(best):
    if n < 5: continue
    fr = 1 - (alpha*n)%1.0
    bound = 0.4809*n/fr
    ok = best[n] <= bound
    if ok: poss+=1
    if n <= 45 or ok:
        print(f"{n:>4} {best[n]:>12} {fr:>12.6f} {bound:>14.1f} {str(ok):>21}")
print()
print(f"depths where strictness is even numerically possible: {poss} of {len([k for k in best if k>=5])}")
print()
print("r_min(n,0) grows fast; the bound (*) grows only like n/(1-frac(alpha n)), which is")
print("polynomial in n because alpha = log2 3 has finite irrationality measure.")
print("=> any superpolynomial realizer floor forces tau_0 = sigma for all large seeds.")
