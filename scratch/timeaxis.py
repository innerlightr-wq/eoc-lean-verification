"""GATES 3,4,13,18,20,29,48,55,56: the time axis on actual orbits.

tau_0(m) = inf{n>=1 : R_n > 0},   sigma(m) = inf{n>=1 : m_n < m_0}.
Identity: log2 m_n = log2 m_0 - R_n + E_n,  so  m_n < m_0  <=>  R_n > E_n.
Integer forms:  R_n <= 0 <=> 2^{S_n} <= 3^n  ;  R_n > 0 <=> 2^{S_n} > 3^n.
"""
import math
alpha = math.log2(3)
def v2(n):
    r=0
    while n&1==0: n>>=1; r+=1
    return r

def analyse(m0, cap=4000):
    mi=m0; S=0; E=0.0; n=0; C=0
    tau=None; sig=None
    bad_int=bad_min=bad_desc=0
    selffin_min=1e18            # min over steps of (available recovery) - (required to reach 0)
    while n < cap:
        # step
        t=3*mi+1; d=v2(t)
        # GATE 20/48: available valuation vs what is needed to lift R to 0 from depth -R_n
        R = S - alpha*n
        need = -R + alpha          # d needed at this step to make R_{n+1} = 0
        avail = math.log2(3*mi+1)  # hard cap: 2^d | 3m+1 so d <= log2(3m+1)
        if n >= 1: selffin_min = min(selffin_min, avail - need)
        E += math.log2(1+1/(3*mi))
        C = 3*C + (1 << S)
        S += d; mi = t >> d; n += 1
        Rn = S - alpha*n
        # integer form of the corridor
        if (Rn <= 0) != ((1 << S) <= 3**n): bad_int += 1
        # GATE 13: R_n <= 0  =>  m_n > m_0
        if Rn <= 0 and not (mi > m0): bad_min += 1
        # descent iff R_n > E_n
        if (mi < m0) != (Rn > E - 1e-12): bad_desc += 1
        if tau is None and Rn > 0: tau = n
        if sig is None and mi < m0: sig = n
        if tau is not None and sig is not None: break
        if mi == 1: break
    return tau, sig, S, E, selffin_min, (bad_int, bad_min, bad_desc)

bi=bm=bd=0; n=0; strict=[]; worst_tau=[]
sf = 1e18
for m0 in range(3, 200001, 2):
    tau, sig, S, E, s, bads = analyse(m0)
    bi+=bads[0]; bm+=bads[1]; bd+=bads[2]; n+=1
    sf = min(sf, s)
    if tau is not None and sig is not None and tau < sig:
        strict.append((m0, tau, sig))
    if tau is not None:
        worst_tau.append((tau/math.log2(m0), m0, tau, sig))

print(f"seeds: {n}")
print(f"  integer form  R_n<=0 <=> 2^S_n <= 3^n        : mismatches {bi}")
print(f"  GATE 13  R_n<=0 => m_n > m_0                 : violations {bm}")
print(f"  descent iff R_n > E_n                        : mismatches {bd}")
print(f"  seeds with NO drift exit found within cap    : {sum(1 for r,m,t,s in worst_tau if t is None)}")
print()
print(f"GATE 4 - strictness tau_0 < sigma : {len(strict)} / {n} seeds")
print("  smallest examples (m, tau_0, sigma):", strict[:8])
print()
print(f"GATE 48 - self-financing margin  min over all steps of (log2(3m_n+1) - (alpha - R_n)):")
print(f"  {sf:.4f}   (positive => the valuation cap ALWAYS exceeds what a one-step return to R=0 needs)")
print()
worst_tau.sort(reverse=True)
print("GATE 56 - largest tau_0/log2 m")
print(f"{'m':>8} {'tau_0':>7} {'sigma':>7} {'tau/log2m':>10}")
for r,m,t,s in worst_tau[:8]:
    print(f"{m:>8} {t:>7} {str(s):>7} {r:>10.4f}")
