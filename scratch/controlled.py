"""(a) P measured at CONSTANT sample size per bucket, to avoid the max-over-larger-sample trap.
   (b) Test the reframing:  R_n <= c  <=>  m_n >= m_0 2^{E_n - c},
       i.e. O_c counts the time the orbit spends at or above (a 2^{-c} fraction of) its START.
"""
import math, random
alpha = math.log2(3)
def v2(x):
    r=0
    while x&1==0: x>>=1; r+=1
    return r

def run(m0, c=1.0, cap=5000):
    mi=m0; S=0; n=0; E=0.0
    inC=None; P=0; O=0; bad=0
    while True:
        R = S - alpha*n
        cur = (R <= c)
        # (b) reframing check
        if cur != (mi >= m0 * 2**(E - c) - 1e-9): bad += 1
        if cur:
            O += 1
            if not inC: P += 1
        inC = cur
        if mi==1 and n>0: break
        t=3*mi+1; d=v2(t); E += math.log2(1+1/(3*mi))
        S += d; mi = t>>d; n += 1
        if n>cap: return None
    return O, P, bad, E

print("(b) reframing  R_n <= c  <=>  m_n >= m_0 2^{E_n - c}")
tot=badtot=0
for m0 in range(3, 60001, 2):
    r=run(m0)
    if r is None: continue
    tot+=1; badtot+=r[2]
print(f"    {tot} seeds, mismatches: {badtot}")
print("    => O_c is exactly the time the orbit spends at or above 2^{-c} times its start")
print("       (up to the tiny carry factor 2^{E_n}, E_n <= %.3f here)" % max(run(m)[3] for m in [27,703,6171,285175]))

print("\n(a) episode count P at CONSTANT sample size (2000 random odd seeds per bucket)")
print(f"{'log2 m0':>8} {'sampled':>8} {'mean P':>7} {'max P':>6} {'mean O':>8} {'max O':>6}")
random.seed(17)
for b in range(8, 25):
    lo, hi = 2**b, 2**(b+1)
    seen=0; Ps=[]; Os=[]
    tries=0
    while seen < 2000 and tries < 60000:
        tries += 1
        m0 = random.randrange(lo, hi) | 1
        r = run(m0)
        if r is None: continue
        Os.append(r[0]); Ps.append(r[1]); seen += 1
    if seen < 500: break
    print(f"{b:>8} {seen:>8} {sum(Ps)/len(Ps):>7.3f} {max(Ps):>6} {sum(Os)/len(Os):>8.2f} {max(Os):>6}")
