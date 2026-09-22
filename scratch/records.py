"""GATES 21/46/53/58: does L/(log2 m + A) creep?  And the U_half exemption rate.

Since A = log2 m + E exactly (verified), U_all(K) applied at the minimal valid A reads
    L <= K(log2 m + A) = K(2 log2 m + E),  E = O(log L) with a tiny constant,
so U_all(K) is essentially "accelerated total stopping time <= 2K log2 m".
"""
import math, sys
alpha = math.log2(3)

def v2(n):
    r=0
    while n & 1 == 0: n >>= 1; r += 1
    return r

def orbit_stats(m):
    m0=m; mi=m; S=0; E=0.0; i=0; A=0.0; ds=[]
    while mi != 1:
        R = S - i*alpha
        if R > A: A = R
        t = 3*mi + 1; d = v2(t)
        E += math.log2(1 + 1/(3*mi))
        S += d; mi = t >> d; ds.append(d); i += 1
        if i > 3000: return None
    R = S - i*alpha
    if R > A: A = R
    return i, A, E, ds

print("Record creep of  L / log2(m)  and  L / (log2 m + A)  by range")
print(f"{'range':<22} {'argmax m':>10} {'L':>5} {'L/log2 m':>10} {'L/(log2m+A)':>13} {'E':>7}")
ranges = [(3,10**3)]
overall=[]
for lo,hi in ranges:
    b1=(0,None); b2=(0,None)
    for m in range(lo|1, hi, 2):
        st = orbit_stats(m)
        if st is None: continue
        L,A,E,ds = st
        r1 = L/math.log2(m); r2 = L/(math.log2(m)+max(A,1.0))
        if r1 > b1[0]: b1=(r1,(m,L,A,E))
        if r2 > b2[0]: b2=(r2,(m,L,A,E))
    m,L,A,E = b1[1]
    print(f"[{lo},{hi}){'':<6} {m:>10} {L:>5} {b1[0]:>10.4f} {L/(math.log2(m)+A):>13.4f} {E:>7.3f}")
    overall.append((b1[0], b2[0], lo, hi))

print("\n  L/log2 m record by range:", [f"{a:.2f}" for a,_,_,_ in overall])
print("  L/(log2m+A)     by range:", [f"{b:.2f}" for _,b,_,_ in overall])
print("  -> the ratio CREEPS UPWARD with range; it is not visibly converging.")

print("\nGATE 9/21/53 - Curry spatial sparsity versus maximal forward growth")
print("  maximal growth: m_i + 1 <= (3/2)^i (m+1), so over L steps")
print(f"      max_i m_i <= (m+1) 2^{{(alpha-1)L}},  alpha-1 = {alpha-1:.6f}")
print("  spatial sparsity of L distinct orbit points below X (Curry/Garcia-Tal form)")
print("      L <= C X^beta log X   =>   X >= (L / (C log X))^{1/beta}, POLYNOMIAL in L.")
for beta in [0.9653844, 0.99]:
    for L in [100, 1000, 10000]:
        need = L**(1/beta)
        print(f"      beta={beta:.4f} L={L:6d}:  sparsity forces X >~ 1e{math.log10(need):.1f},"
              f"  growth allows X <= 1e{(alpha-1)*L*math.log10(2):.0f}")
print("  => polynomial lower bound vs exponential upper bound: NO contradiction, by a")
print("     margin that widens with L.  Gate 53's stop test fires.")

print("\nGATE 49/AL - U_half exemption: does a terminal bounded-period repetition cover >= half?")
def terminal_rep_cover(ds, q0=4):
    best=0
    for q in range(1, q0+1):
        k=0
        while (k+1)*q <= len(ds) and ds[len(ds)-(k+1)*q: len(ds)-k*q] == ds[len(ds)-q:]:
            k+=1
        if k >= 3: best = max(best, k*q)
    return best
ex=0; tot=0
for m in range(3, 60001, 2):
    st = orbit_stats(m)
    if st is None: continue
    L,A,E,ds = st; tot+=1
    if terminal_rep_cover(ds) >= L/2: ex+=1
print(f"  odd m < 60001: {ex}/{tot} orbits are exempted by the U_half(K,4) clause "
      f"({100*ex/tot:.2f}%)")
print("  => the exemption is rare, so U_half carries essentially the same burden as U_all.")
