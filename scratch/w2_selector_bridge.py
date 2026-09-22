#!/usr/bin/env python3
"""Computational support for docs/W2_REALIZER_SELECTOR_BRIDGE_AUDIT.md.

Standard library only, deterministic. Small targeted checks, not curve fitting.

  python3 scratch/w2_selector_bridge.py

Covers: the Chang full-shift W=2 stress test (gates 9/11), the high-valuation
defect budget (gate 10), the offset-zero cutoff regime (gate 3), the
q-sensitivity table (gates 25/26), character resolution in r-space (gate 24),
and matched-harmonic-state realizer spread (gate 20).

Finite data is used for structural falsification only.
"""
import math
from collections import defaultdict, Counter
alpha=math.log2(3)
def fl(k):
    v=int(alpha*k)
    while 2**(v+1)<=3**k: v+=1
    while 2**v>3**k: v-=1
    return v
def carry(D):
    k=len(D); C=0; s=0
    for j in range(k):
        C+=3**(k-1-j)*2**s; s+=D[j]
    return C
def lr(D):
    k=len(D); S=sum(D); M=2**(S+1)
    return ((2**S-carry(D))*pow(pow(3,k,M),-1,M))%M
def term(D):
    return (3**len(D)*lr(D)+carry(D))//2**sum(D)
def zcw(k):
    caps=[fl(j) for j in range(k+1)]; out=[]
    def rec(j,s,cur):
        if j==k: out.append(tuple(cur)); return
        for d in range(1,caps[j+1]-s+1):
            cur.append(d); rec(j+1,s+d,cur); cur.pop()
    rec(0,0,[]); return out

print("=== GATE 9/L: the formal Chang construction as a W=2 stress test ===")
def changSeq(y,i):
    r=i%7
    return 2 if r==4 else ((3 if y(i//7) else 1) if r==6 else 1)
alltrue=lambda k: True
D=[changSeq(alltrue,i) for i in range(70)]
print(f"  y == true, first 21 digits: {D[:21]}")
h=sum(1 for d in D if d>=3)
print(f"  digit-3 density = {h}/{len(D)} = {h/len(D):.4f} = 1/7 exactly")
runs=[]; c=0
for d in D:
    if d<=2: c+=1
    else: runs.append(c); c=0
runs.append(c)
print(f"  maximal pure-W=2 run length = {max(runs)}  (blocks are 1,1,1,1,2,1,3)")
S=0; ok=True
for j,d in enumerate(D):
    S+=d
    if S>fl(j+1): ok=False
print(f"  zero-confined: {ok}")
print("  => zero confinement does NOT imply eventual W=2 survival; W=2 runs are uniformly bounded (<=6)")

print()
print("=== GATE 10/M: high-valuation defect budget ===")
print(f"  S_N >= N + 2 h_N  and  S_N <= floor(alpha N)  =>  2 h_N <= floor(alpha N) - N")
print(f"  asymptotic: h_N/N <= (alpha-1)/2 = {(alpha-1)/2:.9f}")
worst=0; bad=0
for k in range(1,15):
    for W in zcw(k):
        hN=sum(1 for d in W if d>=3); SN=sum(W)
        if not (SN >= k + 2*hN): bad+=1
        if not (2*hN <= fl(k)-k): bad+=1
        worst=max(worst,hN/k)
print(f"  verified on all zero-confined words k<=14: violations = {bad}; max observed h_N/N = {worst:.4f}")
print(f"  Chang construction sits at 1/7 = {1/7:.4f}, well inside the budget {((alpha-1)/2):.4f}")

print()
print("=== GATE 3/F: is the offset-zero upper inequality automatic? ===")
print("  offset-zero: r(A) < Y <= r(A) + 2^{S_A+1}")
print("  second positive realizer is r + 2^{S_A+1}, so the condition says EXACTLY ONE")
print("  realizer of A lies in [1,Y).  Upper bound is automatic iff 2^{S_A+1} >= Y.")
for K in (20,30,40):
    Y=2**K
    auto=[s for s in range(1,60) if 2**(s+1)>=Y]
    print(f"  Y=2^{K}: automatic for all S_A >= {min(auto)}  (i.e. S_A+1 >= {K})")

print()
print("=== GATES 25/26: q-sensitivity.  r -> r + q*2^{S+1} ===")
print("  m_A^0 = (3^p r + C)/2^S   =>   m -> m + 2q*3^p   (independent of the alphabet)")
W=(1,2,1,1,2,1)  # a W=2 word
p=len(W); S=sum(W); r0=lr(W); C=carry(W); m0=term(W)
print(f"  test word A={W}: p={p}, S_A={S}, r(A)={r0}, m_A^0={m0}")
for q in range(6):
    r=r0+q*2**(S+1); m=(3**p*r+C)//2**S
    print(f"    q={q}: r={r:<8} r mod 2^(S+1)={r%2**(S+1):<5} m={m:<8} m mod 8={m%8}  m-m0={m-m0} = 2q*3^p={2*q*3**p}")
print(f"  m mod 8 has period {8//math.gcd(8,2*3**p)} in q -> PERIODIC, never growing")
print()
print("  q-SENSITIVITY TABLE")
print(f"  {'observable':<34} {'behaviour under r -> r+q*2^(S+1)':<38} {'sees Archimedean size?'}")
rows=[("r(A) mod 2^{S_A+1}","completely q-invariant","NO"),
      ("prefix twist e(k r/2^{s+1})","completely q-invariant","NO"),
      ("m_A^0 mod 2^{S_B+3}","periodic in q (period 2^{S_B+2})","NO"),
      ("terminal class mod 8, psi_eta","periodic in q (period 4)","NO"),
      ("F_{S_B}(m) suffix survival","periodic in q","NO"),
      ("G_s(k), Sigma_I","built from the above; q-periodic","NO"),
      ("offset-zero indicator 1[r<Y<=r+2^{S+1}]","cutoff-dependent (selects q=0)","YES - but it IS the target"),
      ("r(A) as an integer","grows linearly in q","YES")]
for a,b,c in rows: print(f"  {a:<34} {b:<38} {c}")

print()
print("=== GATE 24/W: resolution of the harmonic machinery in r-space ===")
for S in (20,40,80,160):
    print(f"  S={S:<4} r lives mod 2^{S+1} ({S+1} bits); suffix character sees terminal class mod 8 (3 bits)"
          f"  -> fraction {3/(S+1):.4f}")
print("  the character family eta in {1,2,3,5,6,7} has 6 elements; the trivial character eta=0")
print("  (which IS the offset-zero count) is EXCLUDED from the family by construction.")

print()
print("=== GATE 20/V: matched terminal class, different realizer size (zero-confined shells) ===")
print(f"  {'k':>3} {'S':>3} {'m mod 8':>8} {'#words':>7} {'min log2 r':>11} {'max log2 r':>11} {'spread':>7}")
for k in (12,13,14):
    byS=defaultdict(list)
    for Wd in zcw(k): byS[sum(Wd)].append(Wd)
    S=max(byS,key=lambda s:len(byS[s]))
    g=defaultdict(list)
    for Wd in byS[S]: g[term(Wd)%8].append(math.log2(lr(Wd)))
    for cls in sorted(g):
        v=g[cls]
        if len(v)<20: continue
        print(f"  {k:>3} {S:>3} {cls:>8} {len(v):>7} {min(v):>11.2f} {max(v):>11.2f} {max(v)-min(v):>7.2f}")
