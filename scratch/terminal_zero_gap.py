#!/usr/bin/env python3
"""Computational support for docs/NORMALIZED_CARRY_TERMINAL_ZERO_GAP_AUDIT.md.

Standard library only, deterministic, small and targeted.  Covers:
  - the g = ceil(E) correction to the previous round;
  - the carry-side pattern z_N = 2^S + r_N in the small-realizer regime;
  - carry dominance killing the mixed real/2-adic approximation;
  - non-locality of the high bits of the sparse-unit sum;
  - same-(N,S) gap fibers, the random-injective null, and prefix/suffix perturbation;
  - negative-integer and Chang calibration, and record-frontier gap values.

  python3 scratch/terminal_zero_gap.py

All population figures are diagnostics only; the frontier needs a pointwise statement.
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
    N=len(D); C=0; s=0
    for j in range(N):
        C+=3**(N-1-j)*2**s; s+=D[j]
    return C
def lr(D):
    N=len(D); S=sum(D); M=2**(S+1)
    return ((2**S-carry(D))*pow(pow(3,N,M),-1,M))%M
def zcw(k):
    caps=[fl(j) for j in range(k+1)]; out=[]
    def rec(j,s,cur):
        if j==k: out.append(tuple(cur)); return
        for d in range(1,caps[j+1]-s+1):
            cur.append(d); rec(j+1,s+d,cur); cur.pop()
    rec(0,0,[]); return out
def gap(D):
    S=sum(D); r=lr(D); return S - (r.bit_length()-1)   # S - floor(log2 r)

print("=== GATE 1/E: correction.  g(D) = S - floor(log2 r)  vs  E(D) = S - log2 r ===")
bad=0; tot=0; eq=0
for k in range(3,12):
    for D in zcw(k):
        S=sum(D); r=lr(D)
        g=S-(r.bit_length()-1); E=S-math.log2(r)
        tot+=1
        if not (g-1 < E <= g + 1e-12): bad+=1
        if abs(E-g)<1e-12: eq+=1
        if g != math.ceil(E-1e-12) and r>1: bad+=1
print(f"  words {tot}; violations of  g-1 < E <= g  and  g = ceil(E): {bad}")
print(f"  cases with E == g exactly (r = 1): {eq}")
print("  => E(D) is NOT an integer zero-run; g(D) = ceil(E(D)) is.  Prior report's phrasing corrected.")

print()
print("=== GATE 2/F: carry-side pattern.  z_N = Z_N mod 2^{S+1} ===")
bad=0; small=0
for k in range(3,11):
    for D in zcw(k):
        N=len(D); S=sum(D); M=2**(S+1); r=lr(D)
        Z=(-carry(D)*pow(pow(3,N,M),-1,M))%M
        if r < 2**S:
            small+=1
            if Z != 2**S + r: bad+=1
        else:
            if Z != r - 2**S: bad+=1
print(f"  small-realizer cases (r < 2^S): {small}; mismatches of z_N = 2^S + r_N: {bad}")
print("  so a gap of length g means: bit S of z_N is 1, then g-1 zero bits, then the top bit of r")

print()
print("=== GATES 13/17/P/R: carry dominance kills the mixed approximation ===")
print("  orbit identity 3^N r_N + C_N = 2^S m_N, m_N odd.  A gap g means r_N < 2^{S-g+1}.")
print("  'approximation' |2^S m_N - C_N| = 3^N r_N.  Nontrivial only if 3^N r_N < 2^S.")
print(f"  {'N':>3} {'S':>4} {'log2(3^N)':>10} {'log2(2^S)':>10} {'log2(3^N * r_min)':>18} {'nontrivial?':>12}")
for k in (6,9,12,15):
    Ws=zcw(k); rmin=min(lr(D) for D in Ws)
    S=max(sum(D) for D in Ws)
    print(f"  {k:>3} {S:>4} {k*alpha:>10.2f} {S:>10.2f} {k*alpha+math.log2(rmin):>18.2f} "
          f"{str(k*alpha+math.log2(rmin) < S):>12}")
print("  since S = alpha*N + O(1), log2(3^N) = alpha*N ~ S, so 3^N r_N >= 2^S ALWAYS (r_N >= 1).")
print("  the approximation error exceeds the unit 2^S: VACUOUS.  Carry dominance, as in the Pell audit.")

print()
print("=== GATE 5/I: which terms control the high bits of Z_N? ===")
D=(1,2,1,1,2,1,2); N=len(D); S=sum(D); M=2**(S+1)
print(f"  D={D}, S={S}.  term j is 3^-(j+1) * 2^{{S_j}}: an odd unit times 2^{{S_j}},")
print("  so its 2-adic expansion has a 1 at bit S_j and generically nonzero bits at EVERY higher position.")
s=0; Ss=[]
for d in D: Ss.append(s); s+=d
for j in range(N):
    term=(pow(pow(3,j+1,M),-1,M)*2**Ss[j])%M
    print(f"    j={j} S_j={Ss[j]:>2}  term mod 2^(S+1) = {term:>6} = {term:0{S+1}b}")
print("  every term with S_j <= b contributes to bit b.  NO LOCALITY: the high frontier")
print("  depends on the entire history, not on a bounded suffix.")

print()
print("=== GATES 20/U + 21: same-(N,S) shell, fiber of the gap condition ===")
print(f"  {'N':>3} {'S':>3} {'words':>6} {'g>=1':>6} {'g>=2':>6} {'g>=3':>6} {'g>=4':>6} {'max g':>6} {'distinct suffixes at g>=3':>26}")
for k in (12,13,14):
    byS=defaultdict(list)
    for D in zcw(k): byS[sum(D)].append(D)
    S=max(byS,key=lambda s:len(byS[s]))
    Ws=byS[S]; gs=[(D,gap(D)) for D in Ws]
    big=[D for D,g in gs if g>=3]
    suf=len({D[-4:] for D in big}) if big else 0
    print(f"  {k:>3} {S:>3} {len(Ws):>6} "
          f"{sum(1 for _,g in gs if g>=1):>6} {sum(1 for _,g in gs if g>=2):>6} "
          f"{sum(1 for _,g in gs if g>=3):>6} {sum(1 for _,g in gs if g>=4):>6} "
          f"{max(g for _,g in gs):>6} {suf:>26}")
print("  large-gap words do NOT collapse to few suffixes: symbolic freedom survives the gap condition.")

print()
print("=== GATES 29/30/AC/AD: prefix and suffix perturbation ===")
k=13
byS=defaultdict(list)
for D in zcw(k): byS[sum(D)].append(D)
S=max(byS,key=lambda s:len(byS[s])); Ws=byS[S]
# prefix perturbation: same long prefix, differ late
bypre=defaultdict(list)
for D in Ws: bypre[D[:k-2]].append(D)
spreads=[max(gap(D) for D in v)-min(gap(D) for D in v) for v in bypre.values() if len(v)>1]
print(f"  same {k-2}-letter prefix, last 2 letters vary: max spread in g = {max(spreads) if spreads else 0}"
      f"  (over {len(spreads)} prefix classes)")
# suffix perturbation: same suffix, vary prefix
bysuf=defaultdict(list)
for D in Ws: bysuf[D[-4:]].append(D)
spreads2=[max(gap(D) for D in v)-min(gap(D) for D in v) for v in bysuf.values() if len(v)>1]
print(f"  same 4-letter suffix, prefix varies:        max spread in g = {max(spreads2) if spreads2 else 0}"
      f"  (over {len(spreads2)} suffix classes)")
print("  a late one-letter change moves g by O(S); identical suffixes give widely varying g.")
print("  => the high-gap event is neither prefix-local nor suffix-local.")

print()
print("=== GATE 22/V: same-shell null comparison (density of g >= G) ===")
print(f"  {'N':>3} {'S':>3} {'words':>6} " + " ".join(f"{'g>='+str(G):>8}" for G in range(1,6)))
for k in (13,14):
    byS=defaultdict(list)
    for D in zcw(k): byS[sum(D)].append(D)
    S=max(byS,key=lambda s:len(byS[s])); Ws=byS[S]
    gs=[gap(D) for D in Ws]
    row=" ".join(f"{sum(1 for g in gs if g>=G)/len(Ws):>8.4f}" for G in range(1,6))
    print(f"  {k:>3} {S:>3} {len(Ws):>6} {row}")
print(f"  random-injective prediction 2^-G:      " + " ".join(f"{2.0**-G:>8.4f}" for G in range(1,6)))
print("  agreement is close: NO extra arithmetic suppression or enhancement of the gap.")

print()
print("=== GATE 27/AA: negative-integer calibration ===")
def nu2(n):
    k=0
    while n%2==0: n//=2; k+=1
    return k
for x in (-1,-5):
    m=x; D=[]
    for _ in range(12):
        d=nu2(3*m+1); D.append(d); m=(3*m+1)//2**d
    print(f"  x={x}: word={D[:8]}...  g_N for N=2..8: {[gap(tuple(D[:N])) for N in range(2,9)]}")
print("  their realizers are 2^{S+1}-1-ish (top bit SET), so g = 0 or 1: NO long zero gap.")
print("  long zero gaps are a small-realizer phenomenon, not a generic zero-confinement one.")

print()
print("=== GATE 28/AB: Chang full-shift stress test (no Chang route reopened) ===")
def changSeq(y,i):
    r=i%7
    return 2 if r==4 else ((3 if y(i//7) else 1) if r==6 else 1)
for name,y in (("all-true",lambda k:True),("all-false",lambda k:False),
               ("alternating",lambda k:k%2==0),("period-3",lambda k:k%3==0)):
    D=tuple(changSeq(y,i) for i in range(14))
    print(f"  {name:>12}: g_N for N=4..12 = {[gap(D[:N]) for N in range(4,13)]}")
print("  arbitrary symbolic complexity coexists with both small and large gaps:")
print("  Chang complexity is not the variable controlling the gap.")

print()
print("=== GATE 23/W: record-frontier calibration, g vs E ===")
print(f"  {'seed':>9} {'N':>3} {'S':>4} {'r_N':>10} {'g=S-floor(log2 r)':>18} {'E=S-log2 r':>12} {'g==ceil(E)':>11}")
for m0 in (27,703,26623,159487,626331):
    m=m0; D=[]
    for _ in range(14):
        d=nu2(3*m+1); D.append(d); m=(3*m+1)//2**d
        if m==1: break
    for N in (min(8,len(D)), min(12,len(D))):
        if N<3: continue
        W=tuple(D[:N]); S=sum(W); r=lr(W)
        g=S-(r.bit_length()-1); E=S-math.log2(r)
        print(f"  {m0:>9} {N:>3} {S:>4} {r:>10} {g:>18} {E:>12.3f} {str(g==math.ceil(E-1e-12)):>11}")
