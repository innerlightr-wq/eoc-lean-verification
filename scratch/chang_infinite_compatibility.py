#!/usr/bin/env python3
"""Computational support for docs/CHANG_INFINITE_COMPATIBILITY_AUDIT.md.

Standard library only, deterministic.

    python3 scratch/chang_infinite_compatibility.py

Sections:
  H/L  the constructive gadget: emit any Chang history inside the exact zero corridor,
       validate confinement, exact label match, absence of spurious events, and spacing
  N/O  fibers of the Chang-history map and conditional entropy, within matched (N,S) shells
  U    does fixing a history pin the least realizer?

The Beatty facts used (floor(2a)=3, floor(3a)=4, and the 1/2/3-step gap sets) are PROVED in
EOC/ChangInfiniteCompatibility.lean; they are re-checked numerically here only as a sanity test.
Finite data is not evidence about infinite behaviour.
"""

from decimal import Decimal, getcontext
getcontext().prec=60
alpha_d = Decimal(3).ln()/Decimal(2).ln()
alpha=float(alpha_d)
def fl(k): return int((Decimal(k)*alpha_d).to_integral_value(rounding='ROUND_FLOOR'))
def fl_exact(k):
    v=int(alpha*k)
    while 2**(v+1)<=3**k: v+=1
    while 2**v>3**k: v-=1
    return v
assert all(fl(k)==fl_exact(k) for k in range(0,600))
print("high-precision floor agrees with the exact integer method for k < 600")
print(f"  floor(2a)={fl(2)} (2a={2*alpha:.6f});  floor(3a)={fl(3)} (3a={3*alpha:.6f})")
N1=30000
F=[fl(k) for k in range(N1+4)]
g1={F[N+1]-F[N] for N in range(N1)}
g2={F[N+2]-F[N] for N in range(N1)}
g3={F[N+3]-F[N] for N in range(N1)}
print(f"  1-step gaps {sorted(g1)}; 2-step {sorted(g2)}; 3-step {sorted(g3)}  (N<{N1})")
print()
print("=== emission gadget: append (2,1,1+y) starting from deficit D ===")
worst={0:99,1:99}; net={0:99,1:99}
for N in range(1,N1):
    b1=F[N+1]-F[N]; b2=F[N+2]-F[N+1]; b3=F[N+3]-F[N+2]
    for y in (0,1):
        d1=b1-2; d2=b1+b2-3; d3=b1+b2+b3-4-y
        worst[y]=min(worst[y],d1,d2,d3); net[y]=min(net[y],d3)
for y in (0,1):
    print(f"  label {y}: min intermediate (D_j - D) = {worst[y]:+d};  min net (D_end - D) = {net[y]:+d}")
print()
print("  => reserve D >= 1 suffices for EITHER label; label 0 costs nothing, label 1 costs <= 1")
print("=== recharge: append digit 1 ===")
print(f"  D -> D + b - 1; two steps give >= D+1 since 2-step gap >= {min(g2)}")
print(f"  density of b=2 is alpha-1 = {alpha-1:.6f}")


from decimal import Decimal, getcontext
import random
getcontext().prec=80
A = Decimal(3).ln()/Decimal(2).ln()
def fl(k): return int((Decimal(k)*A).to_integral_value(rounding='ROUND_FLOOR'))

def labels(D):
    """all Chang events with determined label: event at j iff (d_j,d_{j+1})=(2,1); label=1 iff d_{j+2}>=2"""
    return [(j, 1 if D[j+2]>=2 else 0) for j in range(len(D)-2) if D[j]==2 and D[j+1]==1]

def zero_confined(D):
    S=0
    for j,d in enumerate(D):
        S+=d
        if S > fl(j+1): return False, j+1
    return True, None

def build(y, RESERVE=2):
    """emit history y inside the exact zero corridor.
       blocks: label0 -> (2,1,1)  valuation 4 ;  label1 -> (2,1,3)  valuation 6
       padding: digit 1 only. Digit 3 after a 2-1 pair prevents a spurious (2,1) event."""
    D=[]; S=0
    def defic(): return fl(len(D)) - S
    def push(d):
        nonlocal S
        D.append(d); S+=d
        assert S <= fl(len(D)), f"corridor violated at {len(D)}"
    while defic() < RESERVE: push(1)          # initial reserve
    for b in y:
        blk = [2,1,3] if b else [2,1,1]
        for d in blk: push(d)
        while defic() < RESERVE: push(1)      # recharge
    return D

print("=== constructive infinite-symbolic gadget: validation ===")
random.seed(11)
tests = ([tuple([1]*40), tuple([0]*40), tuple([0,1]*20), tuple([1,1,0]*13)]
         + [tuple(random.randint(0,1) for _ in range(40)) for _ in range(40)])
allok=True; lens=[]
for y in tests:
    D=build(list(y))
    ok,viol = zero_confined(D)
    ev=labels(D)
    got=tuple(l for _,l in ev)
    match = got[:len(y)]==tuple(y) and len(got)==len(y)
    lens.append(len(D)/len(y))
    if not(ok and match):
        allok=False
        print(f"  FAIL y={y[:12]}... confined={ok}@{viol} labels_match={match} got={got[:12]}")
print(f"  {len(tests)} histories of length 40 (incl. all-1s, all-0s, alternating, periodic, random)")
print(f"  every word zero-confined AND label sequence exactly equals the target: {allok}")
print(f"  no spurious events: #events == len(y) in every case: {allok}")
print(f"  steps per label: min {min(lens):.2f}, max {max(lens):.2f}, mean {sum(lens)/len(lens):.2f}")
print()
# what goes wrong with (2,1,2)
print("=== why label-1 block is (2,1,3) and not (2,1,2) ===")
bad=[2,1,2,1,1,2,1,1]
print(f"  word {bad} has events at {[j for j,_ in labels(bad)]} -> the 2 at index 2 is followed by 1,")
print("  creating a SPURIOUS event. Using digit 3 instead removes it: ", end="")
good=[2,1,3,1,1,2,1,1]
print(f"{good} -> events at {[j for j,_ in labels(good)]}")
print()
print("=== deficit accounting (exact) ===")
print("  label 0 block (2,1,1): valuation 4 over 3 steps; 3-step Beatty gap >= 4 => net deficit change >= 0")
print("  label 1 block (2,1,3): valuation 6 over 3 steps; => net deficit change >= -2")
print("  padding digit 1: deficit change = b-1 in {0,1}; any 2 consecutive steps give >= +1")
print("  => reserve 2 is invariant; spacing per label is bounded, so event density is positive")


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
def zcw(k):
    caps=[fl(j) for j in range(k+1)]; out=[]
    def rec(j,s,cur):
        if j==k: out.append(tuple(cur)); return
        for d in range(1,caps[j+1]-s+1):
            cur.append(d); rec(j+1,s+d,cur); cur.pop()
    rec(0,0,[]); return out
def labels(D):
    return tuple(1 if D[j+2]>=2 else 0 for j in range(len(D)-2) if D[j]==2 and D[j+1]==1)

print("=== GATE 12/13: fiber of the Chang-history map, within matched (N,S) shells ===")
print(f"{'N':>3} {'S':>3} {'words':>6} {'#distinct histories':>20} {'max fiber':>10} {'mean fiber':>11} {'log2(words)':>12} {'log2(hist)':>11}")
for k in (12,13,14):
    byS=defaultdict(list)
    for D in zcw(k): byS[sum(D)].append(D)
    for S in sorted(byS):
        Ds=byS[S]
        if len(Ds)<300: continue
        c=Counter(labels(D) for D in Ds)
        print(f"{k:>3} {S:>3} {len(Ds):>6} {len(c):>20} {max(c.values()):>10} {sum(c.values())/len(c):>11.1f}"
              f" {math.log2(len(Ds)):>12.2f} {math.log2(len(c)):>11.2f}")
print()
print("=== conditional entropy: bits of the valuation word NOT determined by the Chang history ===")
tot_w=tot_h=0
for k in (14,):
    byS=defaultdict(list)
    for D in zcw(k): byS[sum(D)].append(D)
    for S in sorted(byS):
        Ds=byS[S]
        if len(Ds)<300: continue
        c=Counter(labels(D) for D in Ds)
        tot_w+=math.log2(len(Ds)); tot_h+=math.log2(len(c))
print(f"  summed over k=14 shells: log2(#words)={tot_w:.2f}, log2(#histories)={tot_h:.2f}")
print(f"  fraction of word-entropy captured by the Chang history: {tot_h/tot_w:.3f}")
print(f"  => the Chang observable leaves ~{100*(1-tot_h/tot_w):.0f}% of the valuation entropy undetermined")
print()
print("=== GATE 20/22: does a fixed history pin the realizer? ===")
k=14
byS=defaultdict(list)
for D in zcw(k): byS[sum(D)].append(D)
S=max(byS, key=lambda s: len(byS[s]))
Ds=byS[S]; c=defaultdict(list)
for D in Ds: c[labels(D)].append(lr(D))
big=max(c, key=lambda h: len(c[h]))
rs=sorted(c[big])
print(f"  shell (N={k},S={S}); most populous history h={big} has {len(c[big])} realizers")
print(f"  their log2 r ranges over [{math.log2(rs[0]):.2f}, {math.log2(rs[-1]):.2f}] out of max {S+1}")
allr=sorted(lr(D) for D in Ds)
print(f"  whole shell log2 r ranges over [{math.log2(allr[0]):.2f}, {math.log2(allr[-1]):.2f}]")
print(f"  => fixing the Chang history does NOT bound the least realizer away from the shell minimum")
