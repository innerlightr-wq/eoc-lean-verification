"""Supplementary negative-finding checks:
   (N1) do burst-ending -> next-burst-ending return maps close mod 2^k ?
   (N2) ensemble balance of Y under iid geometric valuation measure (P(d=k)=2^-k),
        and whether it transfers to a single deterministic orbit.
"""
import random
from collections import defaultdict, Counter

def v2(n): return (n & -n).bit_length() - 1
def traj(n):
    s=[n]
    while s[-1]!=1:
        x=3*s[-1]+1; s.append(x>>v2(x))
    return s
def dstep(seq,j): return v2(3*seq[j]+1) if j<len(seq)-1 else 2

# ---------- N1: return-map closure ----------
print("N1 — burst-ending -> next-burst-ending residue return map, closure test")
seeds=list(range(3,2_000_001,2))
pairs={k:defaultdict(set) for k in (5,6,7,8,10,12)}
count=0
for n0 in seeds:
    seq=traj(n0); T=len(seq)-1
    if T<3: continue
    X=[1 if dstep(seq,j)>=2 else 0 for j in range(T)]
    bends=[]
    j=0
    while j<T:
        if X[j]==1:
            while j<T and X[j]==1: j+=1
            t=j-1
            if j<T and X[j]==0 and seq[t]%8==1:
                bends.append(t)
        else:
            j+=1
    for a,b in zip(bends,bends[1:]):
        count+=1
        for k in pairs:
            pairs[k][seq[a]%(1<<k)].add(seq[b]%(1<<k))
print(f"  consecutive burst-ending pairs sampled: {count}")
for k in sorted(pairs):
    multi=sum(1 for v in pairs[k].values() if len(v)>1)
    tot=len(pairs[k])
    mx=max(len(v) for v in pairs[k].values())
    print(f"  mod 2^{k:2d}: {tot:4d} input residues, {multi:4d} map to >1 output  "
          f"(max fan-out {mx})  -> {'CLOSES' if multi==0 else 'DOES NOT CLOSE'}")

# ---------- N2: ensemble balance under geometric valuation measure ----------
print()
print("N2 — ensemble Y-balance under iid geometric valuations P(d=k)=2^-k, k>=1")
random.seed(7)
def geo():
    k=1
    while random.random()<0.5: k+=1
    return k
NS=4_000_000
hist=Counter(); chan=Counter()
for _ in range(NS):
    # random word, compute realizer residue r = -C_N 3^{-N} mod 32 with S_N>=5
    S=0; Cm=0; N=0; w=[]
    while S<5:
        d=geo(); w.append(d)
        Cm=(3*Cm+pow(2,S,32))%32; S+=d; N+=1
    r=(-Cm*pow(3,-N,32))%32
    hist[r]+=1
    if w[0]==2 and len(w)>1 and w[1]==1:      # Chang channel start (2,1,...)
        chan[r]+=1
odds=sorted(x for x in hist if x%2==1)
print(f"  {NS} samples; distinct residues hit: {sorted(hist)}")
print(f"  all odd residues equidistributed? min/max count = "
      f"{min(hist[o] for o in odds)}/{max(hist[o] for o in odds)}  "
      f"(uniform expectation {NS//16})")
n9,n25=chan[9],chan[25]
print(f"  channel (2,1,...): #9={n9}  #25={n25}  P(25)={n25/(n9+n25):.4f}  (#9-#25={n9-n25})")
