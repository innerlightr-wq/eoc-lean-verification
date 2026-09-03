"""Supplementary: verify the mod-32 realizer identity along ONE long trajectory
(>= 100000 accelerated steps) to satisfy Test 1's single-orbit length request."""
import random
def v2(n): return (n & -n).bit_length() - 1
def traj(n):
    s=[n]
    while s[-1]!=1:
        x=3*s[-1]+1; s.append(x>>v2(x))
    return s
random.seed(1)
# ~180k-bit odd seed -> ~100k+ accelerated steps
n0 = random.randrange(1<<180000, 1<<180050) | 1
seq = traj(n0)
T = len(seq)-1
print("single-trajectory accelerated steps:", T)
checks=exc=0
# head + 400 tail offsets spread across the whole orbit
offs = list(range(0,50)) + list(range(50, T, max(1,T//400)))
for k in offs:
    S=0; Cm=0; hits=0
    for j in range(0, min(T-k+6, 400)):
        dj = v2(3*seq[k+j]+1) if k+j<T else 2
        Cm = (3*Cm + pow(2,S,32)) % 32
        S += dj
        Nn=j+1
        if S>=5:
            pred = (-Cm*pow(3,-Nn,32))%32
            if pred != seq[k]%32: exc+=1
            checks+=1; hits+=1
            if hits>=6: break
print("mod-32 identity checks:", checks, " exceptions:", exc)
