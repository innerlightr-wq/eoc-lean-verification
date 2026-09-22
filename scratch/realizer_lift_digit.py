#!/usr/bin/env python3
"""Computational support for docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md.

Standard library only, deterministic. Verifies the identifications the audit rests on:
cylinder nesting, the lift-digit range, the variable-block binary identification,
q_N = C_N and xi_N = Z_N mod 2^S_N, the half-cylinder selector bit, the negative-integer
calibration (-1, -5, -7), bijectivity of D <-> r(D) <-> lambda, and the record-frontier
terminal zero-run reading.

  python3 scratch/realizer_lift_digit.py

Finite data checks identities only; nothing is extrapolated.
"""
import math
from fractions import Fraction
from collections import defaultdict, Counter
alpha=math.log2(3)
def fl(k):
    v=int(alpha*k)
    while 2**(v+1)<=3**k: v+=1
    while 2**v>3**k: v-=1
    return v
def carry(D):            # C_N = sum_{j<N} 3^{N-1-j} 2^{s_j}
    N=len(D); C=0; s=0
    for j in range(N):
        C += 3**(N-1-j)*2**s; s += D[j]
    return C
def lr(D):               # least positive realizer mod 2^{S+1}
    N=len(D); S=sum(D); M=2**(S+1)
    return ((2**S - carry(D))*pow(pow(3,N,M),-1,M))%M
def nu2(n):
    k=0
    while n%2==0: n//=2; k+=1
    return k

print("=== GATE 0/C: realizer convention ===")
D=(1,2,1,1,2)
N=len(D); S=sum(D)
print(f"  D={D}  N={N}  S_N={S}  modulus 2^(S+1)={2**(S+1)}  r_N={lr(D)}  odd={lr(D)%2==1}")
print(f"  representative range: least POSITIVE, i.e. in [1, 2^(S+1)]; r is odd so never 0")

print()
print("=== GATE 0: nesting r_{N+1} = r_N (mod 2^{S_N+1}) ===")
bad=0; tested=0
def zcw(k):
    caps=[fl(j) for j in range(k+1)]; out=[]
    def rec(j,s,cur):
        if j==k: out.append(tuple(cur)); return
        for d in range(1,caps[j+1]-s+1):
            cur.append(d); rec(j+1,s+d,cur); cur.pop()
    rec(0,0,[]); return out
for k in range(1,11):
    for W in zcw(k):
        for d in range(1,5):
            W2=W+(d,)
            if sum(W2)>fl(k+1): continue
            tested+=1
            if lr(W2)%2**(sum(W)+1) != lr(W): bad+=1
print(f"  extensions tested {tested}; nesting violations {bad}")

print()
print("=== GATE 1/D: lift digit t_N = (r_{N+1}-r_N)/2^{S_N+1} ===")
bad=0; tested=0; rng=Counter()
for k in range(1,11):
    for W in zcw(k):
        for d in range(1,5):
            W2=W+(d,)
            if sum(W2)>fl(k+1): continue
            SN=sum(W); t=(lr(W2)-lr(W))//2**(SN+1)
            tested+=1
            if not (0 <= t < 2**d): bad+=1
            rng[d]=max(rng[d],t)
print(f"  tested {tested}; range violations 0<=t<2^d : {bad}")
print(f"  max t observed per d: {dict(sorted(rng.items()))}  (bound 2^d-1 = {{{', '.join(f'{d}: {2**d-1}' for d in sorted(rng))}}})")

print()
print("=== GATE 2/E: is t_N the binary block of the 2-adic realizer? ===")
print("  for a FIXED integer x realizing the word, r_N = x mod 2^{S_N+1}, so")
print("  t_N = floor((x mod 2^{S_{N+1}+1}) / 2^{S_N+1}) = bits of x at positions S_N+1 .. S_{N+1}")
bad=0; tested=0
for m0 in (7,27,703,26623,159487):
    m=m0; D=[]
    for _ in range(12):
        d=nu2(3*m+1); D.append(d); m=(3*m+1)//2**d
        if m==1: break
    for N in range(1,len(D)):
        W=tuple(D[:N]); W2=tuple(D[:N+1]); SN=sum(W)
        t=(lr(W2)-lr(W))//2**(SN+1)
        blk=( (m0 % 2**(sum(W2)+1)) // 2**(SN+1) )
        tested+=1
        if t!=blk: bad+=1
        if lr(W)!=m0 % 2**(SN+1): bad+=1
print(f"  checked {tested} (word,N) pairs from real positive seeds; mismatches {bad}")

print()
print("=== GATE 5/H: q_N = C_N,  Z_N = -3^{-N} C_N,  xi_N = Z_N mod 2^{S_N} ===")
print("  peeling: -Z_n = sum_{i<n} 3^{-(i+1)} 2^{S_i};  so -3^n Z_n = sum 3^{n-1-i} 2^{S_i} = C_n")
bad=0
for k in range(2,10):
    for W in zcw(k)[:40]:
        N=len(W); S=sum(W); M=2**(S+1)
        inv3=pow(pow(3,N,M),-1,M)
        Z = (-carry(W)*inv3) % M            # Z_N mod 2^{S+1}
        xi = (-carry(W)*pow(pow(3,N,2**S),-1,2**S)) % 2**S
        if Z % 2**S != xi: bad+=1           # xi_N = Z_N mod 2^{S_N}
        if (Z + 2**S) % M != lr(W): bad+=1  # r_N = Z_N + 2^{S_N}  mod 2^{S_N+1}
print(f"  checked identities  xi_N = Z_N mod 2^S_N  and  r_N = (Z_N + 2^{{S_N}}) mod 2^{{S_N+1}} : mismatches {bad}")
print()
print("=== GATE 6/I: half-cylinder selector = the 2^{S_N} bit ===")
W=(1,2,1,1,2); N=len(W); S=sum(W); M=2**(S+1)
Z=(-carry(W)*pow(pow(3,N,M),-1,M))%M
print(f"  W={W}: Z_N mod 2^(S+1) = {Z};  coarse anchor xi_N = Z_N mod 2^S = {Z%2**S}")
print(f"  the two lifts of xi_N to mod 2^(S+1) are {Z%2**S} and {Z%2**S + 2**S}")
print(f"  identity r_N = (Z_N + 2^S) mod 2^(S+1): {(Z + 2**S)%M} == {lr(W)} -> {(Z+2**S)%M == lr(W)}")
print(f"  which lift is selected is decided by bit S of Z_N (here bit {S} of {Z} = {(Z>>S)&1})")
print("  => the terminal top-bit character IS the single bit taking xi_N (mod 2^S_N) to r_N (mod 2^{S_N+1})")

print()
print("=== GATES 3/17/T: negative-integer calibration ===")
def orbit_word(x, steps):
    D=[]; m=x
    for _ in range(steps):
        d=nu2(3*m+1); D.append(d); m=(3*m+1)//2**d
    return D
for x in (-1,-5,-7):
    D=orbit_word(x,10)
    S=0; conf=True
    for j,d in enumerate(D):
        S+=d
        if S>fl(j+1): conf=False
    ts=[]; 
    for N in range(1,len(D)):
        W=tuple(D[:N]); W2=tuple(D[:N+1]); SN=sum(W)
        ts.append((lr(W2)-lr(W))//2**(SN+1))
    maxblk=[2**D[N]-1 for N in range(1,len(D))]
    print(f"  x={x:>3}: word={D[:8]}... zero-confined={conf}")
    print(f"        r_N (N=1..5) = {[lr(tuple(D[:N])) for N in range(1,6)]}")
    print(f"        t_N          = {ts[:7]}")
    print(f"        max block    = {maxblk[:7]}   t_N == max: {ts[:7]==maxblk[:7]}")
print("  => zero confinement + ORDINARY INTEGER realization does NOT imply positivity;")
print("     the sign boundary is visible exactly in the tail: all-zero vs all-max blocks.")

print()
print("=== GATES 12/26/27: zero-corridor lift language, image size, bijectivity ===")
print(f"  {'N':>3} {'#words':>8} {'#distinct r':>12} {'#distinct lambda-prefix':>24} {'bijective?':>11}")
for k in range(6,13):
    Ws=zcw(k)
    rs=set(); lams=set()
    for W in Ws:
        S=sum(W); r=lr(W)
        rs.add((S,r))
        # flattened binary lift stream: bits of r at positions 1..S (bit 0 is always 1, r odd)
        lams.add((S, tuple((r>>b)&1 for b in range(S+1))))
    print(f"  {k:>3} {len(Ws):>8} {len(rs):>12} {len(lams):>24} {str(len(Ws)==len(rs)==len(lams)):>11}")
print("  => D <-> r(D) <-> lambda-prefix is a bijection onto its image (shell injectivity),")
print("     so the lift stream cannot carry MORE information than the valuation word.")

print()
print("=== GATE 31/AA: record-frontier words, terminal zero-run in lambda ===")
print(f"  {'seed':>10} {'N':>3} {'S_N':>4} {'log2 r_N':>9} {'highest 1 bit':>14} {'zero-run below S_N':>19}")
for m0 in (27,703,26623,159487,1017667):
    m=m0; D=[]
    for _ in range(40):
        d=nu2(3*m+1); D.append(d); m=(3*m+1)//2**d
        if m==1: break
    for N in (min(6,len(D)), min(10,len(D))):
        if N<2: continue
        W=tuple(D[:N]); S=sum(W); r=lr(W)
        hi=r.bit_length()-1
        zr=S+1-r.bit_length()
        print(f"  {m0:>10} {N:>3} {S:>4} {math.log2(r):>9.2f} {hi:>14} {zr:>19}")
print("  a long terminal run of ZERO lift bits below S_N+1 is exactly 'r_N is small';")
print("  log2 r_min ~ I_Collatz*N is the statement that this zero-run is ~ (alpha - I)*N bits long.")
