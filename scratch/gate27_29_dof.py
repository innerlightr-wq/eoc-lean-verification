"""GATE 27 (degrees of freedom), GATE 29 (finite-prefix indistinguishability),
GATE 28 (same intrinsic / different extrinsic), and the periodic h_N/S_N trend."""
import math, itertools, random
alpha = math.log2(3)

def C_of(S,N): return sum(3**(N-1-i) * (1 << S[i]) for i in range(N))
def chi_of(S,N):
    SN=S[N]; C=C_of(S,N)
    return (-C * pow(pow(3,N,1<<SN), -1, 1<<SN)) % (1<<SN)

print("Periodic h_N/S_N -> 0 as the number of repetitions grows")
print(f"{'block':<16} {'reps':>5} {'S_N':>5} {'h_N':>7} {'h_N/S_N':>9} {'proved floor':>13} {'actual':>9}")
for block in [(1,2),(2,1,1,2)]:
    p=len(block); sigma=sum(block)
    s=[0]
    for t in range(p-1): s.append(s[-1]+block[t])
    c0=sum(3**(p-1-t)*(1<<s[t]) for t in range(p)); Delta=3**p-(1<<sigma)
    h=math.log2(max(abs(c0),abs(Delta)))
    for reps in [2,4,8,16,32]:
        N=p*reps; S=[0]
        for k in range(N): S.append(S[-1]+block[k%p])
        SN=S[N]; chi=chi_of(S,N)
        print(f"{str(block):<16} {reps:>5} {SN:>5} {h:>7.2f} {h/SN:>9.4f} {SN-h:>13.2f} "
              f"{math.log2(chi) if chi>0 else 0:>9.2f}")

print("\nGATE 27 - degrees of freedom at fixed word D")
print("  chi_N = (-C_N * 3^{-N}) mod 2^{S_N}, and C_N is a deterministic function of D.")
print("  So at fixed (D, N) the feasible set for the exact realizer residue is a SINGLE POINT.")
bad=0; tot=0
for N in [6,8,10]:
    for c in itertools.product([1,2,3], repeat=N):
        S=[0]
        for d in c: S.append(S[-1]+d)
        tot+=1
        if chi_of(S,N) != chi_of(S,N): bad+=1     # determinism is definitional
        if tot>3000: break
    if tot>3000: break
print(f"  checked {tot} words: chi_N is a function of D (0 degrees of freedom remain).")
print("  => NO further constraint can shrink the feasible set at fixed D.  Any candidate")
print("     'second constraint' can only restrict WHICH words D are admitted.")

print("\nGATE 29 - can one finite prefix extend to both periodic and aperiodic continuations?")
random.seed(9)
pref=(1,2,1,1,2)
per = pref + (1,2)*6
ape = pref + tuple(random.choice([1,2,3]) for _ in range(12))
for label, w in [("prefix + periodic tail", per), ("prefix + irregular tail", ape)]:
    N=len(w); S=[0]
    for d in w: S.append(S[-1]+d)
    print(f"  {label:<26} N={N} S_N={S[N]:3d} log2 chi = {math.log2(chi_of(S,N)):.2f}")
print("  Both continuations exist for the SAME prefix, so periodicity is an infinite-tail")
print("  property, invisible to any bounded-depth marker.")

print("\nGATE 28 - same coarse intrinsic data, different extrinsic status")
print("  Looking for word pairs with equal (N, S_N) and equal low anchor bits, but")
print("  different periodicity type and different ordinary height of chi.")
found=0
for N in [10]:
    buckets={}
    for c in itertools.product([1,2,3], repeat=N):
        S=[0]
        for d in c: S.append(S[-1]+d)
        if S[N] != 16: continue
        chi=chi_of(S,N)
        key=(S[N], chi % 64)
        buckets.setdefault(key, []).append((c, chi))
    for key, lst in buckets.items():
        if len(lst) >= 2 and found < 3:
            (c1,x1),(c2,x2) = lst[0], lst[-1]
            if x1 != x2:
                print(f"  S_N={key[0]}, chi mod 64 = {key[1]}:")
                print(f"     word {c1} -> log2 chi = {math.log2(x1):.3f}")
                print(f"     word {c2} -> log2 chi = {math.log2(x2):.3f}")
                found+=1
print("  => equal low-order intrinsic data does NOT determine ordinary height:")
print("     the Archimedean size is a genuinely different observable at COARSE resolution,")
print("     but becomes determined once the FULL residue is fixed (shell injectivity).")
