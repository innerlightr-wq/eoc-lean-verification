"""GATE 8/10/19/20/21: reconstruct B_N exactly and find what links its two norms.

From the previous branch:  chi_N = chi  <=>  2^{S_N} | B(D,chi) := C_N + 3^N chi,
with C_N = sum_{i<N} 3^{N-1-i} 2^{S_i}.

CLAIM: if chi realizes the word D for N steps, with accelerated iterates m_0 = chi,
m_{j+1} = (3 m_j + 1)/2^{d_{j+1}}, then

        B(D, chi)  =  2^{S_N} * m_N        with m_N odd and positive.

Consequences, if true:
  v2(B)        = S_N          EXACTLY (not merely >=)
  log2|B|      = S_N + log2 m_N
  log2|B| - v2(B) = log2 m_N  <-- the "Archimedean-2-adic gap" is an EXACT identity
  rad(B) = 2 * rad(m_N)       <-- odd-prime support is that of an arbitrary odd integer

Also test the dual 3-adic form:  2^{S_N} m ≡ C_N (mod 3^N), so m ≡ C_N 2^{-S_N} (mod 3^N).
"""
import math, random

def v2(n):
    if n == 0: return None
    r = 0
    while n % 2 == 0: n //= 2; r += 1
    return r

def word_of(n0, N):
    ds=[0]; m=n0
    for _ in range(N):
        t=3*m+1; d=v2(t); m=t>>d; ds.append(d)
    return ds

bad_id=bad_v2=bad_odd=bad_dual=0; tot=0
worst_pos_margin = -1e9
for n0 in range(1, 20001, 2):
    N = random.Random(n0).randint(3, 22)
    ds = word_of(n0, N)
    S=[0]
    for j in range(1,N+1): S.append(S[-1]+ds[j])
    C = sum(3**(N-1-i) * (1 << S[i]) for i in range(N))
    B = C + 3**N * n0
    # iterate forward
    m = n0
    for j in range(1, N+1): m = (3*m+1) >> ds[j]
    tot += 1
    if B != (1 << S[N]) * m: bad_id += 1
    if m % 2 != 1: bad_odd += 1
    if v2(B) != S[N]: bad_v2 += 1
    # dual 3-adic residue
    mstar = (C * pow(pow(2, S[N], 3**N), -1, 3**N)) % 3**N
    if (m - mstar) % 3**N != 0: bad_dual += 1
    # GATE 23: what does positivity m >= 1 give as a lower bound on chi?
    pos_bound = ((1 << S[N]) - C) / 3**N        # chi >= this, from m >= 1
    worst_pos_margin = max(worst_pos_margin, pos_bound)

print(f"words tested: {tot}")
print(f"B(D,chi) = 2^(S_N) * m_N            : mismatches {bad_id}")
print(f"m_N odd                             : violations {bad_odd}")
print(f"v2(B) = S_N EXACTLY                 : violations {bad_v2}")
print(f"m_N = C_N * 2^(-S_N) mod 3^N        : violations {bad_dual}")
print(f"\nGATE 23 positivity: chi >= (2^S_N - C_N)/3^N.")
print(f"  largest value that bound ever takes = {worst_pos_margin:.6f}")
print(f"  (anything < 1 is VACUOUS, since chi >= 1 is already known)")

print("\nGATE 21 odd-prime support of B_N = 2^{S_N} m_N:")
def rad_small(n, lim=10**7):
    f=[]; d=3
    while d*d<=n and d<lim:
        if n%d==0:
            f.append(d)
            while n%d==0: n//=d
        d+=2
    if n>1: f.append(n)
    return f
for n0 in [7, 27, 97, 871]:
    N=10; ds=word_of(n0,N); S=[0]
    for j in range(1,N+1): S.append(S[-1]+ds[j])
    m=n0
    for j in range(1,N+1): m=(3*m+1)>>ds[j]
    print(f"  n0={n0:5d} N={N}  S_N={S[N]:3d}  m_N={m:8d}  odd primes of m_N: {rad_small(m)}")
