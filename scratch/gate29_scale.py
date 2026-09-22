"""GATE 7/8/29: the exact scale.  B(D,chi) = C_N + 3^N chi,  realizer <=> 2^{S_N} | B.

Product formula over Q:  |B|_2 * |B|_inf * prod_{p odd} |B|_p = 1, and |B|_p <= 1,
so  2^{v2(B)} <= |B|,  i.e.  v2(B) <= log2|B|.  That is ALL the product formula gives.

Open Problem C needs  v2(B) < S_N  for every chi < 2^{eps N}.
So the required improvement over the trivial/product-formula bound is exactly

    log2|B| - S_N.
"""
import math, random
alpha = math.log2(3)

def C_of(S, N):
    return sum(3**(N-1-i) * (1 << S[i]) for i in range(N))

print("Exact scale of the required improvement over the product-formula bound")
print(f"{'shell S_N/N':>12} {'log2|B|/N':>11} {'S_N/N':>8} {'gap/N':>9} {'v2 needed / log2|B|':>21}")
random.seed(3)
for ratio in [1.0, 1.1, 1.25, 1.4, 1.5, 1.5849]:
    N = 40; eps = 0.05
    # build a word with S_N/N ~= ratio, respecting S_j <= floor(alpha j)
    S=[0]
    for j in range(1, N+1):
        want = ratio*j
        d = max(1, min(4, round(want - S[-1])))
        if S[-1] + d > math.floor(alpha*j): d = math.floor(alpha*j) - S[-1]
        d = max(1, d)
        S.append(S[-1]+d)
    SN = S[N]
    chi = 1 << int(eps*N)
    B = C_of(S, N) + 3**N * chi
    lb = math.log2(B)
    print(f"{SN/N:>12.4f} {lb/N:>11.4f} {SN/N:>8.4f} {(lb-SN)/N:>9.4f} {SN/lb:>21.4f}")

print()
print("asymptotically, with S_N = s*N and chi = 2^{eps N}:")
print("   log2|B| = max(alpha*N + O(log N), alpha*N + eps*N) = (alpha+eps)N + O(log N)")
print("   required improvement = log2|B| - S_N = (alpha + eps - s)N + O(log N)")
print(f"   heavy shell s = alpha = {alpha:.6f}  ->  improvement needed = eps*N   (HARDEST)")
print(f"   light shell s = 1                ->  improvement needed = {alpha-1:.6f}*N + eps*N")
print()
print("GATE 13 - is the multiplicative-order target constrained?")
print("  chi_N  =  (-C_N) * 3^{-N}  mod 2^{S_N};  C_N = sum 3^{N-1-i}2^{S_i} is ODD")
print("  (i=0 term 3^{N-1} odd, all others even).  So the 'target' residue -C_N is an")
print("  arbitrary history-dependent ODD residue mod 2^{S_N}: order of 3 mod 2^m is 2^{m-2},")
print("  the full odd-residue orbit, so the order theorem constrains nothing.")
bad = 0
for _ in range(400):
    N = random.randint(5, 25); S=[0]
    for j in range(1, N+1): S.append(S[-1] + random.choice([1,2,3,4]))
    if C_of(S,N) % 2 != 1: bad += 1
print(f"  C_N odd on 400 random words: violations {bad}")
