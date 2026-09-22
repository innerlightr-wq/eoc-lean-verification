"""GATE 23, corrected.  Build an UNCOUNTABLE family of infinite zero-confined valuation
words with R_n -> -infinity linearly.

Corrected construction: free bit only at every third position.
    d_j = b_{j/3} in {1,2}  if 3 | j,   d_j = 1 otherwise.

Then S_j <= j + floor(j/3), and the zero corridor needs S_j <= floor(alpha j).
"""
import math, random, itertools
alpha = math.log2(3)

def word(bits, L):
    """length-L word: free bit at each position divisible by 3 (1-indexed)."""
    d=[]
    for j in range(1, L+1):
        d.append(bits[j//3 - 1] if j % 3 == 0 else 1)
    return d

def confined(d):
    S=0
    for j,x in enumerate(d, start=1):
        S += x
        if S > math.floor(alpha*j): return False, j, S
    return True, None, S

print("Worst-case check: ALL-2 choice (the extreme member of the family)")
for L in [6, 12, 30, 60, 120, 300, 600]:
    bits=[2]*(L//3+2)
    d=word(bits,L); ok,j,S = confined(d)
    print(f"  L={L:4d}  zero-confined: {str(ok):5s}  S_L={S:4d}  floor(alpha L)={math.floor(alpha*L):4d}  "
          f"R_L={S-alpha*L:8.2f}")

print("\nRandom members")
random.seed(3)
allok=True; worstR=0
for _ in range(3000):
    L=300; bits=[random.choice([1,2]) for _ in range(L//3+2)]
    d=word(bits,L); ok,j,S=confined(d)
    if not ok: allok=False; print("   FAIL at", j, S)
    worstR = max(worstR, S-alpha*L)
print(f"  3000 random members of length 300, all zero-confined: {allok}")
print(f"  least negative R_L observed (worst case): {worstR:.2f}   (all -> -infinity)")

print("\nExhaustive check on all 2^k choices for small depth")
for L in [12, 18, 24]:
    k = L//3
    bad=0; tot=0
    for bits in itertools.product([1,2], repeat=k+1):
        d=word(list(bits),L); ok,_,_ = confined(d)
        tot+=1
        if not ok: bad+=1
    print(f"  L={L:3d}: {tot-bad}/{tot} of all 2^{k+1} members are zero-confined")

print("\nAsymptotics, proved rather than sampled:")
print("  S_j <= j + floor(j/3) <= 4j/3,  and floor(alpha j) >= alpha j - 1.")
print(f"  4/3 = {4/3:.6f}  <  alpha = {alpha:.6f}, gap {alpha-4/3:.6f}")
print(f"  so R_j <= (4/3 - alpha) j = -{alpha-4/3:.4f} j -> -infinity LINEARLY,")
print("  and confinement holds for all j >= 1 (checked exhaustively above for small j,")
print("  and implied by 4j/3 <= alpha j - 1 for j >= 4).")
print("\n  The map (b_i) -> word is injective => the family has cardinality 2^aleph0.")
print("  At most countably many valuation words admit a positive-integer realizer")
print("  (the map positive realizer -> its own word is defined on a countable set).")
print("  => all but countably many members have NO positive-integer realizer,")
print("     while satisfying zero confinement AND R_n -> -infinity linearly.")
