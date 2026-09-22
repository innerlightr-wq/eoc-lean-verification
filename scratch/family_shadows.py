"""Does the GATE 23 family satisfy EVERY word-level shadow in the inventory?

Shadows to test on famWord:
  (a) zero confinement                 S_j <= floor(alpha j)   [equivalently 2^{S_j} <= 3^j]
  (b) R_j -> -infinity                 R_j = S_j - alpha j
  (c) sum 2^{R_j} < infinity           (word shadow of Curry's sum 1/m_n < infinity, since
                                        1/m_n = 2^{R_n}/(m_0 Q_n) with Q_n bounded)
  (d) occupation  #{n : R_n >= -G}     Curry: << 2^{beta G} G
"""
import math, random
alpha = math.log2(3)

def famWord(b, i):           # digits indexed from 0
    return (2 if (i//3) in b else 1) if (i+1) % 3 == 0 else 1

def profile(b, L):
    S=[0]
    for i in range(L): S.append(S[-1] + famWord(b, i))
    return S

print(f"{'member':<22} {'confined?':>10} {'R_L/L':>9} {'sum 2^{R_j}':>13} {'#{R_n>=-G}, G=20':>18}")
random.seed(11)
cases = [("all 1 (b empty)", set()),
         ("all 2 (b = N)", set(range(10**6))),
         ("random", {i for i in range(10**6) if random.random()<0.5}),
         ("sparse (b = squares)", {i*i for i in range(2000)}),
         ("periodic (b = evens)", {2*i for i in range(10**6)})]
for name, b in cases:
    L=3000; S=profile(b,L)
    conf = all(S[j] <= math.floor(alpha*j) for j in range(1,L+1))
    conf2 = all((2**S[j]) <= 3**j for j in range(1, 200))   # exact integer form, small j
    R = [S[j]-alpha*j for j in range(L+1)]
    tot = sum(2.0**r for r in R)
    occ = sum(1 for r in R if r >= -20)
    print(f"{name:<22} {str(conf and conf2):>10} {R[L]/L:>9.4f} {tot:>13.4f} {occ:>18}")

print()
print("  (a) zero confinement  : holds for every member (also in the exact integer form 2^S <= 3^j)")
print("  (b) R_j/j -> 4/3 - alpha = -0.2516 at worst, so R_j -> -infinity LINEARLY")
print("  (c) 2^{R_j} <= 2^{-0.2516 j}: geometric, so sum 2^{R_j} < infinity for EVERY member")
print("  (d) R_n >= -G forces n <= G/0.2516 ~ 3.97 G, so #{n : R_n >= -G} = O(G),")
print("      far inside Curry's occupation bound << 2^{beta G} G.")
print()
print("  => every member satisfies EVERY word-level shadow in the inventory,")
print("     yet all but countably many have no positive-integer realizer.")
