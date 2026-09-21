import math
alpha = math.log2(3)
def s_word(d, N): return sum(d[:N])
def q_word(d, N):
    q = 0
    for j in range(N):
        q = 3*q + 2**s_word(d, j)
    return q
def least_realizer(d, N):
    S = s_word(d, N); qN = q_word(d, N); mod = 2**(S+1)
    target = (2**S - qN) % mod
    inv3N = pow(pow(3, N, mod), -1, mod)
    return (target * inv3N) % mod
def actual_word(m0, length):
    d = []; m = m0
    for _ in range(length):
        v = 0; t = 3*m+1
        while t % 2 == 0: t//=2; v+=1
        d.append(v); m = t
    return d
def floorA(n): return math.floor(alpha*n)

# Take a real seed's word for K steps, then deliberately deviate (change one digit,
# keep zero-corridor valid), continue minimally, see how fast r_N departs from m0.
m0 = 6171
K = 8
d_real = actual_word(m0, 40)
print(f"m0={m0}, real word (40 digits): {d_real}")
rs_real = [least_realizer(d_real, N) for N in range(1,41)]
print(f"real r_N: {rs_real}")

for dev_add in [1,2,3]:
    d = d_real[:K]
    S = s_word(d, K)
    # deviate: bump digit K by dev_add if still zero-corridor feasible, else use minimal
    cap = floorA(K+1) - S
    dK = min(d_real[K] + dev_add, cap) if cap>=1 else 1
    if dK < 1: dK = 1
    d.append(dK)
    S += dK
    # continue with minimal digits (d_i=1) to extend
    for n in range(K+2, 41):
        cap = floorA(n) - S
        if cap < 1:
            break
        d.append(1); S += 1
    rs = [least_realizer(d, N) for N in range(1, len(d)+1)]
    print(f"\ndeviate at step {K} by +{dev_add} (digit {d_real[K]}->{dK}): word len {len(d)}")
    print(f"r_N after deviation: {rs}")
    # compare to m0
    print(f"  matches m0? {[r==m0 for r in rs]}")
