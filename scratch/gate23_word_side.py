"""WORD side (where Open Problem C actually lives).

chi_N = (-C_N 3^{-N}) mod 2^{S_N},  C_N = sum_{i<N} 3^{N-1-i} 2^{S_i}
chi_N = chi  <=>  2^{S_N} | B(D,chi) := C_N + 3^N chi.

GATE 23 (periodic calibration).  For a purely periodic word of period p, block (e_1..e_p),
sigma = sum e_t, partial sums s_t:
      c_0 := sum_{t<p} 3^{p-1-t} 2^{s_t},   Delta := 3^p - 2^sigma  (odd)
      C_{Np} = c_0 (3^{Np} - 2^{N sigma}) / Delta
and the condition collapses to the FIXED-COMPLEXITY divisibility
      2^{N sigma} | (c_0 + chi * Delta).
Both c_0 and Delta are independent of N: three terms, no growth.

GATE 32 (scaling).  For irregular confined words measure v2(B)/log2|B|.
"""
import math, random

def v2(n):
    if n == 0: return None
    r = 0
    while n % 2 == 0: n //= 2; r += 1
    return r

def C_of(S, N):
    return sum(3**(N-1-i) * (1 << S[i]) for i in range(N))

print("GATE 23 - periodic closed form")
bad = 0; tot = 0
for block in [(1,), (2,), (1,2), (2,1), (1,1,4), (3,1,2), (2,2,1,1), (1,4,1,2,2)]:
    p = len(block); sigma = sum(block)
    s = [0]
    for t in range(p-1): s.append(s[-1] + block[t])
    c0 = sum(3**(p-1-t) * (1 << s[t]) for t in range(p))
    Delta = 3**p - (1 << sigma)
    for Nrep in range(1, 7):
        N = Nrep * p
        S = [0]
        for k in range(N): S.append(S[-1] + block[k % p])
        C = C_of(S, N)
        pred = c0 * (3**N - (1 << (Nrep*sigma))) // Delta if Delta != 0 else None
        tot += 1
        if Delta == 0 or C != pred: bad += 1; print("   closed form FAILS", block, N)
    # the collapsed divisibility, checked against the direct chi
    N = 5*p; S=[0]
    for k in range(N): S.append(S[-1]+block[k%p])
    C = C_of(S,N); SN = S[N]
    chi = (-C * pow(pow(3,N,1<<SN), -1, 1<<SN)) % (1 << SN)
    lhs = (c0 + chi*Delta) % (1 << SN)
    print(f"  block {str(block):14s} p={p} sigma={sigma} c0={c0:6d} Delta={Delta:8d}  "
          f"chi={chi}  2^S_N | (c0+chi*Delta)? {lhs==0}   log2(chi)/S_N={math.log2(chi)/SN if chi>0 else 0:.4f}")
print(f"  periodic closed form C_Np = c0(3^Np - 2^Nsigma)/Delta : {tot-bad}/{tot} exact")

print("\nGATE 32 - irregular confined words: how close does v2(B) get to log2|B|?")
alpha = math.log2(3)
random.seed(11)
print(f"{'N':>4} {'words':>7} {'max v2(B)/log2|B|':>19} {'needed for a realizer':>22} {'max log2(chi)/S_N':>19}")
for N in [12, 18, 24, 30]:
    best = 0.0; need = 0.0; smallest = 1.0; nw = 0
    for _ in range(3000):
        S=[0]; ok=True
        for j in range(1, N+1):
            d = random.choice([1,1,2,2,3,4])
            S.append(S[-1]+d)
            if S[-1] > math.floor(alpha*j): ok=False; break     # zero-corridor confinement
        if not ok: continue
        nw += 1
        C = C_of(S, N); SN = S[N]
        chi = (-C * pow(pow(3,N,1<<SN), -1, 1<<SN)) % (1 << SN)
        B = C + 3**N * chi
        val = v2(B); 
        if val is None: continue
        best = max(best, val/math.log2(B))
        need = max(need, SN/math.log2(B))
        smallest = min(smallest, math.log2(chi)/SN if chi>0 else 0)
    print(f"{N:>4} {nw:>7} {best:>19.4f} {need:>22.4f} {smallest:>19.4f}")
