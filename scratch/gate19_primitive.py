"""GATES 18/19/20/25: forced vs excess precision, and the cumulative bound.

From X_j = floor(n_0 / 2^{S_j}):
  v2(a_j - u_j) = d_{j+1} - M_j + M_{j+1}     [forced part + excess]
  excess        = M_{j+1} = v2( floor(n_0 / 2^{S_{j+1}}) )
                = length of the zero-run of n_0 starting at bit S_{j+1}

Claim (disjointness): at a failure, M_{j+1} < d_{j+2}, so the run [S_{j+1}, S_{j+1}+M_{j+1})
ends strictly before S_{j+2}.  Runs at distinct failures are therefore DISJOINT intervals
inside [0, floor(log2 n_0)].  Hence

  sum over failures of M_{j+1}  <=  floor(log2 n_0) + 1
  #failures                     <=  #{j : S_j <= log2 n_0}  <=  log2 n_0.
"""
import math

def v2(n):
    if n == 0: return None
    r = 0
    while n % 2 == 0: n //= 2; r += 1
    return r

def run(n0, cap=4000):
    ds = [0]; m = n0
    for _ in range(cap):
        t = 3*m+1; d = v2(t); m = t >> d; ds.append(d)
        if m == 1 and len(ds) > 3: 
            for _ in range(400): ds.append(2)
            break
    S = [0]
    for j in range(1, len(ds)): S.append(S[-1] + ds[j])
    return ds, S

bad_id = bad_disj = bad_sum = bad_cnt = 0; tot = 0; seeds = 0
worst_ratio = 0.0
for n0 in range(1, 200001, 2):
    ds, S = run(n0)
    lg = n0.bit_length() - 1
    Ms = {}; fails = []
    for j in range(1, len(ds)-1):
        if S[j] > lg: break
        X = n0 >> S[j]
        if X == 0: break
        Ms[j] = v2(X)
        if Ms[j] < ds[j+1]: fails.append(j)
    seeds += 1
    # identity  v2(a-u) = d_{j+1} - M_j + M_{j+1}, checked via X_{j+1} = (X_j - K_j)/2^d
    for j in fails:
        if j+1 not in Ms: continue
        tot += 1
        lhs = ds[j+1] - Ms[j] + Ms[j+1]
        # direct: a-u = 2^{d - M_j} X_{j+1}
        rhs = v2((n0 >> S[j+1]) << (ds[j+1] - Ms[j])) if ds[j+1] >= Ms[j] else None
        if rhs is None or lhs != rhs: bad_id += 1
    # disjointness of the excess runs
    iv = []
    for j in fails:
        if j+1 in Ms: iv.append((S[j+1], S[j+1] + Ms[j+1]))
    iv.sort()
    for (a1,b1),(a2,b2) in zip(iv, iv[1:]):
        if b1 > a2: bad_disj += 1
    tot_excess = sum(Ms[j+1] for j in fails if j+1 in Ms)
    if tot_excess > lg + 1: bad_sum += 1
    if len(fails) > max(lg, 1): bad_cnt += 1
    if lg > 0: worst_ratio = max(worst_ratio, tot_excess / lg)

print(f"seeds tested (odd, < 200001): {seeds}")
print(f"v2(a-u) = d - M_j + M_(j+1)        : mismatches {bad_id} / {tot}")
print(f"excess runs pairwise disjoint      : violations {bad_disj}")
print(f"sum of excess <= floor(log2 n0)+1  : violations {bad_sum}")
print(f"#failures <= log2 n0               : violations {bad_cnt}")
print(f"worst observed  (sum excess)/log2 n0 = {worst_ratio:.4f}")

print("\nGATE 31 negative-witness stress test")
for name, seed2adic, dword in [("-1", -1, 1), ("-5", -5, None)]:
    # n = -1: 3n+1 = -2, d=1, n -> -1.  n = -5: 3(-5)+1 = -14 = -7*2, d=1, -> -7; etc.
    n = seed2adic; ds=[0]; ok=True
    for _ in range(40):
        t = 3*n+1
        if t == 0: ok=False; break
        d = v2(abs(t)); n = t >> d; ds.append(d)
    S=[0]
    for j in range(1,len(ds)): S.append(S[-1]+ds[j])
    Ms=[]
    for j in range(1, 20):
        chi = seed2adic % (1 << S[j])
        X = (seed2adic - chi) // (1 << S[j])
        Ms.append(v2(X) if X != 0 else None)
    print(f"  n0={name:>3}  d-word {ds[1:9]}  M_j {Ms[:8]}  (None = X_j is 0)")
