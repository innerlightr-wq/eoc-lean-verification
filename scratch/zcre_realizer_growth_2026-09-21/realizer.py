def s_word(d, N): return sum(d[:N])

def q_word(d, N):
    q = 0
    for j in range(N):
        q = 3*q + 2**s_word(d, j)
    return q

def least_realizer(d, N):
    S = s_word(d, N)
    qN = q_word(d, N)
    mod = 2**(S+1)
    target = (2**S - qN) % mod
    inv3N = pow(pow(3, N, mod), -1, mod)   # FIX: invert 3^N, not just 3
    x = (target * inv3N) % mod
    return x

def actual_word(m0, length):
    d = []
    m = m0
    for _ in range(length):
        v = 0
        t = 3*m+1
        while t % 2 == 0:
            t//=2; v+=1
        d.append(v)
        m = t
    return d

print("=== Test 1 (fixed): r_N for real seeds vs m0 ===")
for m0 in [3,7,9,11,13,15,27,31,63,127, 837799, 6171]:
    d = actual_word(m0, 60)
    rs = [least_realizer(d, N) for N in range(1,61)]
    ok_le = all(r <= m0 for r in rs)
    stab_N = None
    for N in range(1,61):
        if all(least_realizer(d,k)==m0 for k in range(N,61)):
            stab_N = N; break
    print(f"m0={m0:8d}  all r_N<=m0: {ok_le}  stabilizes at N={stab_N}  r_1..r_12={rs[:12]}")
