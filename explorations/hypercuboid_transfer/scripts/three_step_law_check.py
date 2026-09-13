"""
Extension of two_step_law_check.py to k=3: verify
P(d_t=q, d_{t+1}=r, d_{t+2}=s) = 2^{-q} 2^{-r} 2^{-s} exactly, by brute force
over a large dyadic block of the single lift parameter k.
"""

def a_val(m):
    x = 3 * m + 1
    q = 0
    while x % 2 == 0:
        x //= 2
        q += 1
    return q

def T_val(m):
    x = 3 * m + 1
    while x % 2 == 0:
        x //= 2
    return x

def orbit_iter(m, t):
    for _ in range(t):
        m = T_val(m)
    return m

def three_step(seed, t, K, qmax=3):
    z0 = orbit_iter(seed, t)
    counts = {}
    N = 2 ** K
    for k in range(N):
        z = z0 + 2 * (3 ** t) * k
        q = a_val(z)
        if q > qmax:
            continue
        w1 = T_val(z)
        r = a_val(w1)
        if r > qmax:
            continue
        w2 = T_val(w1)
        s = a_val(w2)
        if s > qmax:
            continue
        counts[(q, r, s)] = counts.get((q, r, s), 0) + 1
    return counts, N

if __name__ == "__main__":
    for seed, t in [(27, 0), (703, 4)]:
        counts, N = three_step(seed, t, K=18, qmax=3)
        print(f"=== seed={seed} t={t}, N=2^18={N} ===")
        max_err = 0.0
        for q in range(1, 4):
            for r in range(1, 4):
                for s in range(1, 4):
                    c = counts.get((q, r, s), 0)
                    freq = c / N
                    pred = 2.0 ** (-(q + r + s))
                    err = abs(freq - pred)
                    max_err = max(max_err, err)
        print(f"  max |freq - 2^-(q+r+s)| over full q,r,s<=3 table = {max_err:.2e}")
        # spot print a few rows
        for combo in [(1,1,1),(2,1,3),(3,3,1),(1,3,2)]:
            c = counts.get(combo, 0)
            print(f"  {combo}: exact count={c}, freq={c/N:.8f}, predicted={2.0**(-sum(combo)):.8f}")
