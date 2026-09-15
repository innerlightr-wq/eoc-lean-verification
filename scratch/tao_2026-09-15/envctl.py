"""Parts XXXV-XXXVII: random-index / deterministic-environment model.  Phi_xi = E_P e(sum_{i<J} {xi 2^{S_i} / 3^{i+1}})
over the confined prefix shell P_sigma (uniform paths), for 3-adic environments xi (mod 3^{J+1}):
true 2^{-m} (several m), random, rational/periodic (-1/2, 1/5, 1/7, 1/13), small integers (frozen), Thue-Morse ternary digits,
and 'long-run' environments (random digits with planted runs).  Reports amplitude rate -log2|Phi/P|/J and digit statistics
(fraction of the first J ternary digits lying in runs >= 4 of a repeated digit, block-3 entropy).
usage: python3 envctl.py J sigma"""
import math, random, sys
AL = math.log2(3); random.seed(3)
J, sg = map(int, sys.argv[1:3]); b = [math.floor(j * AL) for j in range(J + 2)]; MOD = 3 ** (J + 1)
g = [dict() for _ in range(J + 1)]; g[J][sg] = 1
for i in range(J - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
def phi(xi):
    val = {sg: 1.0 + 0j}
    for i in range(J - 1, -1, -1):
        mod = 3 ** (i + 1); new = {}; S2s = sorted(val); suf = 0j; wt = 0; k = len(S2s)
        for S in sorted(g[i], reverse=True):
            while k > 0 and S2s[k - 1] > S:
                k -= 1
                if S2s[k] <= b[i + 1]: suf += g[i + 1][S2s[k]] * val[S2s[k]]; wt += g[i + 1][S2s[k]]
            if wt:
                x = (xi * pow(2, S, mod) % mod) / mod
                new[S] = suf / wt * complex(math.cos(2 * math.pi * x), math.sin(2 * math.pi * x))
        val = new
    return abs(val[0])
def digits(xi, n): return [(xi // 3 ** k) % 3 for k in range(n)]
def stats(xi):
    d = digits(xi % MOD, J); inrun = 0; k = 0
    while k < J:
        r = k
        while r < J and d[r] == d[k]: r += 1
        if r - k >= 4: inrun += r - k
        k = r
    from collections import Counter
    c = Counter(tuple(d[k:k + 3]) for k in range(J - 2)); n = sum(c.values())
    H = -sum(v / n * math.log(v / n, 27) for v in c.values())
    return inrun / J, H
envs = []
for m in (107, 108, 150, 200): envs.append((f"2^-{m}", pow(2, -m, MOD)))
for r in range(3): envs.append((f"random{r}", random.randrange(1, MOD)))
for q in (2, 5, 7, 13): envs.append((f"-1/{q}" if q == 2 else f"1/{q}", (-pow(2, -1, MOD)) % MOD if q == 2 else pow(q, -1, MOD)))
for a in (1, 2, 5): envs.append((f"int {a}", a))
tm = [bin(k).count('1') % 2 for k in range(J + 1)]; envs.append(("Thue-Morse", sum((1 + tm[k]) * 3 ** k for k in range(J + 1)) % MOD))
for R in (6, 12):  # random digits with planted runs of 0s of length R every 2R digits
    dd = [0 if (k % (2 * R)) < R else random.randrange(3) for k in range(J + 1)]; dd[0] = 1
    envs.append((f"planted runs {R}", sum(dd[k] * 3 ** k for k in range(J + 1)) % MOD))
print(f"J={J} sigma={sg}: environment -> amplitude rate -log2|Phi/P|/J ; run-fraction(>=4) ; block-3 entropy (1 = max)")
for name, xi in envs:
    v = phi(xi); fr, H = stats(xi)
    print(f"  {name:18s} rate={-math.log2(max(v, 1e-300)) / J:7.4f}   runfrac={fr:.3f}  H3={H:.3f}")
