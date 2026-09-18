import json, statistics as st
rows = [json.loads(l) for l in open('shifts.jsonl')]
def q(v, p): v = sorted(v); return v[min(len(v) - 1, int(p * len(v)))]
print(len(rows), "environments")
for j in (400, 800, 1600):
    for kind, A, sel in (('lam1 consecutive', 2, lambda r: r['kind'] == 'lam1' and r['A'] == 2 and j // 6 <= r['t'] < j // 6 + 400),
                         ('lam1 scattered', 2, lambda r: r['kind'] == 'lam1' and r['A'] == 2 and not (j // 6 <= r['t'] < j // 6 + 400)),
                         ('haar', 2, lambda r: r['kind'] == 'haar'),
                         ('lam1 A=5', 5, lambda r: r['kind'] == 'lam1' and r['A'] == 5)):
        rs = [r for r in rows if r['j'] == j and sel(r)]
        if not rs: continue
        F = [r['frac'] for r in rs]; M = [r['max_rate'] for r in rs]
        w = max(rs, key=lambda r: (r['frac'], r['max_rate']))
        print(f"j={j} {kind:17s} n={len(rs):3d} W={rs[0]['W']:3d} K={rs[0]['K']}: F max {max(F):.3f} mean {st.mean(F):.4f} "
              f"frac(F>0) {sum(f > 0 for f in F)/len(F):.3f} frac(F>2/9) {sum(f > 2/9 for f in F)/len(F):.3f} | "
              f"max rate max {max(M):.4f} q90 {q(M,.9):.4f} median {st.median(M):.4f} | max run {max(r['max_run'] for r in rs)} "
              f"| worst t={w['t']} ({w['bad']} bad, rate {w['max_rate']:.4f})")
# autocorrelation of max_rate over consecutive t
for j in (400, 800, 1600):
    rs = sorted((r for r in rows if r['j'] == j and r['kind'] == 'lam1' and r['A'] == 2 and j // 6 <= r['t'] < j // 6 + 400), key=lambda r: r['t'])
    x = [r['max_rate'] for r in rs]; m = st.mean(x); v = st.pvariance(x)
    ac = [sum((x[i] - m) * (x[i + k] - m) for i in range(len(x) - k)) / ((len(x) - k) * v) for k in (1, 2, 5, 10)]
    print(f"j={j}: autocorrelation of max window rate over consecutive t, lags 1,2,5,10: " + ", ".join(f"{a:.2f}" for a in ac))
