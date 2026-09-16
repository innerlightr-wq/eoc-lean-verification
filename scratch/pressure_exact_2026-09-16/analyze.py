"""Summarise corpus_J.json: exact pressures (d = 1/108 and 1/54), certification counts, window maxima."""
import json, sys, statistics as st
KS = ('16', '24', '32', '64', '128')
def q(v, p): v = sorted(v); return v[min(len(v) - 1, int(p * len(v)))]
for J in sys.argv[1:]:
    try: rows = json.load(open(f'corpus_{J}.json'))
    except FileNotFoundError: continue
    print(f"== J = {J}: {len(rows)} instances (odd lam, t in {sorted({r['t'] for r in rows})})")
    for D in ('108', '54'):
        P = [r[D]['P'] for r in rows]
        c17 = sum(r[D]['lt017'] for r in rows); c16 = sum(r[D]['lt16'] for r in rows)
        w = max(rows, key=lambda r: r[D]['P'])
        print(f"  d=1/{D}: P max {max(P):.5f} (lam={w['lam']}, t={w['t']})  median {st.median(P):.5f}  q99 {q(P,.99):.5f}"
              f"  | certified < 17/100: {c17}/{len(rows)}, < 1/6: {c16}/{len(rows)}")
    for K in KS:
        vals = [(r['108']['win'][K][0], r) for r in rows if K in r['108']['win']]
        if not vals: continue
        v = [a for a, _ in vals]; best, br = max(vals, key=lambda z: z[0])
        over = sum(1 for a in v if a > 0.17)
        print(f"  K={K:>3}: window rate max {best:.4f} (lam={br['lam']}, t={br['t']}, r0={br['108']['win'][K][1]})"
              f"  median {st.median(v):.4f}  q90 {q(v,.9):.4f}  q99 {q(v,.99):.4f}  #>0.17: {over}")
