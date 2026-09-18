import json, statistics as st
rows = [json.loads(l) for l in open('logk2.jsonl')]
print(f"{len(rows)} environments")
for th in ('0.1', '0.08', '0.12'):
    print(f"\n== dangerous threshold {th}: fraction f_A(j) = #dangerous / W  (max over environments | mean)  [W, K]")
    for A in ('1', '2', '3', '4', '6', '8'):
        line = f"  A={A}: "
        for j in (400, 800, 1600, 3200, 6400):
            rs = [r for r in rows if r['j'] == j and A in r['A']]
            if not rs: line += f" j={j}: --          "; continue
            fr = [r['A'][A]['frac'][th] for r in rs]
            w = max(rs, key=lambda r: r['A'][A]['frac'][th])
            line += f" j={j}: {max(fr):.3f}|{st.mean(fr):.3f} [W={rs[0]['A'][A]['W']},K={rs[0]['A'][A]['K']}]"
        print(line)
print("\nworst environments at theta_d = 0.1 (A=2,3,4):")
for A in ('2', '3', '4'):
    w = max((r for r in rows if A in r['A']), key=lambda r: (r['A'][A]['frac']['0.1'], r['j']))
    print(f"  A={A}: j={w['j']} t={w['t']} lam={w['lam']} frac={w['A'][A]['frac']['0.1']:.3f} count={w['A'][A]['count']['0.1']}/{w['A'][A]['W']} max rate={w['A'][A]['max']:.3f}")
print("\nmax window rate over environments (all A):")
for A in ('1', '2', '3', '4', '6', '8'):
    print(f"  A={A}: " + "  ".join(f"j={j}: {max((r['A'][A]['max'] for r in rows if r['j']==j and A in r['A']), default=float('nan')):.3f}" for j in (400,800,1600,3200,6400)))
