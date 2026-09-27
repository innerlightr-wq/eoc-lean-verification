"""Run statistics, conditional frequencies, block (2-of-9) test and residue patterns of dangerous windows (lambda = 1)."""
import json, math
from collections import Counter
data = json.load(open('windows_lam1.json'))
data.sort(key=lambda d: (d['j'], d['t'], d['K']))
for d in data:
    if d['K'] not in (4, 6, 8): continue
    D = [1 if w['nbad'] > 0 else 0 for w in d['wins']]
    W = len(D); p = sum(D) / W
    if not 0 < p < 1: continue
    p11 = sum(D[i] and D[i+1] for i in range(W-1)) / max(1, sum(D[:-1]))
    p1_2 = sum(D[i] and D[i+2] for i in range(W-2)) / max(1, sum(D[:-2]))
    p111 = sum(D[i] and D[i+1] and D[i+2] for i in range(W-2))
    runs = Counter(); r = 0
    for x in D + [0]:
        if x: r += 1
        elif r: runs[r] += 1; r = 0
    # 9-blocks: max number of dangerous windows in any 9 consecutive windows; fraction of 9-blocks with <= 2
    blocks = [sum(D[i:i+9]) for i in range(W - 8)]
    le2 = sum(1 for b in blocks if b <= 2) / len(blocks)
    # disjoint 9-blocks
    dblocks = [sum(D[i:i+9]) for i in range(0, W - 8, 9)]
    # position of dangerous windows mod 9 / mod 3 / mod 2
    modc = {mm: Counter(i % mm for i, x in enumerate(D) if x) for mm in (2, 3, 9)}
    # expected under independence
    print(f"j={d['j']} t={d['t']} K={d['K']}: W={W} P(D)={p:.3f} P(D+1|D)={p11:.3f} P(D+2|D)={p1_2:.3f} "
          f"#DDD={p111} runs={dict(sorted(runs.items()))} max9={max(blocks)} frac9<=2={le2:.2f} "
          f"disjoint9={Counter(dblocks)} mod3={dict(modc[3])} mod2={dict(modc[2])}")
    # dangerous start states: exponent a = m - x0 residues
    ares = Counter(); cnt = 0
    for w in d['wins']:
        for x0 in w['bad_states']:
            ares[(d['m'] - x0) % 6] += 1; cnt += 1
    print(f"    dangerous (window,state) pairs sampled={cnt}; a mod 6 distribution={dict(sorted(ares.items()))}")
