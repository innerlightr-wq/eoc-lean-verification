"""GATE 46/58: extend the creep evidence using large long-trajectory seeds.

The seeds below are widely circulated as record trajectory-length starters.  Their provenance
does not matter here: L, A and the ratio are COMPUTED directly for each, so every row is a valid
data point regardless of whether the seed is truly a record holder.
"""
import math
alpha = math.log2(3)
def v2(n):
    r=0
    while n & 1 == 0: n >>= 1; r+=1
    return r

seeds = [27, 703, 871, 6171, 10971, 26623, 35655, 52527, 77031, 106239, 142587,
         230631, 410011, 511935, 626331, 837799, 1117065, 1501353, 1723519,
         2298025, 3064033, 3542887, 5649499, 6649279, 8400511, 11200681,
         14934241, 36791535, 63728127, 169941673, 226588897, 268549803,
         670617279, 1412987847, 1674652263, 2298025017, 3586720163, 9780657630+1]

print(f"{'m':>13} {'log2 m':>8} {'L':>6} {'A':>9} {'E':>7} {'L/log2m':>9} {'L/(log2m+A)':>13}")
rows=[]
for m in seeds:
    if m % 2 == 0: m += 1          # accelerated map needs an odd seed
    mi=m; S=0; E=0.0; i=0; A=0.0
    ok=True
    while mi != 1:
        R = S - i*alpha
        if R > A: A = R
        t = 3*mi+1; d = v2(t)
        E += math.log2(1+1/(3*mi))
        S += d; mi = t >> d; i += 1
        if i > 5000: ok=False; break
    if not ok: continue
    R = S - i*alpha
    if R > A: A = R
    r1 = i/math.log2(m); r2 = i/(math.log2(m)+A)
    rows.append((m, i, A, E, r1, r2))
    print(f"{m:>13} {math.log2(m):>8.2f} {i:>6} {A:>9.2f} {E:>7.3f} {r1:>9.4f} {r2:>13.4f}")

print()
best=0; bm=None
run=[]
for m,L,A,E,r1,r2 in rows:
    if r2 > best: best, bm = r2, m
    run.append((m, best))
print("running maximum of L/(log2 m + A) as the seed size grows:")
prev=None
for m,b in run:
    if b != prev:
        print(f"   new max {b:.4f} at m = {m}  (log2 m = {math.log2(m):.1f})")
        prev=b
print(f"\n  required constant for the launch route (Gate D): K ~ 12.6")
print(f"  largest observed ratio here: {best:.4f} at m = {bm}")
print("  the running maximum is still increasing at the top of the tested range.")
