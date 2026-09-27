"""Structure of cheap 1-confined words = the words of L_1-record seeds (Parts I-VIII, XI-XII, LVIII-LXVI).

By prefix locking / the lift gap, an eps-cheap word of length N is the orbit word of its own least realizer,
so the cheap-word dataset is exactly {word of m : m an L_1-record seed}.  For every record seed we compute
  L_1, L_1/m, log2(m)/L_1 (the cost per step), digit frequencies vs the tilted-geometric law p q^{d-1},
  factor complexity p(k) for k = 1..8 (vs the maximum possible min(#alphabet^k, N-k+1)),
  longest repeated factor, longest border, and the drift depth.
usage: python3 cheap.py MMAX"""
import math, sys
from collections import Counter

AL = math.log2(3); p0 = 1 / AL; q0 = 1 - p0
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000000
NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]

def prefix(m):
    x = m; S = 0; ds = []; Rs = []
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j]: break
        S += a; ds.append(a); Rs.append(S - j * AL); x = v >> a
    return ds, Rs

records = []
best = 0; m = 3
while m <= MMAX:
    x = m; S = 0; j = 0
    while j < NCAP:
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j + 1]: break
        S += a; j += 1; x = v >> a
    if j > best: best = j; records.append((m, j))
    m += 2

def longest_repeated(w):
    n = len(w); bestl = 0
    for L in range(1, n):
        seen = set(); hit = False
        for i in range(n - L + 1):
            f = tuple(w[i:i + L])
            if f in seen: hit = True; break
            seen.add(f)
        if hit: bestl = L
        else: break
    return bestl

def longest_border(w):
    n = len(w)
    for L in range(n - 1, 0, -1):
        if w[:L] == w[n - L:]: return L
    return 0

print(f"L_1-record seeds up to {MMAX} (these are exactly the cheap-word realizers)")
print("      m      L_1   L_1/m   log2m/L_1  maxd  freq(d=1,2,3,>=4)        p(2) p(3) p(4) p(6) p(8)  lrep border  minR")
for m, L in records:
    if L < 10: continue
    ds, Rs = prefix(m)
    c = Counter(ds); n = len(ds)
    fr = [c[1] / n, c[2] / n, c[3] / n, sum(v for k, v in c.items() if k >= 4) / n]
    pk = []
    for k in (2, 3, 4, 6, 8):
        pk.append(len({tuple(ds[i:i + k]) for i in range(n - k + 1)}))
    print(f"{m:9d}  {L:4d}  {L/m:7.4f}  {math.log2(m)/L:8.4f}  {max(ds):3d}  "
          + " ".join(f"{f:.3f}" for f in fr)
          + "   " + " ".join(f"{v:4d}" for v in pk)
          + f"  {longest_repeated(ds):4d} {longest_border(ds):5d}  {min(Rs):6.2f}")
print(f"\ntilted-geometric reference: P(d=1)={p0:.3f} P(d=2)={p0*q0:.3f} P(d=3)={p0*q0**2:.3f} "
      f"P(d>=4)={q0**3:.3f}")
print("max possible p(k) for a length-N word is min(alphabet^k, N-k+1); record words are compared to that.")
# record staircase geometry
print("\nrecord staircase: jumps and plateaus")
print("   m_i        L_1(m_i)   m_{i+1}/m_i   plateau N-range   required floor A = m_i / L_1(m_i)")
for i, (m, L) in enumerate(records):
    if L < 10: continue
    nxt = records[i + 1][0] if i + 1 < len(records) else None
    prevL = records[i - 1][1] if i else 0
    print(f"{m:9d}   {L:4d}      " + (f"{nxt/m:10.2f}" if nxt else f"{'-':>10}")
          + f"     ({prevL+1}..{L})        {m/L:8.3f}")
