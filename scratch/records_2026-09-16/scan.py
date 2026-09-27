"""Full L_1-record staircase to large X, with survivor-sieve statistics (Parts IV-X, XXI-XXIV, XXX-XXXVI).
usage: python3 scan.py XMAX"""
import math, sys
AL = math.log2(3); X = int(sys.argv[1]); NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]
recs = []; best = 0
surv = {}          # depth N -> (count of seeds with L_1 >= N, least such seed)
DEPTHS = [10, 20, 30, 40, 50, 60, 70, 80]
m = 3
while m <= X:
    x = m; S = 0; j = 0
    while j < NCAP:
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j + 1]: break
        S += a; j += 1; x = v >> a
    if j > best:
        best = j; recs.append((m, j))
    for N in DEPTHS:
        if j >= N:
            c, f = surv.get(N, (0, m)); surv[N] = (c + 1, f)
    m += 2
print(f"scan to X = {X}: {len(recs)} records, deepest L_1 = {best}")
print("   i        m_i      N_i    N_i/m_i   m_i/N_i   log2(m_i)/N_i   m_{i+1}/m_i   dN")
for i, (m_, N_) in enumerate(recs):
    nxt = recs[i+1] if i + 1 < len(recs) else None
    print(f"  {i:3d} {m_:11d}  {N_:5d}   {N_/m_:8.4f}  {m_/N_:9.3f}   {math.log2(m_)/N_:10.4f}    "
          + (f"{nxt[0]/m_:9.3f}   {nxt[1]-N_:3d}" if nxt else "       -     -"))
print("\nsurvivor sieve: seeds with L_1 >= N among odd m <= X")
print("   N   #survivors   density      least survivor   1/density")
for N in DEPTHS:
    if N in surv:
        c, f = surv[N]; dens = c / (X / 2)
        print(f"  {N:3d}  {c:10d}   {dens:.3e}   {f:14d}   {1/dens if dens else float('inf'):12.1f}")
