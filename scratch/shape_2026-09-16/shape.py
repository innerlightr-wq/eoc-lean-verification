"""Excursion shape cost: does duration add seed cost beyond depth? (Parts IV-XVII, XXII, XLIX-LIII)

Seed-equivalence (prefix locking) again: every "least realizer over words" equals "least seed whose own word
it is", so the frontiers are computed by scanning seeds.
  r_stay(Q,L) = min{ m : within the 1-confined prefix of m, R_j <= -Q for L consecutive steps }
  r_exc(Q,L)  = min{ m : the 1-confined prefix has an excursion below -Q of duration >= L }
Also: exact least realizers of periodic words P^k (word-level, via  m = -C_N 3^{-N} mod 2^{S_N}), the all-ones
benchmark, and the anatomy of seed 27.
usage: python3 shape.py MMAX"""
import math, sys

AL = math.log2(3)
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000000
NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]

def prefix(m):
    x = m; S = 0; ds = []; Rs = []
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        if S + a > top[j]: break
        S += a; ds.append(a); Rs.append(S - j * AL); x = v >> a
    return ds, Rs

QS = [2, 4, 6, 8]
stay = {}; exc = {}
m = 3
while m <= MMAX:
    ds, Rs = prefix(m)
    for Q in QS:
        # longest run of consecutive j with R_j <= -Q
        best = 0; cur = 0
        for R in Rs:
            if R <= -Q: cur += 1; best = max(best, cur)
            else: cur = 0
        if best: stay.setdefault(Q, {})
        for L in range(1, best + 1):
            if L not in stay.get(Q, {}): stay[Q][L] = m
        # excursion below -Q: maximal interval between down-crossing and up-crossing (R <= -Q somewhere inside)
        i = 0; bestE = 0
        while i < len(Rs):
            if Rs[i] <= -Q:
                a = i
                while i < len(Rs) and Rs[i] <= -Q: i += 1
                bestE = max(bestE, i - a)
            else: i += 1
        exc.setdefault(Q, {})
        for L in range(1, bestE + 1):
            if L not in exc[Q]: exc[Q][L] = m
    m += 2

print(f"r_stay(Q,L) = least seed staying below -Q for L consecutive steps (seeds 3..{MMAX})")
print("   Q\\L " + "".join(f"{L:>10d}" for L in (1, 2, 3, 4, 6, 8, 10)))
for Q in QS:
    row = []
    for L in (1, 2, 3, 4, 6, 8, 10):
        v = stay.get(Q, {}).get(L)
        row.append(f"{v:>10d}" if v else f"{'>MMAX':>10}")
    print(f"  {Q:3d} " + "".join(row))
print()
print("log2 r_stay(Q,L) (same table)")
for Q in QS:
    row = []
    for L in (1, 2, 3, 4, 6, 8, 10):
        v = stay.get(Q, {}).get(L)
        row.append(f"{math.log2(v):>10.2f}" if v else f"{'-':>10}")
    print(f"  {Q:3d} " + "".join(row))

# periodic families: exact least realizer of P^k
def least_realizer(ds):
    C = 0; S = 0
    for j, d in enumerate(ds):
        C = 3 * C + (1 << S); S += d
    mod = 1 << S
    return (-C * pow(3, -len(ds), mod)) % mod, S

print("\nperiodic families P^k: exact least realizer (word level)")
print("  pattern        k   len  S     log2 r     drift R_N    log2r/L   log2r/(-R_N)")
for P in ([1], [1, 2], [1, 1, 2], [1, 1, 1, 2], [1, 2, 1, 1, 2], [1, 1, 2, 1, 2]):
    for k in (4, 8, 16):
        ds = P * k
        r, S = least_realizer(ds)
        N = len(ds); R = S - N * AL
        if r == 0: continue
        print(f"  {str(P):<14} {k:3d}  {N:4d} {S:4d}  {math.log2(r):9.2f}  {R:10.3f}  "
              f"{math.log2(r)/N:8.3f}  {(math.log2(r)/(-R) if R < 0 else float('nan')):9.3f}")

# seed 27 anatomy
ds, Rs = prefix(27)
print(f"\nseed 27 anatomy: L_1 = {len(ds)}, word = {''.join(map(str, ds))}")
runs = []; cur = 0
for d in ds:
    if d == 1: cur += 1
    else:
        runs.append(cur); cur = 0
runs.append(cur)
print(f"  d=1 run lengths between gaps: {runs}")
print(f"  #d=1 = {sum(1 for d in ds if d == 1)}, #d>=2 = {sum(1 for d in ds if d >= 2)}, "
      f"max d = {max(ds)}, min R = {min(Rs):.3f}, final R = {Rs[-1]:.3f}")
