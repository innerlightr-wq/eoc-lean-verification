"""Parts I, XXV-XXXII: black-to-black hopping along sampled confined paths (exact integer arithmetic).

Cells: a_i = m - S_i, b_i = i + 1 (i = 0..J-1), m = floor(J alpha) + t + 1, t = J // 6, eta = 1/54; confined law as in
triangle_2026-09-15/triangles.py (uniform over compositions with S_i <= floor(i alpha), S_J = floor(J alpha)).
Step i: cell i -> cell i+1 with digit d_i = S_{i+1} - S_i.  y = centered residue of xi 2^{-a} mod 3^b.
link(i): y_{i+1} = 2^{d_i} y_i  (same triangle; exact characterization, see REPORT).  hop(i): both black, not linked.
Checks: (K) exact transfer kernel y(a-d,b+1) = centered(2^d y + 3^b j), j = -z (-1)^{a-d} mod 3, z = (2^a y - 1)/3^b
(xi = 1 only); (T) every hop has d >= 6; (D) per path n/H <= W + W' + N6 with H = floor(Rmax_path/ln3) + 1.
Q(a,b) = sum_{d>=6} P*(d) 1{(a-d,b+1) black, distinct triangle}; Qb = same without 'distinct'.
usage: python3 hops.py J npaths [xi_mode: true|random]"""
import math, random, sys
from collections import Counter
import statistics as stats

AL = math.log2(3); LN3 = math.log(3); r = 1 - 1 / AL; eta = 1 / 54
w = lambda d: (1 / AL) * r ** (d - 1)
J, NP = int(sys.argv[1]), int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else "true"
random.seed(1000 + J)
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
xi = 1
if mode == "random":
    xi = random.randrange(1, 3 ** (J + 5)) | 1
    xi = xi if xi % 3 else xi + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
# backward counting table in log space (row entries span > 1e308 at J = 1600)
NEG = float("-inf")
def lae(x, y):
    if x == NEG: return y
    if y == NEG: return x
    return max(x, y) + math.log1p(math.exp(-abs(x - y)))
g = [None] * (J + 1); g[J] = [NEG] * (sg + 2); g[J][sg] = 0.0
for i in range(J - 1, -1, -1):
    nxt = g[i + 1]; row = [NEG] * (sg + 2); acc = NEG
    for S in range(top[i + 1], -1, -1):          # row[S] = log sum_{S < S2 <= top[i+1]} exp(nxt[S2])
        row[S] = acc if S <= top[i] else NEG
        acc = lae(acc, nxt[S])
    g[i] = row


def sample_path():
    S = [0]
    for i in range(J):
        s0 = S[-1]; lo, hi = s0 + 1, top[i + 1]
        sl = g[i + 1][lo: hi + 1]; mx = max(sl)
        S.append(random.choices(range(lo, hi + 1), weights=[math.exp(x - mx) for x in sl])[0])
    assert S[-1] == sg
    return S


ycache = {}
def Y(a, b):
    k = (a, b)
    if k not in ycache:
        q = 3 ** b; v = xi * pow(2, -a, q) % q
        ycache[k] = v - q if v > q // 2 else v
    return ycache[k]


def black(a, b): return 54 * abs(Y(a, b)) < 3 ** b          # |y| < eta 3^b
def size(a, b): return math.log(3 ** b / (54 * abs(Y(a, b))))  # ln(eta 3^b / |y|)


def apex(a, b):
    while black(a + 1, b): a += 1
    while black(a, b + 1): b += 1
    return a, b, size(a, b)


st = Counter(); trans = Counter(); hop_digits = Counter(); runs = []; episodes = []; entry_depth = []
kernel_bad = 0; hop_small = 0; det_viol = 0; Qs = []; Qbs = []; dens = []; occ3 = occ6 = 0; cells_tot = 0
bigd_black = Counter()        # (current black?, next black?) for steps with d >= 6
for _ in range(NP):
    S = sample_path()
    a = [m - s for s in S[:J]]; b = [i + 1 for i in range(J)]; d = [S[i + 1] - S[i] for i in range(J - 1)]
    blk = [black(a[i], b[i]) for i in range(J)]
    lnk = [blk[i] and blk[i + 1] and Y(a[i + 1], b[i + 1]) == (1 << d[i]) * Y(a[i], b[i]) for i in range(J - 1)]
    state = []
    for i in range(J):
        if not blk[i]: state.append("W")
        elif i == 0 or not blk[i - 1]: state.append("E")
        elif lnk[i - 1]: state.append("S")
        else: state.append("H")
    for i in range(J - 1):
        trans[(state[i], state[i + 1])] += 1
        if d[i] >= 6: bigd_black[(blk[i], blk[i + 1])] += 1
        if state[i + 1] == "H":
            hop_digits[d[i]] += 1
            if d[i] < 6: hop_small += 1
        if xi == 1:                                             # (K) exact kernel
            yy, q = Y(a[i], b[i]), 3 ** b[i]
            z = ((1 << a[i]) * yy - 1) // q
            jj = (-z * (-1) ** ((a[i] - d[i]) % 2)) % 3
            v = ((1 << d[i]) * yy + q * jj) % (3 * q)
            v = v - 3 * q if v > (3 * q) // 2 else v
            if v != Y(a[i + 1], b[i + 1]): kernel_bad += 1
    st.update(state)
    # runs (maximal linked chains), apex sizes, episodes
    i = 0; rmax_path = 0.0
    while i < J:
        if not blk[i]: i += 1; continue
        e0 = i; ntri = 0
        while i < J and blk[i]:
            s0 = i
            while i < J - 1 and lnk[i]: i += 1
            A = apex(a[s0], b[s0]); rmax_path = max(rmax_path, A[2])
            runs.append((i - s0 + 1, A[2])); entry_depth.append(size(a[s0], b[s0])); ntri += 1
            i += 1
            if i < J and not blk[i]: break
        episodes.append((i - e0, ntri))
    for i in range(J):
        if blk[i]:
            A = apex(a[i], b[i]); cells_tot += 1
            occ3 += A[2] >= 3; occ6 += A[2] >= 6
            if i < J - 1:
                y0 = Y(a[i], b[i]); Q = Qb = 0.0
                for dd in range(6, 41):
                    if black(a[i] - dd, b[i] + 1):
                        Qb += w(dd)
                        if Y(a[i] - dd, b[i] + 1) != (1 << dd) * y0: Q += w(dd)
                Qs.append(Q); Qbs.append(Qb)
    n = J; W = sum(not x for x in blk); W1 = sum(not blk[i + 1] for i in range(J - 1)); N6 = sum(x >= 6 for x in d)
    H = math.floor(rmax_path / LN3) + 1
    if n // H > W + W1 + N6: det_viol += 1
    dens.append((W / n, N6 / (J - 1), H))

tot = sum(st.values()); nsteps = sum(trans.values())
p6 = r ** 5
print(f"J={J} xi={mode} paths={NP} t={t} m={m}: cells {tot}, black fraction {1 - st['W'] / tot:.4f}"
      f"  (states W/E/S/H = {st['W']}/{st['E']}/{st['S']}/{st['H']})")
print(f"  checks: kernel mismatches {kernel_bad} (xi=1 only), hops with d<6: {hop_small}, deterministic-inequality violations {det_viol}/{NP}")
print(f"  mean white density {stats.mean([x[0] for x in dens]):.4f} (min {min(x[0] for x in dens):.4f});"
      f" mean N6/n {stats.mean([x[1] for x in dens]):.5f} (p6 = {p6:.5f}); mean H = {stats.mean([x[2] for x in dens]):.2f}")
bb = bigd_black
nb = bb[(True, True)] + bb[(True, False)]; nw = bb[(False, True)] + bb[(False, False)]
print(f"  steps with d>=6: from black {nb}, next black {bb[(True, True)]} (P = {bb[(True, True)] / max(nb, 1):.4f});"
      f" from white {nw}, next black {bb[(False, True)]} (P = {bb[(False, True)] / max(nw, 1):.4f});  2 eta = {2 * eta:.4f}")
nbs = sum(v for (s1, s2), v in trans.items() if s1 != "W")
hops = sum(v for (s1, s2), v in trans.items() if s2 == "H")
print(f"  distinct-triangle hops {hops} out of {nbs} steps from black: rate {hops / max(nbs, 1):.2e}"
      f"  (random model p6*2eta = {p6 * 2 * eta:.2e}); hop digits {dict(sorted(hop_digits.items()))}")
Qa, Qba = Qs, Qbs
print(f"  Q(a,b) over {len(Qa)} black cells: mean {stats.mean(Qa):.2e}, max {max(Qa):.2e}, max Q/p6 = {max(Qa) / p6:.3f};"
      f"  Qb (any black target): mean {stats.mean(Qba):.2e}, max {max(Qba):.2e}")
L = [x[0] for x in runs]; SZ = [x[1] for x in runs]
frac = lambda xs, c: sum(1 for x in xs if x >= c) / len(xs)
print(f"  runs {len(L)}: mean length {stats.mean(L):.2f}, P(len>=2,4,8,16) = {[round(frac(L, k), 4) for k in (2, 4, 8, 16)]},"
      f" max {max(L)}; run length <= floor(apex/ln3)+1 violated: {sum(1 for l, s in runs if l > math.floor(s / LN3) + 1)}")
print(f"  entry depth (size at run start): mean {stats.mean(entry_depth):.3f} (random model Exp(1) mean 1); "
      f"apex size of visited triangles: mean {stats.mean(SZ):.2f}, P(>=3,6) = {frac(SZ, 3):.3f}, {frac(SZ, 6):.4f}")
E = [x[0] for x in episodes]; NT = [x[1] for x in episodes]
print(f"  episodes {len(E)}: mean length {stats.mean(E):.2f}, max {max(E)}, triangles/episode mean {stats.mean(NT):.4f}, max {max(NT)}")
print(f"  occupation of black cells by apex size >=3: {occ3 / max(cells_tot, 1):.3f}, >=6: {occ6 / max(cells_tot, 1):.4f} (fractions of black cells)")
print("  coarse chain P(next | current):")
for s1 in "WESH":
    row = {s2: trans[(s1, s2)] for s2 in "WESH"}; tt = sum(row.values())
    if tt: print(f"    {s1}: " + "  ".join(f"{s2}:{row[s2] / tt:.4f}" for s2 in "WESH") + f"   (n={tt})")
