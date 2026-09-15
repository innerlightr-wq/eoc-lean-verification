"""Exact per-step decomposition of the first moment (PROVED MATH identity, measured here).
With B(j,s) = Haar probability of surviving from absolute state (j, S_j = s) to depth N, and
n[j][s] = #{odd mu < X surviving through j with S_j = s}:
   Z_j = sum_s n[j][s] B(j,s),   Z_0 = (X/2) p_N = M_X(N),   Z_N = S_X(N),
   Z_{j+1} - Z_j = sum_s sum_d n[j][s] (nu_{j,s}(d) - 2^-d) B(j+1, s+d)   (nu = empirical next-digit law)
so  Q_X(N) = S_X(N)/M_X(N) = prod_j (1 + eps_j),  eps_j = Z_{j+1}/Z_j - 1  (h-weighted next-digit error).
Poisson benchmark: Var_j = sum_s n[j][s] (sum_d 2^-d B(j+1,s+d)^2 - B(j,s)^2).
usage: python3 product_formula.py file.bin c HI N"""
import struct, sys
from math import floor, log2, sqrt
fn, c, HI, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
JM, SM, DM = 260, 480, 24
raw = open(fn, "rb").read()
import array
arr = array.array("Q"); arr.frombytes(raw)
off_n = 0; off_nd = (JM + 1) * SM
def n(j, s): return arr[off_n + j * SM + s]
def nd(j, s, d): return arr[off_nd + (j * SM + s) * DM + d]
A = log2(3)
def Kf(j):
    s = floor(c + j * A)
    while (1 << (s - c)) > 3 ** j: s -= 1
    return s
K = [10 ** 9] + [Kf(j) for j in range(1, N + 2)]
# Haar survival B(j, s) for s <= K_j
B = [None] * (N + 1)
B[N] = {s: 1.0 for s in range(N, min(K[N], SM - 1) + 1)}
for j in range(N - 1, -1, -1):
    nxt = B[j + 1]; top = K[j + 1]
    vals, t = {}, 0.0
    for s in range(top - 1, j - 1, -1):
        t = 0.5 * (nxt.get(s + 1, 0.0) + t)
        vals[s] = t
    B[j] = {s: vals[s] for s in range(j, (K[j] if j > 0 else 0) + 1) if s in vals}
Bg = lambda j, s: B[j].get(s, 0.0) if j <= N else 0.0
Z, V = [], []
for j in range(N + 1):
    Z.append(sum(n(j, s) * Bg(j, s) for s in range(SM) if n(j, s)))
for j in range(N):
    v = 0.0
    for s in range(SM):
        if n(j, s) == 0: continue
        e2 = sum(2.0 ** -d * Bg(j + 1, s + d) ** 2 for d in range(1, DM))
        v += n(j, s) * (e2 - Bg(j, s) ** 2)
    V.append(v)
X2 = 2 ** (HI - 1)
M = Z[0]; S = Z[N]
Nf = max(j for j in range(1, N + 1) if K[j] + 1 <= HI)
print(f"c={c} X=2^{HI} N={N}: M = Z_0 = {M:.2f} (X/2 p_N check: n[0][0]={n(0,0)}), S = Z_N = {S:.0f}, Q = {S/M:.5f}; fresh-bit depth {Nf}")
eps = [Z[j + 1] / Z[j] - 1 for j in range(N)]
zs = [(Z[j + 1] - Z[j]) / sqrt(V[j]) if V[j] > 0 else 0 for j in range(N)]
print(f"  max |eps_j| over fresh-bit steps j < {Nf}: {max(abs(e) for e in eps[:Nf]):.2e}  (exact identity => 0)")
post = range(Nf, N)
print(f"  post-fresh-bit steps {Nf}..{N-1}: sum eps = {sum(eps[j] for j in post):+.5f}, sum |eps| = {sum(abs(eps[j]) for j in post):.5f},"
      f" log Q = {log2(S/M)/log2(2.718281828):+.5f}")
print(f"  per-step z = dZ_j / sqrt(Var_j): rms {sqrt(sum(zs[j]**2 for j in post)/len(post)):.3f}, mean {sum(zs[j] for j in post)/len(post):+.3f}"
      f"   (cumulative Poisson sd of S: {sqrt(sum(V[j] for j in post)):.1f})")
print("   j    Z_j          eps_j       z_j")
for j in list(range(Nf - 2, Nf + 6)) + list(range(Nf + 10, N, max(1, (N - Nf) // 8))):
    if 0 <= j < N:
        print(f"  {j:3d}  {Z[j]:12.2f}  {eps[j]:+.2e}  {zs[j]:+6.2f}")
