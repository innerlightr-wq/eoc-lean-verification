"""Exact distribution of the class-level good-pair-block count at lambda = 1 (the CriticalWhiteCount quantity).

Pair block r = steps (2r, 2r+1).  Class = even prefix sums (S_{2r}); internal choices
B_r = {x : S_{2r} < x < S_{2r+2}, x <= floor((2r+1) alpha)} (Lean `pairB` with b = floor(j alpha)).
Block r is good (Lean `GoodPair` via `distZ_phase_ge_of_white`, proxy d = eta) iff
  |B_r| <= N0  and  exists x with x, x+1 in B_r and the Tao cell (m - x, 2r+2) white (|U| >= eta).
Uniform law over confined words (weights |B_r| per class transition) = the confined law; pair sums u > UMAX
are dropped (their probability is < 1e-12 at UMAX = 30).  Exact big-integer counts.
usage: python3 gb_dp.py J N0 [UMAX]"""
import math, sys

AL = math.log2(3)
J, N0 = int(sys.argv[1]), int(sys.argv[2]); UMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 30
SHAPE = 'shape' in sys.argv[4:]   # control: every cell white (pure digit statistics)
ETA = next((a_[4:] for a_ in sys.argv[4:] if a_.startswith('eta=')), '1/54')   # white iff |U| >= eta
EN, ED = map(int, ETA.split('/'))
assert J % 2 == 0
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
R = J // 2

def white_row(b):   # dict x -> white? for cells (m - x, b), x in [b - 1, top[b-1]]
    q = 3 ** b; row = {}; x0 = b - 1
    rr = pow(2, -(m - x0), q)
    for x in range(x0, top[b - 1] + 2):
        y = rr if rr <= q // 2 else rr - q
        row[x] = True if SHAPE else ED * abs(y) >= EN * q
        rr = rr * 2 % q
    return row

K = math.ceil(0.26 * R) + 1       # counts >= K lumped (only lower-tail thresholds up to 0.25 R are reported)
cur = {0: [1] + [0] * K}          # cur[S_{2r}][g]
M0 = {0: 1}; M1 = {0: 0}          # first-moment DP for the exact mean
for r in range(R):
    wr = white_row(2 * r + 2)     # cells at odd step 2r+1 are (m - x, 2r+2)
    cap = top[2 * r + 1]
    new = {}; newM0 = {}; newM1 = {}
    for S, vec in cur.items():
        for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
            hi = min(S2 - 1, cap)
            nB = hi - S                                     # |B_r|
            if nB <= 0: continue
            good = nB <= N0 and any(wr.get(x, False) for x in range(S + 1, hi) if x + 1 <= hi)
            tgt = new.setdefault(S2, [0] * (K + 1))
            newM0[S2] = newM0.get(S2, 0) + nB * M0[S]
            newM1[S2] = newM1.get(S2, 0) + nB * (M1[S] + (M0[S] if good else 0))
            if good:
                for g in range(K):
                    if vec[g]: tgt[g + 1] += nB * vec[g]
                tgt[K] += nB * vec[K]
            else:
                for g in range(K + 1):
                    if vec[g]: tgt[g] += nB * vec[g]
    cur = new; M0 = newM0; M1 = newM1
dist = cur.get(sg)
Z = sum(dist)
assert M0[sg] == Z
mean = M1[sg] / Z
print(f"J={J} N0={N0} UMAX={UMAX} {'SHAPE-ONLY' if SHAPE else 'true env'} eta={ETA}: #words = 2^{math.log2(Z):.2f}; pair blocks R = {R}; "
      f"mean #good = {mean:.3f} ({mean / R:.4f} R)")
out = []
for frac in (0.02, 0.05, 0.1, 0.15, 0.2, 0.25):
    k = math.ceil(frac * R)
    c = sum(dist[:k])
    out.append(f"P(#good < {frac}R) = " + ("0" if c == 0 else f"2^-{math.log2(Z) - math.log2(c):.2f} (rate/step {(math.log2(Z) - math.log2(c)) / J:.4f})"))
print("   " + "; ".join(out))
print(f"   min #good over all words = {next(g for g, c in enumerate(dist) if c)}")
