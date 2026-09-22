#!/usr/bin/env python3
"""Computational support for docs/CHANG_CROSS_SCALE_REALIZER_AUDIT.md.

Standard library only, deterministic. Reproduces every number quoted in that report.

    python3 scratch/chang_cross_scale_audit.py            # gates 2, 11, 26, O/P/Q
    python3 scratch/chang_cross_scale_audit.py univ       # gate 13 (slow: ~10 min to K=11)

Sections:
  2   verify  m_j = 9 (mod 16) <=> (d_j,d_{j+1})=(2,1)  and the mod-32 label <=> d_{j+2}
  11  zero confinement caps Chang burst density at alpha-1
  26  canonical block beta(0)=(2,1,1), beta(1)=(2,1,2) confinement algebra
  13  zero-corridor Chang universality: every label history of length K realizable?
  O/P/Q  same-shell census: do Chang features predict small least realizers?

NOTE: finite data checks identities and already-proved statements. It is NOT evidence
about infinite behaviour, and the universality result below is verified only to K=11.
"""
import math, sys, itertools, statistics
from collections import defaultdict

alpha = math.log2(3)


def floor_ak(k):
    """exact floor(k*log2 3) by integer comparison"""
    v = int(alpha * k)
    while 2 ** (v + 1) <= 3 ** k:
        v += 1
    while 2 ** v > 3 ** k:
        v -= 1
    return v


def carry(D):
    k = len(D); C = 0; s = 0
    for j in range(k):
        C += 3 ** (k - 1 - j) * 2 ** s
        s += D[j]
    return C


def least_realizer(D):
    k = len(D); S = sum(D); M = 2 ** (S + 1)
    return ((2 ** S - carry(D)) * pow(pow(3, k, M), -1, M)) % M


def orbit(D):
    m = least_realizer(D); out = [m]
    for d in D:
        m = (3 * m + 1) // 2 ** d
        out.append(m)
    return out


def zero_confined_words(k):
    caps = [floor_ak(j) for j in range(k + 1)]
    out = []

    def rec(j, s, cur):
        if j == k:
            out.append(tuple(cur)); return
        for d in range(1, caps[j + 1] - s + 1):
            cur.append(d); rec(j + 1, s + d, cur); cur.pop()

    rec(0, 0, [])
    return out


def chang_labels(D):
    """event at j iff (d_j,d_{j+1})==(2,1); label 1 iff d_{j+2}>=2 (m_j = 25 mod 32)"""
    return tuple(1 if D[j + 2] >= 2 else 0
                 for j in range(len(D) - 2) if D[j] == 2 and D[j + 1] == 1)


def gate2():
    print("== 2. Chang observable == 3-digit window of the valuation word ==")
    bad16 = bad32 = tested = 0
    for k in range(3, 11):
        for D in zero_confined_words(k):
            ms = orbit(D)
            for j in range(len(D) - 1):
                tested += 1
                lhs = (ms[j] % 16 == 9); rhs = (D[j], D[j + 1]) == (2, 1)
                if lhs != rhs: bad16 += 1
                if lhs and j + 2 < len(D) and (ms[j] % 32 == 9) != (D[j + 2] == 1):
                    bad32 += 1
    print(f"   positions {tested}; mod-16 mismatches {bad16}; mod-32 label mismatches {bad32}")


def gate11_26():
    print("\n== 11. zero confinement caps Chang burst density ==")
    print(f"   burst = d_t >= 2, so S_k >= k + #bursts; with S_k <= alpha*k:")
    print(f"   burst density <= alpha - 1 = {alpha - 1:.9f}   (Chang reports rho ~ 0.54 typical)")
    print(f"   Chang bit-growth threshold 2 - alpha = {2 - alpha:.9f}; note (alpha-1)+(2-alpha)=1")
    print("\n== 26. canonical block confinement algebra ==")
    print(f"   beta(0)=(2,1,1): drift change 4-3a = {4 - 3 * alpha:+.6f}")
    print(f"   beta(1)=(2,1,2): drift change 5-3a = {5 - 3 * alpha:+.6f}")
    print(f"   intra-block peak above block start: +{2 - alpha:.6f}")
    print(f"   sustainable fraction of 1-labels: c <= 3a-4 = {3 * alpha - 4:.9f}")
    print(f"   S(D(y)) = 4K + w over N = 3K steps")
    print(f"   first-step obstruction: d_0 = 2 but corridor needs S_1 <= floor(a) = {floor_ak(1)}")
    print("   => NO canonical word is itself zero-confined (formalized: changWord_not_zeroConfined)")


def gate13(maxK=11, MAXL=60, DMAX=6):
    print("\n== 13. zero-corridor Chang universality ==")
    caps = [floor_ak(j) for j in range(MAXL + 2)]

    def realizable(y):
        K = len(y); seen = set()

        def rec(j, S, p2, p1, t):
            if t == K: return True
            if j >= MAXL: return False
            key = (j, S, p2, p1, t)
            if key in seen: return False
            seen.add(key)
            for d in range(1, min(caps[j + 1] - S, DMAX) + 1):
                nt = t
                if p2 == 2 and p1 == 1:
                    if (1 if d >= 2 else 0) != y[t]: continue
                    nt = t + 1
                if rec(j + 1, S + d, p1, d, nt): return True
            return False

        return rec(0, 0, None, None, 0)

    for K in range(1, maxK + 1):
        good = sum(1 for y in itertools.product([0, 1], repeat=K) if realizable(y))
        tag = "FULL UNIVERSALITY" if good == 2 ** K else f"missing {2**K - good}"
        print(f"   K={K:>2}: {good}/{2**K}  {tag}")
        sys.stdout.flush()


def gates_OPQ():
    print("\n== O/P/Q. same-shell census: Chang features vs least realizer ==")
    agg = defaultdict(list)
    for k in (12, 13, 14):
        byS = defaultdict(list)
        for D in zero_confined_words(k):
            byS[sum(D)].append(D)
        for S in sorted(byS):
            Ds = byS[S]
            if len(Ds) < 200: continue
            lr = [math.log2(least_realizer(D)) for D in Ds]
            feats = []
            for D in Ds:
                lab = chang_labels(D)
                feats.append(dict(nev=len(lab), n9=sum(1 for l in lab if l == 0),
                                  imbal=sum(2 * l - 1 for l in lab),
                                  absimbal=abs(sum(2 * l - 1 for l in lab)),
                                  rho=sum(1 for d in D if d >= 2) / len(D)))
            idx = sorted(range(len(Ds)), key=lambda i: lr[i])
            nb = max(5, len(Ds) // 10); bot = set(idx[:nb]); rest = idx[nb:]
            for key in ("nev", "n9", "imbal", "absimbal", "rho"):
                xs = [f[key] for f in feats]
                sx = statistics.pstdev(xs); sy = statistics.pstdev(lr)
                if sx == 0 or sy == 0: continue
                mx = statistics.fmean(xs); my = statistics.fmean(lr)
                r = sum((a - mx) * (b - my) for a, b in zip(xs, lr)) / len(xs) / (sx * sy)
                d_eff = (statistics.fmean([xs[i] for i in bot])
                         - statistics.fmean([xs[i] for i in rest])) / sx
                agg[key].append((abs(r), abs(d_eff)))
    print(f"   {'feature':>10} {'max|corr|':>10} {'median|corr|':>13} {'max|Cohen d|':>13} {'shells':>7}")
    for key, v in agg.items():
        rs = [x[0] for x in v]; ds = [x[1] for x in v]
        print(f"   {key:>10} {max(rs):>10.4f} {statistics.median(rs):>13.4f} "
              f"{max(ds):>13.4f} {len(v):>7}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "univ":
        gate13()
    else:
        gate2(); gate11_26(); gates_OPQ()
        print("\n   (run with argument 'univ' for the gate-13 universality search)")
