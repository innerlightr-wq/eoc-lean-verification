#!/usr/bin/env python3
"""
Scratch computational experiment (NOT part of the tracked source tree).

Tests the exact algebraic interface between the EOC realizer/carry coordinate
and Edward Y. Chang's bit-4 observable (9 vs 25 mod 32 at burst-ending times),
per arXiv:2603.25753.

Makes NO theorem claims. Pure finite-state / numerical audit.

Accelerated map:      T(m) = (3m+1) / 2^{v2(3m+1)}
Valuation word:       d_j = v2(3 m_j + 1)
Prefix sums:          S_j = sum_{i<j} d_i          (S_0 = 0)
Carry:                C_N = sum_{j=0}^{N-1} 3^{N-1-j} 2^{S_j}
                      recurrence: C_0 = 0, C_{n+1} = 3 C_n + 2^{S_n}
EOC identity (Carry.lean q_eq_C + iter_carry_eq):
                      2^{S_N} m_N = 3^N m_0 + C_N
"""

import random
import math
from collections import Counter, defaultdict

# --------------------------------------------------------------------------
# primitives
# --------------------------------------------------------------------------

def v2(n: int) -> int:
    return (n & -n).bit_length() - 1

def accel_traj(n: int, cap: int = 5_000_000):
    """Full accelerated trajectory [n0, n1, ..., 1]. (T(1)=1 -> stop.)"""
    s = [n]
    while s[-1] != 1:
        x = 3 * s[-1] + 1
        s.append(x >> v2(x))
        if len(s) > cap:
            break
    return s

def dstep(seq, j):
    """d_j for the trajectory; past reaching 1 the state is 1 and d = v2(4) = 2."""
    if j < len(seq) - 1:
        return v2(3 * seq[j] + 1)
    return 2

def h_bern(p: float) -> float:
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)

# --------------------------------------------------------------------------
# seed sets
# --------------------------------------------------------------------------

SMALL_SEEDS = list(range(3, 1_000_001, 2))          # 500k odd seeds
random.seed(20260903)
BIG_SEEDS = [random.randrange(1 << 220, 1 << 260) | 1 for _ in range(40)]

# ==========================================================================
# TEST 1 — mod-32 realizer identity, head and tail
# ==========================================================================

def test1():
    print("=" * 70)
    print("TEST 1 — mod-32 realizer identity  m_k = -C_N * 3^{-N}  (mod 32),  S_N>=5")
    print("=" * 70)

    mod_checks = 0
    mod_exc = []
    exact_checks = 0
    exact_exc = []

    # (a) small seeds: head + tail, plus exact big-integer identity cross-check
    for n0 in SMALL_SEEDS[:4000]:
        seq = accel_traj(n0)
        T = len(seq) - 1
        for k in range(0, min(T, 40)):
            S = 0
            Cm = 0                      # C_N mod 32
            Cfull = 0                   # exact C_N   (only when do_exact)
            do_exact = (n0 < 6000 and k < 6)
            hits = 0
            for j in range(0, min(T - k + 6, 160)):
                dj = dstep(seq, k + j)
                Cm = (3 * Cm + pow(2, S, 32)) % 32
                if do_exact:
                    Cfull = 3 * Cfull + (1 << S)
                S += dj
                Nn = j + 1
                if S >= 5:
                    hits += 1
                    inv = pow(3, -Nn, 32)
                    pred = (-Cm * inv) % 32
                    act = seq[k] % 32
                    mod_checks += 1
                    if pred != act:
                        mod_exc.append((n0, k, Nn, pred, act))
                    if do_exact:
                        nkN = seq[k + Nn] if k + Nn < len(seq) else 1
                        lhs = (1 << S) * nkN
                        rhs = 3 ** Nn * seq[k] + Cfull
                        exact_checks += 1
                        if lhs != rhs:
                            exact_exc.append((n0, k, Nn))
                    if hits >= 6:
                        break

    # (b) large seeds: long trajectories, mod-only, head + several tails
    for n0 in BIG_SEEDS:
        seq = accel_traj(n0)
        T = len(seq) - 1
        for k in list(range(0, min(T, 30))) + list(range(30, T, max(1, T // 60))):
            S = 0
            Cm = 0
            hits = 0
            for j in range(0, min(T - k + 6, 400)):
                dj = dstep(seq, k + j)
                Cm = (3 * Cm + pow(2, S, 32)) % 32
                S += dj
                Nn = j + 1
                if S >= 5:
                    hits += 1
                    pred = (-Cm * pow(3, -Nn, 32)) % 32
                    act = seq[k] % 32
                    mod_checks += 1
                    if pred != act:
                        mod_exc.append((n0, k, Nn, pred, act))
                    if hits >= 5:
                        break

    total_steps = sum(len(accel_traj(s)) - 1 for s in BIG_SEEDS)
    print(f"  big-seed trajectory steps (sum)      : {total_steps}")
    print(f"  mod-32 identity checks               : {mod_checks}")
    print(f"  mod-32 identity exceptions           : {len(mod_exc)}")
    if mod_exc:
        print("   ", mod_exc[:10])
    print(f"  exact  2^S n_N == 3^N n_0 + C_N checks: {exact_checks}")
    print(f"  exact  identity exceptions           : {len(exact_exc)}")
    if exact_exc:
        print("   ", exact_exc[:10])
    print()
    return len(mod_exc) == 0 and len(exact_exc) == 0

# ==========================================================================
# TEST 2 — C_N mod 64 reduces to a short prefix
# ==========================================================================

def prefix_pattern(word, bound):
    """
    Partial sums S_j that stay < bound, as a tuple, plus r = first index with S_r>=bound.
    Only word entries d_0..d_{r-1} are consulted.
    Returns (tuple_of_partial_sums_below_bound, r, tuple_of_consulted_valuations).
    """
    sums = []
    S = 0
    r = 0
    used = []
    while S < bound:
        sums.append(S)
        S += word[r]
        used.append(word[r])
        r += 1
    return tuple(sums), r, tuple(used)

def CN_mod_from_prefix(Nmod16, patt, M=64):
    """C_N mod M from (N mod 16, partial-sum pattern), using ord_16(3) mod 64."""
    r = len(patt)
    tot = 0
    for j, Sj in enumerate(patt):
        # exponent  N-1-j  ; only its value mod 16 matters mod 64 (ord_64(3)=16)
        e = (Nmod16 - 1 - j) % 16
        tot = (tot + pow(3, e, M) * pow(2, Sj, M)) % M
    return tot % M

def test2():
    print("=" * 70)
    print("TEST 2 — C_N mod 64 as a function of (N mod 16, short valuation prefix)")
    print("=" * 70)

    print("""  Modular reason (derived, not observed):
    * C_N mod 64: a term 3^{N-1-j} 2^{S_j} is 0 mod 64 iff S_j >= 6.
    * S_j is strictly increasing (every d_i >= 1) and S_j >= j, so the first
      index r with S_j >= 6 satisfies r <= 6, and only j < r contribute.
    * ord_64(3) = 16  (3^16 = 1 + 64*k), so 3^{N-1-j} mod 64 depends only on
      (N-1-j) mod 16, i.e. on N mod 16 and j.
    * The contributing partial sums 0 = S_0 < S_1 < ... < S_{r-1} <= 5 form a
      subset A of {0,1,2,3,4,5} with 0 in A: 2^5 = 32 such subsets.
    => C_N mod 64 = f(N mod 16, A),  at most 16 * 32 = 512 finite states.""")

    seen = {}
    mism = 0
    checks = 0
    distinct_states = set()
    distinct_vals = set()

    src = SMALL_SEEDS[:20000] + BIG_SEEDS
    for n0 in src:
        seq = accel_traj(n0)
        T = len(seq) - 1
        for k in range(0, min(T, 30)):
            word = [dstep(seq, k + j) for j in range(0, 40)]
            if sum(word) < 6:
                continue
            patt, r, used = prefix_pattern(word, 6)
            # test several N (>= r so S_N >= 6)
            for Nn in [r, r + 1, r + 3, r + 7, r + 16, max(r, T - k)]:
                # full recurrence C_N mod 64
                S = 0
                Cm = 0
                for j in range(Nn):
                    dj = word[j] if j < len(word) else 2
                    Cm = (3 * Cm + pow(2, S, 64)) % 64
                    S += dj
                # prefix-only formula
                Cp = CN_mod_from_prefix(Nn % 16, patt, 64)
                checks += 1
                if Cm != Cp:
                    mism += 1
                key = (Nn % 16, patt)
                distinct_states.add(key)
                distinct_vals.add(Cm)
                if key in seen and seen[key] != Cm:
                    print("   INCONSISTENT STATE:", key, seen[key], Cm)
                seen[key] = Cm

    print(f"  full-vs-prefix agreement checks       : {checks}")
    print(f"  mismatches (full C_N%64 vs prefix)    : {mism}")
    print(f"  distinct (N%16, A) states observed    : {len(distinct_states)}  (<= 512)")
    print(f"  distinct C_N%64 values observed       : {len(distinct_vals)}")
    print(f"  state -> C_N%64 single-valued         : {'YES' if mism==0 else 'NO'}")
    print()
    return mism == 0

# ==========================================================================
# TEST 3 — Chang bit as a finite-state observable
# ==========================================================================

def forward_pattern_from_residue(r, bound=5):
    """
    Partial-sum pattern A (sums < bound) of the forward valuation word,
    computed from r = m mod 32 only.  Valid because a step's valuation is
    known from n mod 32 whenever it is < 5, and once it is >= 5 (i.e.
    3n+1 == 0 mod 32) we have already crossed `bound`.
    """
    n = r % 32
    S = 0
    A = []
    while S < bound:
        A.append(S)
        t = (3 * n + 1) % 32
        d = 5 if t == 0 else v2(t)      # cap: d>=5 all behave identically here
        # advance n mod 32 by one accelerated step (only defined when d<5;
        # when d>=5 we stop on next loop test since S+d >= bound)
        if d < 5:
            n = ((3 * n + 1) >> d) % 32
        S += d
    return tuple(A)

def test3():
    print("=" * 70)
    print("TEST 3 — Y (bit 4) as a deterministic function of the forward prefix")
    print("=" * 70)

    # (i) bijection  odd residue mod 32  <->  forward partial-sum pattern (sums<5)
    patt2res = {}
    res2patt = {}
    for r in range(1, 32, 2):
        A = forward_pattern_from_residue(r, 5)
        res2patt[r] = A
        patt2res.setdefault(A, set()).add(r)
    bij = all(len(v) == 1 for v in patt2res.values()) and len(patt2res) == 16
    print(f"  odd-residue(mod32) <-> forward-pattern(sums<5) is a bijection: {bij}")
    print(f"  #distinct patterns: {len(patt2res)}  (16 odd residues)")
    print("  full table  [ m mod 32 : pattern A of partial sums < 5 ]:")
    for r in range(1, 32, 2):
        tag = ""
        if r == 9:
            tag = "   <- Chang Y=0"
        if r == 25:
            tag = "   <- Chang Y=1"
        print(f"     {r:2d} : {list(res2patt[r])}{tag}")

    # (ii) cross-check via the -C*3^{-r} formula (independent of forward sim)
    ok = 0
    for r in range(1, 32, 2):
        A = res2patt[r]
        rr = len(A)
        # C_r mod 32 from pattern with N = r (canonical); exponent (r-1-j) mod 8
        C = 0
        for j, Sj in enumerate(A):
            C = (C + pow(3, (rr - 1 - j) % 8, 32) * pow(2, Sj, 32)) % 32
        pred = (-C * pow(3, -rr, 32)) % 32
        ok += (pred == r)
    print(f"  -C_r*3^{{-r}} formula reproduces m mod 32 for all 16 residues: {ok == 16}")

    # (iii) Y lookup as (N mod 16, forward prefix) -- collect from real burst-ends
    #       (populated in Test 4); here just print the reduced table.
    print()
    print("  Reduced deterministic table for Chang's channel (n = 9 mod 16):")
    print("     m mod 32 = 9   <=>  forward valuations (d0,d1,d2,..) = (2,1,1,2,...) "
          "<=>  pattern (0,2,3,4)  ->  Y = 0")
    print("     m mod 32 = 25  <=>  forward valuations (d0,d1,d2,..) = (2,1,3,...)   "
          "<=>  pattern (0,2,3)    ->  Y = 1")
    print("     distinguishing quantity: d2 (3rd forward valuation) == 1  vs  >= 2")
    print("     i.e. bit4(m_t)  <=>  (m_{t+2} mod 4 == 3)      [forward, 2 accel steps]")
    print()
    return bij and ok == 16

# ==========================================================================
# TEST 4 — Chang burst-ending selection
# ==========================================================================
# Chang (arXiv:2603.25753):
#   X_t = 1[ n_t = 1 mod 4 ] = 1[ v2(3 n_t + 1) >= 2 ]        (burst step)
#   X_t = 0                                                    (gap step, d_t = 1)
#   sequence splits as 1^{L_1} 0^{G_1} 1^{L_2} 0^{G_2} ...
#   burst-ending time: X_t = 1, X_{t+1} = 0, and n_t = 1 mod 8
#   Lemma 4.1 / eq (8-9):
#     bit4(n_t)=0  <=>  n_t = 9  mod 32  <=>  following gap run G >= 2
#     bit4(n_t)=1  <=>  n_t = 25 mod 32  <=>  following gap run G  = 1

def collect_burst_ends(seeds):
    events = []
    for n0 in seeds:
        seq = accel_traj(n0)
        T = len(seq) - 1
        if T < 3:
            continue
        X = [1 if dstep(seq, j) >= 2 else 0 for j in range(T)]      # j = 0..T-1
        j = 0
        while j < T:
            if X[j] == 1:
                # burst run [bstart, j]
                bstart = j
                while j < T and X[j] == 1:
                    j += 1
                bend = j - 1            # last burst step
                L = bend - bstart + 1
                if j < T and X[j] == 0:
                    # gap run starts at j
                    gstart = j
                    while j < T and X[j] == 0:
                        j += 1
                    G = j - gstart
                    t = bend
                    nt = seq[t]
                    if nt % 8 == 1:
                        # forward tail word from t
                        word = [dstep(seq, t + i) for i in range(0, 40)]
                        patt6, r6, used6 = prefix_pattern(word, 6)
                        patt5, r5, used5 = prefix_pattern(word, 5)
                        Nnat = T - t          # steps for the tail to reach 1
                        suf = tuple(dstep(seq, t - i) for i in range(0, 4))  # d_t, d_{t-1}, d_{t-2}, d_{t-3}
                        events.append(dict(
                            n0=n0, t=t, nt=nt,
                            m32=nt % 32, m64=nt % 64, m16=nt % 16,
                            Y=(0 if nt % 32 == 9 else (1 if nt % 32 == 25 else -1)),
                            L=L, G=G,
                            Nmod16=Nnat % 16,
                            patt5=patt5, patt6=patt6,
                            fwd=used6,                 # consulted forward valuations
                            suf=suf,
                        ))
            else:
                j += 1
    return events

def test4(events):
    print("=" * 70)
    print("TEST 4 — Chang burst-ending selection: local rule + 9/25 split")
    print("=" * 70)

    bad_resid = [e for e in events if e["Y"] == -1]
    print(f"  selected burst-ending events (n_t = 1 mod 8) : {len(events)}")
    print(f"  events with n_t mod 32 not in {{9,25}}        : {len(bad_resid)}  "
          f"(should be 0: n_t=1 mod 8 & burst-ends => n_t = 9 mod 16)")

    # local rule  Y<->G
    viol = [e for e in events if not ((e["Y"] == 0) == (e["G"] >= 2))]
    print(f"  Lemma 4.1 check  (Y=0 <=> G>=2, Y=1 <=> G=1) violations : {len(viol)}")
    if viol:
        print("    e.g.", [(e['nt'] % 32, e['G'], e['Y']) for e in viol[:8]])

    def split(subset, label):
        c = Counter(e["m32"] for e in subset)
        n9, n25 = c.get(9, 0), c.get(25, 0)
        tot = n9 + n25
        frac = (n25 / tot) if tot else float("nan")
        print(f"    {label:12s}  #events={tot:8d}   #9={n9:8d}   #25={n25:8d}   "
              f"P(25)={frac:.4f}   (#9-#25)={n9-n25}")

    print("  9 / 25 split:")
    split(events, "ALL")
    split([e for e in events if e["L"] == 1], "L = 1")
    split([e for e in events if e["L"] >= 2], "L >= 2")
    print()
    return len(bad_resid) == 0 and len(viol) == 0

# ==========================================================================
# TEST 5 — does the EOC coordinate simplify Y ?  (L >= 2 only)
# ==========================================================================

def cond_entropy(pairs):
    """pairs: iterable of (state, Y).  Returns (#states, N, H(Y|state), H(Y))."""
    by = defaultdict(Counter)
    tot = Counter()
    for s, y in pairs:
        by[s][y] += 1
        tot[y] += 1
    N = sum(tot.values())
    Hy = h_bern(tot[1] / N) if N else 0.0
    Hcond = 0.0
    for s, c in by.items():
        ns = c[0] + c[1]
        Hcond += (ns / N) * h_bern(c[1] / ns)
    return len(by), N, Hcond, Hy

def test5(events):
    print("=" * 70)
    print("TEST 5 — predictive power for Y from various state descriptions (L >= 2)")
    print("=" * 70)

    ev = [e for e in events if e["L"] >= 2 and e["Y"] in (0, 1)]
    print(f"  L>=2 selected events: {len(ev)}")
    if not ev:
        print("  (no L>=2 events)")
        return

    descs = {
        "A  m mod 64":                 lambda e: e["m64"],
        "B  N mod 16 alone":           lambda e: e["Nmod16"],
        "C  fwd prefix (sums<5)":      lambda e: e["patt5"],
        "C' fwd prefix (sums<6)":      lambda e: e["patt6"],
        "C\" fwd valuations tuple":    lambda e: e["fwd"],
        "D  (N%16, fwd prefix<5)":     lambda e: (e["Nmod16"], e["patt5"]),
        "E1 back suffix len1 (d_t)":   lambda e: e["suf"][:1],
        "E2 back suffix len2":         lambda e: e["suf"][:2],
        "E3 back suffix len3":         lambda e: e["suf"][:3],
        "E4 back suffix len4":         lambda e: e["suf"][:4],
        "-- m mod 32 (reference)":     lambda e: e["m32"],
    }
    print(f"  baseline H(Y) = {cond_entropy((0, e['Y']) for e in ev)[3]:.4f} bits\n")
    print(f"  {'description':28s} {'#states':>8s} {'#samples':>9s} "
          f"{'P(Y=1|state) range':>22s} {'H(Y|state)':>11s}")
    for name, f in descs.items():
        nst, N, Hc, Hy = cond_entropy((f(e), e["Y"]) for e in ev)
        by = defaultdict(Counter)
        for e in ev:
            by[f(e)][e["Y"]] += 1
        ps = sorted(c[1] / (c[0] + c[1]) for c in by.values())
        rng = f"[{ps[0]:.3f}, {ps[-1]:.3f}]"
        print(f"  {name:28s} {nst:8d} {N:9d} {rng:>22s} {Hc:11.4f}")
    print()

# ==========================================================================

def main():
    t1 = test1()
    t2 = test2()
    t3 = test3()
    print("collecting burst-ending events ...")
    events = collect_burst_ends(SMALL_SEEDS)
    t4 = test4(events)
    test5(events)

    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  TEST 1 mod-32 identity holds with 0 exceptions : {t1}")
    print(f"  TEST 2 C_N%64 = f(N%16, short prefix)          : {t2}")
    print(f"  TEST 3 Y deterministic from forward prefix     : {t3}")
    print(f"  TEST 4 Chang local rule Y<->G, 0 violations    : {t4}")

if __name__ == "__main__":
    main()
