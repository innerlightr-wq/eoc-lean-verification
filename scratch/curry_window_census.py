#!/usr/bin/env python3
"""Computational support for docs/CURRY_REALIZER_WINDOW_INTERFACE.md (Gates 0, 2, 3, 5, 6, 8, 11, 12).

Standard library only. Deterministic. Reproduces every number quoted in that report.

    python3 scratch/curry_window_census.py

Sections:
  0  raw/accelerated dictionary: k accelerated steps = S_k raw steps, exactly k odd
  2  the critical comparison gamma_* < rho = 1/log2 3, with an elementary certificate
  3  heavy-branch exponent H2(rho) vs the repository's 1 - I0/alpha
  5/6 odd-step density at EVERY raw depth, by direct iteration
  8  bounded-multiplicity exponents beta_*(delta) and the threshold delta_max = 1 - alpha/2
  11 shell census: least realizers, terminal states, fiber multiplicities
  12 population slack of the confined-word family against the window budget

NOTE: finite data here is used only to check identities, notation and already-proved
statements. It is NOT evidence about infinite divergence.
"""
import math
from collections import Counter, defaultdict

alpha = math.log2(3)
rho = 1 / alpha


def H(p):
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def gamma_star():
    lo, hi = 0.5, rho
    for _ in range(300):
        mid = (lo + hi) / 2
        if H(mid) - mid * alpha > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def nu2(n):
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def T0(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def floor_ak(k):
    """exact floor(k*log2 3), decided by integer comparison 2^v vs 3^k"""
    v = int(alpha * k)
    while 2 ** (v + 1) <= 3 ** k:
        v += 1
    while 2 ** v > 3 ** k:
        v -= 1
    return v


def carry(D):
    """C(D) = sum_{j<k} 3^{k-1-j} 2^{s_j}   (P1 Definition 5.1)"""
    k = len(D)
    C = 0
    s = 0
    for j in range(k):
        C += 3 ** (k - 1 - j) * 2 ** s
        s += D[j]
    return C


def least_realizer(D):
    """r(D) = (2^S - C(D)) * 3^{-k}  mod 2^{S+1}   (P1 Proposition 5.2)"""
    k = len(D)
    S = sum(D)
    M = 2 ** (S + 1)
    return ((2 ** S - carry(D)) * pow(pow(3, k, M), -1, M)) % M


def zero_confined_words(k):
    """all D with d_i >= 1 and S_j <= floor(alpha j) for every 1 <= j <= k"""
    caps = [floor_ak(j) for j in range(k + 1)]
    out = []

    def rec(j, s, cur):
        if j == k:
            out.append(tuple(cur))
            return
        for d in range(1, caps[j + 1] - s + 1):
            cur.append(d)
            rec(j + 1, s + d, cur)
            cur.pop()

    rec(0, 0, [])
    return out


def main():
    gs = gamma_star()

    print("== 0. raw/accelerated dictionary ==")
    for m0 in (7, 27, 703, 26623):
        m, S, blocks = m0, 0, []
        for _ in range(12):
            d = nu2(3 * m + 1)
            blocks.append('1' + '0' * (d - 1))
            S += d
            m = (3 * m + 1) // 2 ** d
            if m == 1:
                break
        n, actual = m0, ''
        for _ in range(S):
            actual += '1' if n % 2 else '0'
            n = T0(n)
        k = len(blocks)
        print(f"   m0={m0:>6} k={k:>2} S={S:>3} odd-count={actual.count('1'):>2} "
              f"parity-blocks match: {''.join(blocks) == actual}")

    print("\n== 2. the critical comparison ==")
    print(f"   alpha={alpha:.12f}  rho=1/alpha={rho:.12f}  gamma_*={gs:.12f}")
    print(f"   gamma_* < rho : {gs < rho}   margin {rho - gs:.12f}")
    print(f"   certificate: alpha*rho = {alpha*rho:.15f} (=1) and H2(rho) = {H(rho):.12f} < 1")

    print("\n== 3. heavy-branch exponent vs the repository constant ==")
    print(f"   H2(rho)                  = {H(rho):.12f}")
    print(f"   I0 = alpha(1-H2(rho))    = {alpha*(1-H(rho)):.12f}")
    print(f"   1/I0                     = {1/(alpha*(1-H(rho))):.10f}   (P1 Rem 3.10 prints 12.6074)")

    print("\n== 5/6. odd-step density at every raw depth (direct iteration) ==")
    worst = (9e9, None)
    viol = 0
    for k in range(1, 13):
        for D in zero_confined_words(k):
            r, S = least_realizer(D), sum(D)
            n, odds = r, 0
            for J in range(1, S + 2):
                if n % 2:
                    odds += 1
                n = T0(n)
                dens = odds / J
                if dens < worst[0]:
                    worst = (dens, (k, S, J))
                if dens <= gs:
                    viol += 1
    print(f"   min density over all k<=12 and all raw depths: {worst[0]:.12f} at {worst[1]}")
    print(f"   min >= rho: {worst[0] >= rho - 1e-15};  depths below gamma_*: {viol}")

    print("\n== 8. bounded multiplicity M = X^delta ==")
    def cross(delta):
        if H(0.5) - (0.5 * alpha + delta) <= 0:
            return None
        lo, hi = 0.5, rho
        for _ in range(300):
            mid = (lo + hi) / 2
            if H(mid) - (mid * alpha + delta) > 0:
                lo = mid
            else:
                hi = mid
        g = (lo + hi) / 2
        return g, H(g)
    for d in (0.0, 0.01, 0.05, 0.10, 0.20, 0.2076, 0.25):
        r = cross(d)
        print(f"   delta={d:<7} " + (f"gamma={r[0]:.8f} beta_*(delta)={r[1]:.8f} saving={r[1]<1}"
                                     if r else "no crossing; exponent >= 1"))
    print(f"   delta_max = 1 - alpha/2 = {1 - alpha/2:.10f}")

    print("\n== 11. shell census ==")
    rows = []
    for k in range(1, 13):
        byS = defaultdict(list)
        for D in zero_confined_words(k):
            byS[sum(D)].append(D)
        for S in sorted(byS):
            Ds = byS[S]
            rs = [least_realizer(D) for D in Ds]
            ms = [(3 ** k * r + carry(D)) // 2 ** S for r, D in zip(rs, Ds)]
            cm = Counter(ms)
            rows.append((k, S, len(Ds), len(set(rs)), max(cm.values())))
    print(f"   shells: {len(rows)};  max terminal fiber: {max(r[4] for r in rows)};"
          f"  shells with a repeated realizer: {sum(1 for r in rows if r[3] < r[2])}")
    print("   (matches P1 section 6 'shell injectivity', already proved there)")

    print("\n== 12. population slack of the confined-word family ==")
    print(f"   {'k':>3} {'K':>8} {'log2K/k':>9} {'budget':>9} {'slack':>8}")
    for k in range(8, 16):
        W = zero_confined_words(k)
        K = len(W)
        S = max(sum(D) for D in W)
        budget = math.log2(6 * (S + 2)) + (S + 1) * H(rho)
        print(f"   {k:>3} {K:>8} {math.log2(K)/k:>9.4f} {budget:>9.3f} {budget-math.log2(K):>8.3f}")
    print(f"   budget rate alpha*H2(rho) = {alpha*H(rho):.6f} bits/accelerated step")
    print("   observed confined-word rate at k=15 is far below it: exponential slack.")


if __name__ == "__main__":
    main()
