"""Residue audit for the all-even ShapeTail schedule.  COMPUTATIONAL -- NOT PART OF THE PROOF.

The authoritative proof is EOC/ShapeUnconditional.lean (`shapeTail_allEven`); the Lean kernel re-checks
every finite fact it needs.  This script only guided the choice of schedule and threshold.

Schedule, for even j:
    sigma = floor(j log2 3)  (computed exactly as bitlen(3^j) - 1),
    T = floor(31 j / 100),  K = floor(j / 25),  N0 = 10,  rho_1 = 2^-e,  e = floor(j / 300).
Certificate (the `Arith j sigma e` predicate of the Lean file, denominators cleared):
    j * 3^(j/2) * 2^(sigma + e)  <=  2^(j/2) * 3^T * C(sigma - 1, j - 1)
Budget (hypothesis hK of ShapeCertificate.shapeTail_of_arith):
    K + T + sigma // 12  <=  j // 2
All comparisons are exact integer comparisons.  Standard library only; runs in ~10 s.

Usage:  python3 residues.py > residues.txt
"""
from math import comb

JMAX = 6000


def sigma(j):
    return (3 ** j).bit_length() - 1


def floor_log2_ratio(num, den):
    """floor(log2(num/den)) for positive integers."""
    m = num.bit_length() - den.bit_length()
    if m >= 0:
        return m - 1 if (den << m) > num else m
    return m - 1 if den > (num << -m) else m


def audit(j):
    s = sigma(j)
    T, K, e = 31 * j // 100, j // 25, j // 300
    lhs = j * 3 ** (j // 2) * 2 ** (s + e)
    rhs = 2 ** (j // 2) * 3 ** T * comb(s - 1, j - 1)
    budget = j // 2 - (K + T + s // 12)
    ok = lhs <= rhs and budget >= 0
    return ok, floor_log2_ratio(rhs, lhs), budget


def main():
    print("# r  | q0 | j0  | base j=300+r: bit margin, budget slack")
    print("# q0 = least q such that every j = 300q + r (j >= 2) up to", JMAX, "passes")
    results = {j: audit(j) for j in range(2, JMAX + 1, 2)}
    rows = []
    for r in range(0, 300, 2):
        js = [j for j in range(r, JMAX + 1, 300) if j >= 2]
        q0 = next(q for q in range(len(js) + 1)
                  if all(results[j][0] for j in js[q:])) + (1 if r == 0 else 0)
        _, bits, bud = results[300 + r]
        rows.append((r, q0, 300 * q0 + r, bits, bud))
        print(f"{r:4d} | {q0:2d} | {300 * q0 + r:4d} | {bits:4d} {bud:4d}")
    print("# worst base bit margin :", min(rows, key=lambda t: t[3]))
    print("# worst base budget     :", min(rows, key=lambda t: t[4]))
    print("# all even j in [300, %d] pass:" % JMAX,
          all(results[j][0] for j in range(300, JMAX + 1, 2)))
    fails = [j for j in range(2, 300, 2) if not results[j][0]]
    print("# even j < 300 failing:", len(fails), "largest:", max(fails))
    L, R = 2 * 3 ** 150 * 2 ** 477, 2 ** 150 * 3 ** 93 * comb(475, 300)
    print("# block step: exact margin", floor_log2_ratio(R, L), "bits; with C(475,300) >= 2^430:",
          floor_log2_ratio(2 ** 150 * 3 ** 93 * 2 ** 430, L), "bits")


if __name__ == "__main__":
    main()
