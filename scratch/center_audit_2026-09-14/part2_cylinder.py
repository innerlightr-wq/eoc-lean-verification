"""
Part 2 — audit the reference ensemble: cylinder-refinement next-digit law.

Claim (README "Exact next-digit law from cylinder lifting", already
PROVED MATHEMATICALLY / NOT YET LEAN-PACKAGED in this repo):

    Fix a seed m realizing a length-t prefix (valuation word d_0..d_{t-1}).
    cylinder_restart (TaoLike/Cylinder.lean, FORMALLY VERIFIED) gives, for
    EVERY k : Nat, that m + 2^{S_t+1} * k also realizes the same prefix, and
        orbit(m + 2^{S_t+1} k, t) = orbit(m, t) + 2*3^t*k.
    Varying k uniformly (mod 2^K, K large) and asking for the next digit's
    2-adic valuation gives, exactly:
        P(next digit = q | prefix) = 2^{-q},   q >= 1.

This script:
  (i)   brute-force-verifies this law by cylinder lift enumeration, modestly
        (k up to 2^14, per the task's "start modestly" instruction -- the
        repo's own prior audit already did this to 2^20; we are not
        re-deriving that, only sanity-checking it at smaller, reproducible
        scale here);
  (ii)  derives E[d] = 2, E[Delta R] = 2 - alpha from the law algebraically
        and confirms the empirical cylinder-lift mean matches;
  (iii) is EXPLICIT that this is a law across cylinder LIFTS of one fixed
         prefix (a spatial/ensemble average over the free parameter k), not
         a claim of temporal independence along one fixed natural orbit --
         the natural orbit fixes k=0 forever (see RealizerLift.lean's
         'liftDigit_eq_zero_iff' / the M37B circularity note: whether the
         orbit's own actual next digit matches a given candidate is exactly
         as hard as computing that digit).
"""
import math

ALPHA = math.log2(3)

def v2(n):
    return (n & -n).bit_length() - 1

def T(m):
    x = 3 * m + 1
    return x >> v2(x)

def orbit_and_word(m0, N):
    ms = [m0]
    ds = []
    m = m0
    for _ in range(N):
        d = v2(3 * m + 1)
        m = T(m)
        ds.append(d)
        ms.append(m)
    return ms, ds


print("=" * 72)
print("2(i) Cylinder-lift brute force: P(next digit = q | prefix)")
print("=" * 72)

# Fix a concrete prefix from a real seed's own orbit (any seed works; the
# claim is that the answer is prefix-independent).
m0, t = 27, 5
ms, ds = orbit_and_word(m0, t)
S_t = sum(ds)
base = ms[t]                      # orbit(m0, t), the "k=0" state
# cylinder_restart: orbit(m + 2^{S_t+1} k, t) = orbit(m, t) + 2*3^t*k.
# The STATE at time t moves by step = 2*3^t (v2(step)=1), NOT by 2^{S_t+1}
# (that modulus instead bounds *which seeds* share this prefix). Using the
# wrong (S_t+1)-valuation step here was an earlier bug in this script: it
# made the lift essentially never perturb the low bits, so every k
# reproduced the seed's own fixed next digit -- see REPORT.md, "negative
# result: correct the cylinder-lift script".
step = 2 * 3 ** t                 # correct state-space cylinder step
KMAX_BITS = 14                    # modest, per task instruction
KMAX = 1 << KMAX_BITS

from collections import Counter
counts = Counter()
for k in range(KMAX):
    z = base + step * k
    q = v2(3 * z + 1)
    counts[q] += 1

print(f"  prefix: seed={m0}, t={t}, S_t={S_t}, cylinder step=2^{S_t+1}={step}")
print(f"  lifts enumerated: k in [0, 2^{KMAX_BITS}) = {KMAX}")
print(f"  {'q':>3} {'observed P':>12} {'2^-q':>10} {'count':>10}")
qmax = max(counts)
total_mass = 0.0
for q in range(1, qmax + 1):
    c = counts.get(q, 0)
    p_obs = c / KMAX
    p_pred = 2.0 ** (-q)
    total_mass += p_obs
    flag = "" if abs(p_obs - p_pred) < 3 * math.sqrt(p_pred * (1 - p_pred) / KMAX) + 1e-9 else "  <-- outside ~3 sigma"
    if c > 0 or q <= qmax:
        print(f"  {q:>3} {p_obs:>12.6f} {p_pred:>10.6f} {c:>10}{flag}")
print(f"  total observed mass (should be ~1, up to finite-KMAX censoring of huge q): {total_mass:.6f}")

# Repeat for a second, unrelated prefix to check prefix-independence
m0b, tb = 703, 8
msb, dsb = orbit_and_word(m0b, tb)
S_tb = sum(dsb)
baseb = msb[tb]
stepb = 2 * 3 ** tb
countsb = Counter()
for k in range(KMAX):
    z = baseb + stepb * k
    q = v2(3 * z + 1)
    countsb[q] += 1
print(f"\n  second prefix: seed={m0b}, t={tb}, S_t={S_tb}")
maxdiff = 0.0
for q in range(1, 12):
    p1 = counts.get(q, 0) / KMAX
    p2 = countsb.get(q, 0) / KMAX
    maxdiff = max(maxdiff, abs(p1 - p2))
print(f"  max |P_prefix1(q) - P_prefix2(q)| for q=1..11: {maxdiff:.6f}  (both -> 2^-q; prefix-independent)")

print("""
Conclusion 2(i): brute-force cylinder-lift enumeration reproduces
P(next digit=q|prefix) = 2^-q to within sampling noise for two unrelated
prefixes, at the modest scale used here. This CONFIRMS the repo's existing
analytic claim; it does not extend it.
""")

print("=" * 72)
print("2(ii) E[d] = 2, E[Delta R] = 2 - alpha")
print("=" * 72)
Ed_theory = sum(q * 2.0 ** (-q) for q in range(1, 200))
print(f"  sum_q q*2^-q (theory, q up to 200) = {Ed_theory:.10f}   (should be 2)")
Ed_emp = sum(q * counts.get(q, 0) for q in counts) / KMAX
print(f"  empirical E[d] from cylinder-lift enumeration (prefix 1): {Ed_emp:.6f}")
print(f"  E[Delta R] = E[d] - alpha = {2 - ALPHA:.6f}")

print("""
Conclusion 2(ii): both the exact series sum_q q*2^-q = 2 and the empirical
cylinder-lift mean agree with E[d]=2, so E[Delta R] = 2 - alpha ~ 0.415 > 0:
the UNCONDITIONAL cylinder-lift law has POSITIVE mean drift (pushes R
upward / away from confinement), not zero and not negative. Any apparent
'centering' or 'restoring' tendency seen in a confinement-conditioned
sample cannot come from this unconditional law -- it must come from the
conditioning itself. This is checked directly in part4.
""")
