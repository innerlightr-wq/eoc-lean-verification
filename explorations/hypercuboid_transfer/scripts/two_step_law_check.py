"""
Independent verification of the EXACT two-step (and k-step) cylinder-lift
digit law, derived by hand from EOC.TaoLike.Cylinder's `cylinder_restart`
mechanism (see ROUND1_REPORT.md Part VI for the full derivation).

Claim: for a seed m realizing a length-t prefix d, let z_k := orbit(m,t) +
2*3^t*k (the t-th iterate of the lift-k realizer, exact per
`cylinder_restart`). As k ranges uniformly (dyadically) over N, the pair
(d_t(k), d_{t+1}(k)) -- the next two valuation digits -- satisfies EXACTLY

    P(d_t = q, d_{t+1} = r) = 2^{-q} * 2^{-r}          (q, r >= 1)

i.e. the two steps are exactly independent under the cylinder-lift ensemble,
not merely marginally geometric.

Method A (below): exact frequency counting over k in [0, 2^K) for K large,
using Python's arbitrary-precision integers (no floating point) -- a direct
brute-force check.

Method B (below, separate function): a *structural* check that does not
rely on frequency counting at all -- it verifies the exact algebraic claim
used in the hand derivation, namely that conditioning on d_t=q reduces k to
an exact residue class k = kappa_q + 2^q * j, and that within this class,
3*w_j + 1 (w_j := T(z_k)) is an EXACT affine function A + B*j with v2(B)=1,
for a constant A that does not depend on q's *specific value* except
through which residue class of j is being read off -- i.e. it re-derives
the reduction algebraically, not by sampling.

Both methods must be run and must agree, per the round's independent-
verification requirement.
"""
import sys

def a_val(m):
    """a(m) = v2(3m+1)"""
    x = 3 * m + 1
    q = 0
    while x % 2 == 0:
        x //= 2
        q += 1
    return q

def T_val(m):
    x = 3 * m + 1
    while x % 2 == 0:
        x //= 2
    return x

def orbit_iter(m, t):
    for _ in range(t):
        m = T_val(m)
    return m

# ---------------------------------------------------------------------
# Method A: brute-force exact frequency counting over a large dyadic block
# ---------------------------------------------------------------------

def method_A(seed, t, K, qmax=6, rmax=6):
    """Exact integer frequency count of (d_t, d_{t+1}) over k in [0, 2^K)."""
    z0 = orbit_iter(seed, t)  # t-th iterate of the base realizer (k=0)
    counts = {}
    total = 0
    for k in range(2 ** K):
        z_k = z0 + 2 * (3 ** t) * k
        q = a_val(z_k)
        if q > qmax:
            continue  # tail digits: contributes negligibly, skip for table clarity
        w = T_val(z_k)
        r = a_val(w)
        if r > rmax:
            continue
        counts[(q, r)] = counts.get((q, r), 0) + 1
        total += 1
    return counts, total, 2 ** K

def report_method_A(seed, t, K, qmax=5, rmax=5):
    counts, counted, N = method_A(seed, t, K, qmax, rmax)
    print(f"--- Method A (brute force): seed={seed}, t={t}, K={K}, N=2^{K}={N} ---")
    print(f"{'q':>3}{'r':>3}{'exact count':>14}{'exact freq':>16}{'predicted 2^-(q+r)':>22}")
    max_err = 0.0
    for q in range(1, qmax + 1):
        for r in range(1, rmax + 1):
            c = counts.get((q, r), 0)
            freq = c / N
            pred = 2.0 ** (-(q + r))
            err = abs(freq - pred)
            max_err = max(max_err, err)
            print(f"{q:>3}{r:>3}{c:>14}{freq:>16.8f}{pred:>22.8f}")
    print(f"max |freq - 2^-(q+r)| over table = {max_err:.2e}  (should shrink as K grows)")
    return max_err

# ---------------------------------------------------------------------
# Method B: exact structural/algebraic verification (no sampling)
# ---------------------------------------------------------------------

def method_B(seed, t, q_test, num_j_check=2000):
    """
    Verify the EXACT algebraic reduction used in the hand derivation:
    conditioning on d_t = q_test restricts k to a single residue class
    mod 2^q_test; within that class (parametrized by j), 3*w_j+1 is an
    EXACT affine function of j with additive step having v2 = 1, for
    EVERY j tested (not sampled/approximate) -- confirming the mechanism
    that forces P(d_{t+1}=r | d_t=q) = 2^-r independent of q.
    """
    z0 = orbit_iter(seed, t)
    # find kappa_q: the unique residue mod 2^q_test with a_val(z0 + 2*3^t*k) = q_test
    mod = 2 ** q_test
    kappa = None
    for k0 in range(mod):
        z = z0 + 2 * (3 ** t) * k0
        if a_val(z) == q_test:
            kappa = k0
            break
    if kappa is None:
        return None, f"no residue class found for q={q_test} within modulus 2^{q_test}"

    # verify EVERY k in this residue class (up to num_j_check reps) gives d_t = q_test exactly
    # and extract 3*w_j+1 = A + B*j, checking B is the SAME constant every time (exact)
    step = 3 ** (t + 2) * 2  # predicted B = 2*3^{t+2}, from the hand derivation
    A_values = []
    ok = True
    for j in range(num_j_check):
        k = kappa + mod * j
        z_k = z0 + 2 * (3 ** t) * k
        q_actual = a_val(z_k)
        if q_actual != q_test:
            ok = False
            print(f"  FAIL: j={j} gives d_t={q_actual}, expected {q_test}")
            break
        w = T_val(z_k)
        val = 3 * w + 1
        A_values.append(val)

    if not ok:
        return False, "residue class did not uniformly give d_t = q_test"

    # check exact affine structure: val(j+1) - val(j) should be constant = step, for all j
    diffs = set(A_values[i+1] - A_values[i] for i in range(len(A_values) - 1))
    affine_ok = (len(diffs) == 1) and (next(iter(diffs)) == step)

    return affine_ok, {
        "kappa_q": kappa,
        "predicted_step_B": step,
        "observed_diffs": diffs,
        "num_j_checked": num_j_check,
    }

def report_method_B(seed, t, qmax=5):
    print(f"--- Method B (exact structural check): seed={seed}, t={t} ---")
    all_ok = True
    for q in range(1, qmax + 1):
        ok, info = method_B(seed, t, q, num_j_check=500)
        status = "OK" if ok else "FAIL"
        all_ok = all_ok and bool(ok)
        print(f"  q={q}: {status}  {info if not ok or isinstance(info, str) else {'kappa_q': info['kappa_q'], 'step_matches': True, 'checked': info['num_j_checked']}}")
    print(f"Method B overall: {'ALL EXACT, NO SAMPLING NEEDED' if all_ok else 'FAILED'}")
    return all_ok

if __name__ == "__main__":
    # Use seed 27 at a couple of depths, matching the project's own worked
    # example (README / checkpoint use seed 27's orbit for the one-step law).
    for seed, t in [(27, 0), (27, 5), (703, 3), (10087, 10)]:
        err = report_method_A(seed, t, K=16, qmax=4, rmax=4)
        ok = report_method_B(seed, t, qmax=4)
        print(f"=== seed={seed} t={t}: Method A max error={err:.2e}, Method B exact={ok} ===\n")
