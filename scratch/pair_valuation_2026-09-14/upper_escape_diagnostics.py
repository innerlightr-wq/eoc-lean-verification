"""Upper-wall escape diagnostics (Parts XIII-XIV). COMPUTATIONAL ONLY. Exact integer arithmetic:
  R_n > U        <=>  2^(S_n - U) > 3^n                       (integer U)
  exact identity R_n > U  <=>  2^U m_n prod(3 m_k) < mu prod(3 m_k + 1)     (Lean: R_gt_iff)
  descent time   sigma_U(mu) = min{n : 2^U m_n < mu}           (Lean: U_U <= sigma_U)
Horizon-limited; 'not reaching 1 within the horizon' is NOT interpreted as divergence.
"""
import random
from math import log2, exp

rng = random.Random(20260919)
ALPHA = log2(3)
HORIZON = 20000


def v2(n):
    return (n & -n).bit_length() - 1


def trajectory(mu, horizon=HORIZON):
    """orbit values m_0..m_n and digits until reaching 1 (plus 12 extra steps) or the horizon."""
    ms, ds = [mu], []
    m, extra = mu, None
    for _ in range(horizon):
        x = 3 * m + 1
        d = v2(x)
        m = x >> d
        ds.append(d)
        ms.append(m)
        if m == 1 and extra is None:
            extra = 12
        if extra is not None:
            extra -= 1
            if extra == 0:
                break
    return ms, ds


def analyse(mu, U, ms, ds):
    S = 0
    upper = sigma = h = None
    for n in range(1, len(ms)):
        S += ds[n - 1]
        if upper is None and S - U > 0 and (1 << (S - U)) > 3 ** n:
            upper = n
        if sigma is None and (1 << U) * ms[n] < mu:
            sigma = n
        if h is None and ms[n] == 1:
            h = n
        if upper is not None and sigma is not None and h is not None:
            break
    return upper, sigma, h


# ---- anchors
anchors = []
for bits in (8, 16, 32, 64, 128):
    for _ in range(600):
        mu = rng.getrandbits(bits) | 1 | (1 << (bits - 1))
        if mu % 3 == 0:
            mu += 2
        anchors.append(mu)
traj = {mu: trajectory(mu) for mu in anchors}
not_reached = sum(1 for mu in anchors if 1 not in traj[mu][0][1:] and traj[mu][0][-1] != 1)
print(f"anchors: {len(anchors)} (sizes 2^8..2^128); not reaching 1 within {HORIZON} steps: {not_reached}")

# ---- exact identity check R_n > U <=> 2^U m_n prod(3m_k) < mu prod(3m_k+1)   (sanity of R_gt_iff)
bad = checks = 0
for mu in anchors[:400]:
    ms, ds = traj[mu]
    for U in (0, 2, 5):
        S, P, Q = 0, 1, 1
        for n in range(1, min(len(ms), 200)):
            S += ds[n - 1]
            P *= 3 * ms[n - 1]
            Q *= 3 * ms[n - 1] + 1
            lhs = S - U > 0 and (1 << (S - U)) > 3 ** n
            rhs = (1 << U) * ms[n] * P < mu * Q
            checks += 1
            bad += lhs != rhs
print(f"[identity] R_n > U  <=>  2^U m_n prod(3m_k) < mu prod(3m_k+1): {checks - bad}/{checks}")

print("\n[XIII] first upper exit U_U vs 2^U-descent time sigma_U, hitting time h of 1")
for U in (0, 1, 2, 4, 8):
    rows = []
    viol = eq = 0
    for mu in anchors:
        ms, ds = traj[mu]
        up, sg, h = analyse(mu, U, ms, ds)
        rows.append((mu, up, sg, h))
        if up is not None and sg is not None:
            viol += up > sg
            eq += up == sg
    ups = [r[1] for r in rows if r[1] is not None]
    gaps = [r[2] - r[1] for r in rows if r[1] is not None and r[2] is not None]
    ratio = max(r[1] / log2(r[0]) for r in rows if r[1] is not None)
    after1 = sum(1 for r in rows if r[1] is not None and r[3] is not None and r[1] > r[3])
    print(f"   U={U}: exits {len(ups)}/{len(rows)}; U_U <= sigma_U violated: {viol}; equality "
          f"{eq}/{len(gaps)} ({100*eq/len(gaps):.1f}%); mean gap sigma-U_U {sum(gaps)/len(gaps):.2f}, "
          f"max gap {max(gaps)}; exits after hitting 1: {after1}; max U_U/log2(mu) = {ratio:.2f}")

print("\n[XIII-b] per-size-band statistics for U = 2 (matching ceiling U + L*alpha at the first exit)")
for bits in (8, 16, 32, 64, 128):
    sub = [mu for mu in anchors if mu.bit_length() == bits]
    Ls, mins, hs, Rmax, Rmin, ceil_ = [], [], [], [], [], []
    for mu in sub:
        ms, ds = traj[mu]
        up, sg, h = analyse(mu, 2, ms, ds)
        Ls.append(up)
        mins.append(log2(min(ms[: up + 1]) / mu))
        hs.append(h)
        S, rmx, rmn = 0, 0.0, 0.0
        for n in range(1, (h or len(ms) - 1) + 1):
            S += ds[n - 1]
            R = S - n * ALPHA
            rmx, rmn = max(rmx, R), min(rmn, R)
        Rmax.append(rmx)
        Rmin.append(rmn)
        ceil_.append(2 + up * ALPHA)
    k = len(sub)
    print(f"   {bits:3d}-bit: mean exit {sum(Ls)/k:5.1f} (max {max(Ls)}), mean log2(min m/mu) before exit "
          f"{sum(mins)/k:6.2f}, mean h {sum(hs)/k:6.1f}, mean max R {sum(Rmax)/k:6.1f}, mean min R "
          f"{sum(Rmin)/k:6.2f}, mean matching ceiling {sum(ceil_)/k:5.1f}")

print("\n[XIII-c] fixed corridor [-4, U] and log corridor (B=0.8, C=2, U): which wall is hit first")
for U in (1, 2, 4, 8):
    fixed = {"upper": 0, "lower": 0}
    logc = {"upper": 0, "lower": 0}
    for mu in anchors:
        ms, ds = traj[mu]
        S = 0
        done_f = done_l = False
        for n in range(1, len(ms)):
            S += ds[n - 1]
            R = S - n * ALPHA
            if not done_f and (R > U or R < -4):
                fixed["upper" if R > U else "lower"] += 1
                done_f = True
            if not done_l and (R > U or R < -0.8 * log2(n + 1) - 2):
                logc["upper" if R > U else "lower"] += 1
                done_l = True
            if done_f and done_l:
                break
    print(f"   U={U}: fixed [-4,U] first exit upper/lower = {fixed['upper']}/{fixed['lower']};  "
          f"log corridor upper/lower = {logc['upper']}/{logc['lower']}")

print("\n[XIV] predictors of the upper-exit time (U = 2), Spearman rank correlation with U_2")


def spearman(xs, ys):
    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(v):
            j = i
            while j + 1 < len(v) and v[order[j + 1]] == v[order[i]]:
                j += 1
            for k in range(i, j + 1):
                r[order[k]] = (i + j) / 2
            i = j + 1
        return r
    rx, ry = rank(xs), rank(ys)
    n = len(xs)
    mx, my = sum(rx) / n, sum(ry) / n
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    sxx = sum((a - mx) ** 2 for a in rx)
    syy = sum((b - my) ** 2 for b in ry)
    return sxy / (sxx * syy) ** 0.5


feat = {"log2 mu": [], "sigma_2 (2^2-descent time)": [], "index of first digit >= 3": [],
        "index of first digit >= 4": [], "sum of first 5 digits": [], "leading run of 1-digits": [],
        "headroom 2 - R_1": []}
ys = []
for mu in anchors:
    ms, ds = traj[mu]
    up, sg, h = analyse(mu, 2, ms, ds)
    ys.append(up)
    feat["log2 mu"].append(log2(mu))
    feat["sigma_2 (2^2-descent time)"].append(sg)
    feat["index of first digit >= 3"].append(next(i for i, d in enumerate(ds) if d >= 3))
    feat["index of first digit >= 4"].append(next(i for i, d in enumerate(ds) if d >= 4))
    feat["sum of first 5 digits"].append(sum(ds[:5]))
    run = 0
    while ds[run] == 1:
        run += 1
    feat["leading run of 1-digits"].append(run)
    feat["headroom 2 - R_1"].append(2 - (ds[0] - ALPHA))
for k, v in feat.items():
    print(f"   {k:30s}: {spearman(v, ys):+.3f}")
