"""pure-python statistics helpers (no numpy)."""
import math


def mean(v):
    return sum(v) / len(v) if v else 0.0


def var(v):
    if len(v) < 2:
        return 0.0
    mu = mean(v)
    return sum((x - mu) ** 2 for x in v) / len(v)


def sd(v):
    return math.sqrt(var(v))


def pearson(a, b):
    n = len(a)
    if n < 2:
        return 0.0
    ma, mb = mean(a), mean(b)
    sa = math.sqrt(sum((x - ma) ** 2 for x in a))
    sb = math.sqrt(sum((y - mb) ** 2 for y in b))
    if sa == 0 or sb == 0:
        return 0.0
    return sum((a[i] - ma) * (b[i] - mb) for i in range(n)) / (sa * sb)


def cramer_lambda(x, lo=1e-9, hi=2000.0, iters=300):
    """positive root of  (1/n) sum exp(lam * x_i) = 1 ; requires mean(x) < 0 and max(x) > 0."""
    if mean(x) >= 0 or max(x) <= 0:
        return None

    def g(lam):
        # stable: log-sum-exp
        M = max(lam * xi for xi in x)
        s = sum(math.exp(lam * xi - M) for xi in x)
        return M + math.log(s / len(x))
    if g(hi) < 0:
        return None
    a, b = lo, hi
    for _ in range(iters):
        mid = 0.5 * (a + b)
        if g(mid) < 0:
            a = mid
        else:
            b = mid
    return 0.5 * (a + b)


def solve(A, b):
    """Gaussian elimination with partial pivoting; A is n x n list of lists."""
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if abs(M[p][c]) < 1e-14:
            continue
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        for r in range(n):
            if r == c:
                continue
            f = M[r][c] / pv
            if f:
                for k in range(c, n + 1):
                    M[r][k] -= f * M[c][k]
    out = [0.0] * n
    for c in range(n):
        if abs(M[c][c]) > 1e-14:
            out[c] = M[c][n] / M[c][c]
    return out


def coboundary_fit(w, states):
    """fit  w_r = wbar + phi(states[r+1]) - phi(states[r]) + eps_r  by least squares.

    w has length n ; states has length n+1 (state at r = 0..n).
    returns (resid_sd, frac_var_explained, nstates, phi)
    """
    n = len(w)
    assert len(states) == n + 1
    lab = sorted(set(states))
    idx = {s: i for i, s in enumerate(lab)}
    K = len(lab)
    wbar = mean(w)
    y = [x - wbar for x in w]
    # normal equations  (A^T A) phi = A^T y  with A_r = e_{s_{r+1}} - e_{s_r}
    L = [[0.0] * K for _ in range(K)]
    rhs = [0.0] * K
    for r in range(n):
        i = idx[states[r]]
        j = idx[states[r + 1]]
        L[i][i] += 1.0
        L[j][j] += 1.0
        L[i][j] -= 1.0
        L[j][i] -= 1.0
        rhs[i] -= y[r]
        rhs[j] += y[r]
    # gauge: pin phi[0] = 0
    L[0] = [1.0 if k == 0 else 0.0 for k in range(K)]
    rhs[0] = 0.0
    phi = solve(L, rhs)
    res = [y[r] - (phi[idx[states[r + 1]]] - phi[idx[states[r]]]) for r in range(n)]
    v0 = var(w)
    vr = var(res)
    return sd(res), (1.0 - vr / v0 if v0 > 0 else 0.0), K, phi


def group_r2(vals, keys):
    """1 - E[Var(vals | key)] / Var(vals)  (exact conditional-variance decomposition)."""
    g = {}
    for v, k in zip(vals, keys):
        g.setdefault(k, []).append(v)
    n = len(vals)
    within = sum(len(v) * var(v) for v in g.values()) / n
    v0 = var(vals)
    return (1.0 - within / v0 if v0 > 0 else 0.0), len(g), math.sqrt(within)


def ols_r2(y, X):
    """multiple linear regression R^2 ; X is list of rows (no intercept column needed)."""
    n = len(y)
    p = len(X[0])
    Xa = [[1.0] + list(row) for row in X]
    k = p + 1
    A = [[sum(Xa[i][a] * Xa[i][b] for i in range(n)) for b in range(k)] for a in range(k)]
    bb = [sum(Xa[i][a] * y[i] for i in range(n)) for a in range(k)]
    c = solve(A, bb)
    res = [y[i] - sum(c[a] * Xa[i][a] for a in range(k)) for i in range(n)]
    v0 = var(y)
    return (1.0 - var(res) / v0 if v0 > 0 else 0.0), sd(res), c
