"""3-adic digit automata (pure Python, exact integer state labels).

Conventions.  A 3-adic integer x = sum d_n 3^n is read LOW digit first (n = 0, 1, 2, ...).
Every constraint is "the digits of M*x + c at positions n lie in allowed(n)", with M a positive
integer coprime to 3 and c a 3-adic integer with an eventually periodic digit sequence
(integers, -1/2 = ...111, 1/2 = ...1112).  Reading digit d_n of x, the constraint keeps a carry N:
    total = N + M*d_n + c_n,  output digit = total % 3,  N' = total // 3.
This is Algorithm A of Abram-Lagarias (arXiv:1308.3133, Thm 3.1) with an additive constant and
position-dependent allowed sets; several constraints run in parallel (label product, Algorithm B).

Right-resolving: the next state is a function of (state, digit).  Hausdorff dimension of the
path-set fractal = log_3 of the spectral radius of the essential part (AL13 Prop 2.2)."""
import math
from fractions import Fraction


def cdigits_const(c, n):
    """n-th 3-adic digit of an integer or a rational with denominator coprime to 3."""
    c = Fraction(c)
    # c = a/b, b coprime to 3: digit n of c is digit n of (a * b^{-1} mod 3^{n+1})
    mod = 3 ** (n + 1)
    v = (c.numerator * pow(c.denominator, -1, mod)) % mod
    return v // 3 ** n


class Constraint:
    def __init__(self, M, allowed, c=0, period=None):
        """allowed: function n -> set of allowed output digits (or None = all)."""
        assert M % 3 != 0
        self.M, self.allowed, self.c = M, allowed, Fraction(c)
        # digits of c are eventually periodic; cache lazily
        self._cd = {}

    def cdig(self, n):
        if n not in self._cd:
            self._cd[n] = cdigits_const(self.c, n)
        return self._cd[n]


def build_stationary(Ms, x_digits=(0, 1), out_digits=(0, 1), c=0):
    """Stationary automaton for {x : digits of x in x_digits, digits of M_i x + c in out_digits}.
    c must be an integer >= 0 or -1/2 (all-ones digits) for stationarity.  Returns (states, edges)
    with edges[s] = list of (digit, t).  State = tuple of carries."""
    cd = None
    if c == Fraction(-1, 2):
        cd = 1
    elif c == 0:
        cd = 0
    else:
        raise ValueError("stationary builder supports c in {0, -1/2}")
    start = tuple(0 for _ in Ms)
    states = {start: 0}
    order = [start]
    edges = {}
    i = 0
    while i < len(order):
        s = order[i]; i += 1
        out = []
        for d in x_digits:
            nxt = []
            ok = True
            for N, M in zip(s, Ms):
                tot = N + M * d + cd
                if tot % 3 not in out_digits:
                    ok = False; break
                nxt.append(tot // 3)
            if ok:
                t = tuple(nxt)
                if t not in states:
                    states[t] = len(order); order.append(t)
                out.append((d, t))
        edges[s] = out
    return order, edges


def sccs(order, edges):
    """Tarjan (iterative).  Returns list of SCCs (lists of states)."""
    index = {}; low = {}; onstack = set(); stack = []; res = []; counter = [0]
    for root in order:
        if root in index:
            continue
        work = [(root, iter(edges[root]))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stack.append(root); onstack.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for _, w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); onstack.add(w)
                    work.append((w, iter(edges[w])))
                    advanced = True
                    break
                elif w in onstack:
                    low[v] = min(low[v], index[w])
            if not advanced:
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop(); onstack.discard(w); comp.append(w)
                        if w == v:
                            break
                    res.append(comp)
    return res


def spectral_radius(order, edges, iters=4000, tol=1e-13):
    """Max over SCCs of the Perron root, by power iteration on (A + I) restricted to the SCC."""
    best = 0.0
    for comp in sccs(order, edges):
        cs = set(comp)
        sub = {v: [w for _, w in edges[v] if w in cs] for v in comp}
        if all(len(sub[v]) == 0 for v in comp):
            continue  # trivial SCC without self-loop
        if len(comp) == 1 and not sub[comp[0]]:
            continue
        x = {v: 1.0 for v in comp}
        lam = 0.0
        for k in range(iters):
            y = {v: x[v] + sum(x[w] for w in sub[v]) for v in comp}
            m = max(y.values())
            y = {v: y[v] / m for v in comp}
            if k > 50 and abs(m - lam) < tol:
                lam = m; x = y; break
            lam = m; x = y
        best = max(best, lam - 1.0)
    return best


def dim_C(Ms):
    """dim_H C(1, M_1, ..., M_n) (AL13 Theorem 1.6): x in Sigma, M_i x in Sigma."""
    Ms = [M for M in Ms if M != 1]
    while any(M % 3 == 0 for M in Ms):
        Ms = [M // 3 if M % 3 == 0 else M for M in Ms]
    if any(M % 3 == 2 for M in Ms):
        return 0.0, 1, 1.0
    order, edges = build_stationary(Ms)
    beta = spectral_radius(order, edges)
    return (math.log(beta, 3) if beta > 1 + 1e-12 else 0.0), len(order), beta


def count_words(order, edges, D):
    """Number of admissible length-D digit words from the start state (exact integers)."""
    cnt = {order[0]: 1}
    for _ in range(D):
        nxt = {}
        for s, k in cnt.items():
            for _, t in edges[s]:
                nxt[t] = nxt.get(t, 0) + k
        cnt = nxt
    return sum(cnt.values())
