"""EXACT quadratic-irrational barriers.

beta is stored as the triple (P, Q, S, D) meaning  beta = (P + Q*sqrt(D)) / S
with integers P, Q, S, D,  S > 0,  D > 1 squarefree-ish (only needs: D not a perfect square).

floor(j*beta) is computed with INTEGER arithmetic only (math.isqrt + exact integer
comparisons); no float, no Decimal is involved in the barrier itself.  qverify() checks
the routine against 120-digit Decimal for j up to 10**5.

Construction: beta = [a_0; a_1, ..., a_{m-1}, PERIODIC(c_1..c_p)] -- the first m partial
quotients of alpha = log2 3 followed by a purely periodic tail.  The tail value y is the
positive root of  C y^2 + (E-A) y - B = 0  where [[A,B],[C,E]] = prod_i [[c_i,1],[1,0]];
then beta = (p_{m-1} y + p_{m-2}) / (q_{m-1} y + q_{m-2}) with p_i/q_i the prefix
convergents.  All of that is done in Q(sqrt(D)) with Fractions, hence exact.
"""
import math
from fractions import Fraction as F
from decimal import Decimal, getcontext

getcontext().prec = 140

# ---------------------------------------------------------------- alpha = log2 3 ----
_ALD = Decimal(3).ln() / Decimal(2).ln()
_ALF = F(int(_ALD * 10 ** 80), 10 ** 80)          # exact rational, < alpha
_ALF_HI = _ALF + F(1, 10 ** 80)
AL_FLOAT = math.log2(3)


def floor_alpha(j: int) -> int:
    """EXACT floor(j*log2 3) via a rational bracket that is asserted to determine it."""
    lo = (_ALF * j).__floor__()
    hi = (_ALF_HI * j).__floor__()
    assert lo == hi, "alpha bracket too coarse at j=%d" % j
    return lo


def alpha_cf(n=40):
    x = _ALD
    out = []
    for _ in range(n):
        i = int(x)
        out.append(i)
        x = x - i
        if x == 0:
            break
        x = 1 / x
    return out


ALPHA_CF = alpha_cf(40)

# ------------------------------------------------- arithmetic in Q(sqrt(D)) ---------
class QS:
    """a + b*sqrt(D) with a,b Fractions."""
    __slots__ = ("a", "b", "D")

    def __init__(self, a, b, D):
        self.a = F(a); self.b = F(b); self.D = D

    def __add__(self, o):
        if isinstance(o, QS):
            return QS(self.a + o.a, self.b + o.b, self.D)
        return QS(self.a + F(o), self.b, self.D)

    __radd__ = __add__

    def __mul__(self, o):
        if isinstance(o, QS):
            return QS(self.a * o.a + self.b * o.b * self.D,
                      self.a * o.b + self.b * o.a, self.D)
        return QS(self.a * F(o), self.b * F(o), self.D)

    __rmul__ = __mul__

    def __truediv__(self, o):
        if not isinstance(o, QS):
            return QS(self.a / F(o), self.b / F(o), self.D)
        den = o.a * o.a - o.b * o.b * self.D
        assert den != 0
        conj = QS(o.a, -o.b, self.D)
        num = self * conj
        return QS(num.a / den, num.b / den, self.D)

    def triple(self):
        """(P, Q, S, D) with integers, S > 0, representing (P + Q sqrt D)/S."""
        S = self.a.denominator * self.b.denominator // math.gcd(
            self.a.denominator, self.b.denominator)
        P = self.a.numerator * (S // self.a.denominator)
        Q = self.b.numerator * (S // self.b.denominator)
        g = math.gcd(math.gcd(abs(P), abs(Q)), S)
        if g:
            P //= g; Q //= g; S //= g
        if S < 0:
            P, Q, S = -P, -Q, -S
        return (P, Q, S, self.D)


def _mat_period(cs):
    """prod_i [[c_i,1],[1,0]] = [[A,B],[C,E]]"""
    A, B, C, E = 1, 0, 0, 1
    for c in cs:
        A, B, C, E = A * c + B, A, C * c + E, C
    return A, B, C, E


def _squarefree_part(n):
    """write n = f^2 * d ; return (f, d)."""
    f = 1
    d = n
    p = 2
    while p * p <= d:
        while d % (p * p) == 0:
            d //= p * p
            f *= p
        p += 1 if p == 2 else 2
    return f, d


def beta_from_cf(prefix, period):
    """beta = [prefix ; PERIODIC(period)] as an exact (P,Q,S,D) triple."""
    A, B, C, E = _mat_period(period)
    # C y^2 + (E-A) y - B = 0, positive root
    disc = (A - E) ** 2 + 4 * B * C
    f, D = _squarefree_part(disc)
    assert math.isqrt(D) ** 2 != D, "period gives a rational tail"
    y = QS(F(A - E, 2 * C), F(f, 2 * C), D)
    # prefix convergents
    p0, q0, p1, q1 = 1, 0, prefix[0], 1
    for ai in prefix[1:]:
        p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
    num = y * p1 + QS(p0, 0, D)
    den = y * q1 + QS(q0, 0, D)
    return (num / den).triple()


def minpoly(P, Q, S, D):
    """integer minimal polynomial (A, B, C) of beta=(P+Q sqrt D)/S : A x^2 + B x + C = 0,
    A > 0, gcd = 1."""
    # x = (P + Q rD)/S  ->  (S x - P)^2 = Q^2 D  ->  S^2 x^2 - 2 P S x + P^2 - Q^2 D = 0
    A = S * S
    B = -2 * P * S
    Cc = P * P - Q * Q * D
    g = math.gcd(math.gcd(abs(A), abs(B)), abs(Cc))
    if g:
        A //= g; B //= g; Cc //= g
    if A < 0:
        A, B, Cc = -A, -B, -Cc
    return (A, B, Cc)


def disc_of(A, B, C):
    return B * B - 4 * A * C


# ------------------------------------------------------- the exact floor routine ----
def make_floor(trip):
    """returns f(j) = floor(j*beta), EXACT integer arithmetic."""
    P, Q, S, D = trip
    QQD = Q * Q * D
    sgn = 1 if Q > 0 else -1

    def le_sqrt(t, M):
        """t <= sgn*sqrt(M)  (M = j^2 Q^2 D, never a perfect square for j>0)"""
        if sgn > 0:
            if t <= 0:
                return True
            return t * t <= M
        else:
            if t > 0:
                return False
            return t * t >= M

    def f(j):
        if j == 0:
            return 0
        M = j * j * QQD
        s = math.isqrt(M)
        k = (j * P + sgn * s) // S
        # k is floor(...) up to +-1 ; fix exactly.  predicate: k*S - j*P <= sgn*sqrt(M)
        while le_sqrt((k + 1) * S - j * P, M):
            k += 1
        while not le_sqrt(k * S - j * P, M):
            k -= 1
        return k

    return f


def to_decimal(trip):
    P, Q, S, D = trip
    return (Decimal(P) + Decimal(Q) * Decimal(D).sqrt()) / Decimal(S)


def qverify(trip, N=100000):
    """check make_floor against 140-digit Decimal for j=0..N. returns #mismatches."""
    f = make_floor(trip)
    bd = to_decimal(trip)
    bad = 0
    for j in range(0, N + 1):
        if f(j) != int((bd * j).to_integral_value(rounding="ROUND_FLOOR")):
            bad += 1
    return bad


# ------------------------------------------------------------------ the families ----
def families():
    """list of dicts describing every beta used in this round."""
    out = []
    for m in (4, 6, 8, 10):
        pre = ALPHA_CF[:m]
        out.append(dict(name=f"golden_m{m}", m=m, prefix=pre, period=[1], fam="golden"))
        out.append(dict(name=f"silver_m{m}", m=m, prefix=pre, period=[2], fam="silver"))
        for L in (2, 3):
            out.append(dict(name=f"match{L}_m{m}", m=m, prefix=pre,
                            period=ALPHA_CF[m:m + L], fam=f"match{L}"))
    for d in out:
        d["trip"] = beta_from_cf(d["prefix"], d["period"])
    return out


if __name__ == "__main__":
    import json, os, sys
    DIR = os.path.dirname(os.path.abspath(__file__))
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    fams = families()
    lines = []
    lines.append("EXACTNESS VERIFICATION of floor(j*beta), integer-only routine vs 140-digit Decimal")
    lines.append(f"  j = 0 .. {N}")
    ok_all = True
    for d in fams:
        bad = qverify(d["trip"], N)
        ok_all &= (bad == 0)
        lines.append(f"  {d['name']:14s} trip={d['trip']}  mismatches={bad}")
    # also verify floor_alpha against Decimal
    bad = 0
    for j in range(0, N + 1):
        if floor_alpha(j) != int((_ALD * j).to_integral_value(rounding="ROUND_FLOOR")):
            bad += 1
    lines.append(f"  {'alpha':14s} (rational bracket)                 mismatches={bad}")
    ok_all &= (bad == 0)
    lines.append(f"ALL EXACT: {ok_all}")
    txt = "\n".join(lines)
    print(txt)
    open(os.path.join(DIR, "T0_EXACT.txt"), "w").write(txt + "\n")
