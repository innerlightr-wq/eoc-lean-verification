"""Rigorous Haar bound for the K-window mass from a fixed start state (PROVED MATH; exact rational arithmetic
for the matrix, floats only to print logarithms).

Model.  Window from state x0 at block r0: val(x0) = E*[prod_r s^{B_r} ; survive], the P* pair chain with
eligibility [d2 >= 2] (probability q) and B_r = eligible and dark at the own odd column z_r, row b_r = 2r+2.
Dark (d = 1/108, Lean predicate for low lambda) implies Tao-black at eta = 1/54, which holds iff the balanced-ternary
digits at positions b-3, b-2, b-1 of the phase residue vanish.  Filtration G_r = sigma(xi mod 3^{b_r - 2}, path so far).
  * the two digits b-2, b-1 are uniform on {-1,0,1}^2 given G_r (any unit multiplier), independent of the path;
  * X_r := [digit b_r - 3 of the row-r phase is 0] is G_r-measurable;
  * X_{r+1} is a function of xi mod 3^{b_r} with P(X_{r+1} = 1 | G_r, path) = 1/3.
Hence P(B_r | G_r, d1) <= X_r q/9, and the joint law of (B_r, X_{r+1}) is only constrained by these marginals.
LP bound (maximising s^B V(X') with V1 >= V0): from X = 1, put X' = 1 on all of B:
  row1 = [ (q/9) s + (1/3 - q/9),  2/3 ],  row0 = [ 1/3, 2/3 ]     (columns V1, V0)
so E_xi[val(x0)^beta] <= e^T M_beta^K 1 with s -> s^beta (beta >= 1, Jensen over the substochastic path weights).
Markov:  P_xi(val(x0) > 2^{K/5}) <= (e^T M_beta^K 1) / 2^{beta K/5}."""
from fractions import Fraction as F
import math

def matrix(q, sb):
    return [[q / 9 * sb + (F(1, 3) - q / 9), F(2, 3)], [F(1, 3), F(2, 3)]]

def rho(M):
    a, b = M[0]; c, d = M[1]
    tr = float(a + d); det = float(a * d - b * c)
    return (tr + math.sqrt(tr * tr - 4 * det)) / 2

def power_bound(M, K):
    v = [F(1), F(1)]
    for _ in range(K):
        v = [M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1]]
    return max(v)

q = F(37, 100)          # q <= 37/100 for j >= 300 (DangerousWindows.q_le); the bound is monotone in q
print("q =", q, " (eligibility probability upper bound)")
best = None
for beta_num in range(10, 31):
    beta = beta_num / 10
    M = matrix(q, F(3) ** beta if beta == int(beta) else F(3 ** beta))
    r = rho(M)
    ratio = r / 2 ** (beta / 5)
    c = -math.log(ratio, 3)
    if best is None or c > best[1]: best = (beta, c, r)
    if beta_num in (10, 12, 15, 20, 30):
        print(f"beta={beta:.1f}: rho={r:.6f}  rho/2^(beta/5)={ratio:.6f}  => delta_K <= C 3^(-{c:.4f} K)")
print(f"best beta={best[0]}: c = {best[1]:.4f}, rho = {best[2]:.6f}")
# explicit constant at beta = 1 with exact rational powers
M = matrix(q, F(3))
for K in (8, 16, 24, 26, 32):
    pb = power_bound(M, K)
    bound = float(pb) / 2 ** (K / 5)
    print(f"K={K}: E[val] <= {float(pb):.4f}, P(val > 2^(K/5)) <= {bound:.4e} = 3^-{-math.log(bound, 3):.2f}")
cst = max(float(power_bound(M, K)) / rho(M) ** K for K in range(1, 200))
print(f"constant: e^T M^K 1 <= {cst:.4f} * rho^K for K < 200 (rho = {rho(M):.6f})")
c1 = best[1] if best[0] == 1.0 else -math.log(rho(M) / 2 ** 0.2, 3)
print("\nunion bound over start states: P(window dangerous) <= #states * C * 3^(-cK)")
for c in (c1, best[1], 0.5):
    A = 1 / (c * math.log2(3))
    print(f"  c = {c:.4f}: K = A log2 j needs A > 1/(c log2 3) = {A:.2f}")
