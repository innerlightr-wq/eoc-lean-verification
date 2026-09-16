# Tilted partition function for good pair blocks: shape-only large deviations (round of 2026-09-16, part 2)

Nothing committed or pushed.  Working tree: `main` @ `317c765` + uncommitted white-count round + this directory
(`shape_ld.py`, `check_bound.py`, `CHECK_BOUND.txt`, this file).  No Lean changes this round.

**Stop condition 1 fired: the shape-only exponential lower tail is PROVED (MATH)**, with an explicit rate, and the
finite-J bound is checked against the exact DP.  A by-product is a probabilistic reduction (PROVED MATH):
`CriticalWhiteCount` (λ = 1) ⇐ shape large deviations (proved) + an upper large deviation for the number of black
odd path cells (single-cell statistic, OPEN).  Per the stop rule the operator numerics for the true environment,
the fixed-K automaton computations, η optimisation and Lean work were not started.

## 1. Setting, partition function, Chernoff (PROVED MATH)
J = 2R, sg = ⌊Jα⌋, top[i] = min(⌊iα⌋, sg).  C_J = compositions d₁…d_J ≥ 1 with S_J = sg and S_i ≤ top[i]; the
confined law is uniform on C_J (= P* conditioned on {confined, S_J = sg}, since P*(w) = p^J q^{sg−J}, p = 1/α).
In class form (gb_dp): state S_{2r}, transition S → S′ with multiplicity |B_r(S,S′)| = min(S′−1, top[2r+1]) − S
(number of internal choices), good flag g_r(S,S′).  Then
  Z_J(t) = Σ_{w∈C_J} t^{G(w)} = 1ᵀ T_{R−1}(t)⋯T_0(t) e_0,  T_r(t)(S,S′) = |B_r(S,S′)| t^{g_r(S,S′)},
  Z_J(1) = |C_J|,  E_conf[t^G] = Z_J(t)/Z_J(1),
  P_conf(G ≤ gR) ≤ t^{−gR} Z_J(t)/Z_J(1)  (0 < t ≤ 1),  so Z_J(t)/Z_J(1) ≤ Cρ^J gives rate −log₂ρ − (g/2)log₂(1/t) per step.
Bridge form: with backward counts B_r(S) (confined continuations), P_r(S→S′) = |B_r(S,S′)|B_{r+1}(S′)/B_r(S) is an
exact (time-inhomogeneous) Markov bridge, and E_conf[t^G] = E_bridge[Π_r t^{g_r(S_r,S_{r+1})}] (discrete Feynman–Kac).

## 2. The shape-only theorem
Shape-good block (gb_dp `shape` control): 2 ≤ |B_r| ≤ N₀.  Let u_r = d_{2r+1} + d_{2r+2},
G′ = #{r : 3 ≤ u_r ≤ N₀+1} (uncapped), K = #{i ≤ J : S_i = top[i]} (barrier contacts),
p_g(N₀) = P*(3 ≤ u ≤ N₀+1) = Σ_{u=3}^{N₀+1}(u−1)p²q^{u−2}: **0.29383 (N₀ = 2), 0.53655 (N₀ = 4)** — exactly the DP
shape-only means 0.2940R, 0.5366R.
* (L1) Cycle lemma: |C_J| ≥ binom(sg−1, J−1)/J.  Rotate a composition to start after the maximiser of
  S_i − i·sg/J; the rotation has S′_i ≤ i·sg/J ≤ iα, hence S′_i ≤ top[i]; each confined word has ≤ J preimages.
  (Checked: log₂ bound is 1.4 bits below the exact |C_J| at J = 200…1200.)
* (L2) Generating function: Σ over all compositions with J = 2R parts of t^{G′}x^{S_J} = F_t(x)^R,
  F_t(x) = x²/(1−x)² − (1−t)Σ_{u=3}^{N₀+1}(u−1)x^u.  Hence #{w ∈ Comp(sg,J) : G′ ≤ n} ≤ t^{−n}x^{−sg}F_t(x)^R.
* (L3) Deterministic, on C_J: G_sh ≥ G′ − K.  If S_{2r+2} − 1 ≤ top[2r+1] then |B_r| = u_r − 1; otherwise
  S_{2r+2} = top[2r+1] + 2 = top[2r+2] (α < 2), a contact.
* (L4) Contacts: P*(S_i ≤ top[i] ∀i, K ≥ k) ≤ p^k.  With h_i = top[i] − S_i and inc_i = top[i] − top[i−1] ≥ 1, a
  step from h_{i−1} ≥ 0 reaches h_i ≤ 0 iff d_i ≥ h_{i−1} + inc_i, and by memorylessness of the geometric digit lands
  exactly on 0 with conditional probability p.  M_n = Π_{i≤n}(1[no touch] + 1[touch, h_i=0]/p) is a mean-1 martingale;
  on {confined, K ≥ k}, M_J ≥ p^{−k}.
* (L5) P*(S_J = sg) = binom(sg−1,J−1)p^Jq^{sg−J} ≥ 1/poly(J) (Stirling; (J−1)/(sg−1) = p + O(1/J)); exact value
  ≈ J^{−3/2}·const is not needed.
**Theorem (ShapeLD, PROVED MATH).**  For 0 < t ≤ 1, 0 < x < 1, k ≥ 1, a ≥ 0:
  P_conf(G_sh ≤ a) ≤ J t^{−(a+k−1)} x^{−sg} F_t(x)^R / binom(sg−1,J−1) + J p^k / P*(S_J = sg).
Consequently for every g < p_g(N₀): P_conf(G_sh < gR) ≤ poly(J)·2^{−c(g)J} with
c(g) = max_ε min(I(g+ε)/(2 ln 2), ε·log₂α/2), I = Legendre rate below:
**N₀ = 4: c(0.05) = 0.0847, c(0.1) = 0.0732, c(0.2) = 0.0515 bits/step; N₀ = 2: c(0.05) = 0.0357, c(0.1) = 0.0257,
c(0.2) = 0.0083.**  Finite-J (exact |C_J|, `CHECK_BOUND.txt`): the bound dominates the exact DP probability in all 8
cases; N₀ = 4, g = 0.1: log₂ bound = −2.9, −16.1, −44.1, −72.7 at J = 200, 400, 800, 1200 (exact: −72, −138, −270, −402).

## 3. Pressure and Legendre rate (upper bound PROVED MATH; sharpness COMPUTATIONAL)
ψ(t) = inf_x[ln F_t(x) − 2α ln x] − inf_x[ln F_1(x) − 2α ln x] (nats per pair); (L1)+(L2) give
limsup (1/J)log₂E_conf[t^{G′}] ≤ ψ(t)/(2 ln 2).  Values per step (bits):
| t | 0.1 | 0.25 | 0.5 | 0.75 | 0.9 |
|---|---|---|---|---|---|
| N₀ = 2 | −0.2221 | −0.1799 | −0.1148 | −0.0551 | −0.0215 |
| N₀ = 4 | −0.4940 | −0.3822 | −0.2291 | −0.1047 | −0.0399 |
Legendre rate I(g)/(2 ln 2) = sup_t[−ψ(t) − g ln(1/t)]/(2 ln 2), bits/step:
| g | 0.02 | 0.05 | 0.1 | 0.15 | 0.2 | 0.25 |
|---|---|---|---|---|---|---|
| N₀ = 2 | 0.1935 | 0.1399 | **0.0801** | 0.0411 | 0.0166 | 0.0035 |
| N₀ = 4 | 0.5061 | 0.4284 | **0.3285** | 0.2496 | 0.1853 | 0.1324 |
Exact DP shape-only rates at g = 0.1: N₀ = 4: 0.361, 0.346, 0.338, 0.335 (J = 200…1200; a + b/J fit → 0.330);
N₀ = 2: 0.103, 0.093, 0.087, 0.085.  **The Legendre prediction matches the exact confined DP** (COMPUTATIONAL): the
shape large deviation is the iid pair-sum Cramér rate with the mean constraint E u = 2α; confinement and the endpoint
cost only polynomial factors.  The rigorous c(g) is smaller only because of the crude contact term (L4).
Diffusion picture (HEURISTIC): the bridge state (top[2r] − S_{2r})/√J is an excursion-type diffusion, but the shape
functional is local in u_r, so the limiting pressure does not depend on the diffusion; the state space matters only
through contacts.

## 4. Reduction of the true count (PROVED MATH)
Under the uniform law on C_J, conditional on the class (even prefix sums), the internal odd prefix sums x_r are
independent and uniform on B_r (fibre = Π_r B_r; Lean `recW` construction in BlockCubeInstance).  A shape-good block is
bad iff all eligible cells (m − x, 2r+2), x ∈ B_r \ {max B_r}, are black; then P(x_r eligible and black | class)
= (|B_r| − 1)/|B_r| ≥ 1/2.  With N_odd(w) = #{r : cell (m − S_{2r+1}, 2r+2) black}, Hoeffding gives
  **P_conf(G_true < gR) ≤ P_conf(G_sh < (g+β)R) + P_conf(N_odd ≥ βR/4) + e^{−βR/8}**  (g + β < p_g).
So the joint shape × colour large deviation (which defeated the deterministic decomposition) splits into the proved
shape theorem and a **single-cell** statistic.  Numerically E N_odd ≈ 0.035R (black ≈ 2η), and for N₀ = 4, g = 0.1,
β = 0.3 one needs P_conf(N_odd ≥ 0.075R) ≤ 2^{−cJ}, i.e. about twice the mean (the exact black-count tail from the
white-count round, P(N_B ≥ 0.1J) = 2^{−(0.04–0.08)J}, supports this; the odd-cell tail itself was not computed).
For general low frequencies λ the same argument works with λ-black cells (distZ(λy/3^b) < η; `distZ_phase_ge`).

## 5. Structural notes (PROVED MATH, from the kernel)
Minimal arithmetic state: the step (a, b) → (a − d, b + 1) maps U ↦ centered((2^dU + j)/3), where j is the next 3-adic
digit of 2^{−(a−d)} and is not a function of any finite number of leading digits of U.  So a fixed-K automaton is
exactly the random-digit surrogate, and the difference from the true operator is not confined to near-threshold cells:
Parts XXIX–XXXV's boundary-error formulation is not viable as stated (the digit sequence is the arithmetic content).

## 6. Status
* PROVED (MATH): Chernoff/partition-function identities, bridge/Feynman–Kac form, ShapeLD theorem with explicit
  rates, the reduction of §4.  COMPUTATIONAL: Legendre rate = exact DP rate.  Not started (stop rule): true-environment
  Z_J(t) tables, bulk/endpoint split, two-parameter operator numerics, η/N₀ optimisation, Lean interface.
* Rigorous γ still 0 (the black-count lemma is OPEN); A > 1/α not proved.  If the reduced lemma holds at η = 1/54,
  N₀ = 4, g = 0.1: γ = min(0.1·log₂(1/0.999154), c) = 1.2·10⁻⁴ (HEURISTIC payoff, E ≈ H₂ − 4·10⁻⁶).
* Remaining lemma (OPEN): ∃β′ > 0 below (p_g − g)/4, c > 0: P_conf(#{black odd path cells} ≥ β′R) ≤ 2^{−cJ}
  (uniformly in low frequencies for the λ-black version).
* LEVEL 1.
