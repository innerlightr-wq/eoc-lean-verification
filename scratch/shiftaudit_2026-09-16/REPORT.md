# Shift audit and the named arithmetic frontier (research round, 2026-09-16)

Committed to the PR #9 branch at the end of the round.
New Lean: `EOC/ArithmeticFrontier.lean` (imported by `EOC.lean`; `lake build EOC` = 8803 jobs; axioms `propext,
Classical.choice, Quot.sound`).  Scripts: `shifts.py` → `shifts.jsonl`, `analyze.py` → `ANALYZE.txt`,
`certify_worst.py` → `CERTIFY_WORST.txt`.  **Positive stop condition 5 fired** (end-to-end implication in Lean).

## Formal dependency audit (PROVED MATH, read from the Lean statements)
Final theorem `WeightedChain.weighted_phi_decay_implies_exceptional_bound` (via `ShellwiseChain.exceptional_count_le_of_shellwise`):
* **j (= j₀)** is a single parameter, chosen per K subject to `collatzBarrier U j₀ < K`, `j₀ < N`, `N ≥ A K`.
  Pressure/LowFreqDecay is needed at that one j₀ per K (not for every large even j).
* **Shell pairs (s, σ)**, K ≤ s ≤ b_U(N), σ < K: `hpair` asks, per pair, for WeightedFourier with some ε (c = 1 + ε) or the
  trivial branch c ≥ 2^{s+1−K}; `hweight` asks for the **Haar-weighted sum** Σ c(s,σ)·haarShare(s,σ) ≤ C·haarMass.
  No supremum over (s, σ) is taken.
* **t = s − σ**, and the phase environment is 2^{−(m−z)} with **m = σ + 1 + t = s + 1**.
* Price of a bad pair: trivial branch 2^{s+1−K}; or ε from the trivial collision bound, ε² ≥ (2^t − 1)2^t/|V_{σ,s}| ≈ 2^t·poly
  in the Haar bulk.  Either way c(s,σ) ≳ 2^{t/2}.  Haar weights of t ∝ |V_{σ,σ+t}|·2^{−t} (negative-binomial profile around
  t ≈ 2(N − j₀), width ≈ √N).  A bad shift therefore costs ≈ 2^{t/2} times its weight; even a C growing polynomially in K
  (which leaves the final exponent 1 − I₀A unchanged) cannot absorb a bad shift except for t = O(log C).
  **Pointwise-in-t control is genuinely required** on essentially the whole shift range (kill condition 1 for t-averaging).
* **σ**: all shells σ < K appear with weights |P_σ|; ShapeTail/pressure are proved only at σ = ⌊j₀α⌋, offset 0 (the known
  lower-shell/offset gap); bad σ face the same exponential price.
* **u**: `hfin` of `DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve` **sums** over shells with weights
  min(1, 2^t/2^{u+1}); the uniform "∀ u ≤ U" of `LowFreqDecay` is an API convenience (sup-to-sum loss, recoverable).
* **λ**: already summed within each shell (`lowFreqDecay_of_summedPressure`).  But `summedPressure_of_dangerousWindows` asks
  for a dangerous count **for every λ** and sums the resulting moments; since a λ with excess count contributes
  2^{(excess)·j}, λ-averaging of counts gains only exponentially rare exceptions (sup-to-sum loss of exponential type).
* **Start state**: sup inside the window norm (sup-norm submultiplicativity); genuine for the window method.

| Parameter | Current hypothesis | Actually required downstream |
|---|---|---|
| j | every large even j (in wrapper statements) | one j₀ per K (∃ j₀ compatible with K, N) |
| t | each t separately | each t in the shift range; bad t cost ≳ 2^{t/2}: effectively pointwise |
| u | ∀ u ≤ U uniformly | weighted sum over u (API loss) |
| λ | count bound for every λ in a shell | exponential-moment sum over λ (only exponentially rare bad λ allowed) |
| σ | top shell only (proved part) | all σ < K (open) |
| start state | sup over states | sup (within the window method) |

## Shift averaging (PROVED MATH / COMPUTATIONAL)
* Full-period identity: Σ_{t<Q_D} F(2^{−t} mod 3^D) = Q_D·E_Haar[F] exactly for depth-D cylinder functions (2 is a primitive root).
* Natural t-range: the Haar bulk has width ≈ √N ≈ √(A K) ≈ √j₀, versus Q_D = 2·3^{D−1} with D ≈ 4K = j₀^{O(1)}: no full period.
* Moreover the audit shows averaging over t is not permitted anyway (exponential price of a bad shift).
* Structural observation (COMPUTATIONAL): the sup-over-start-states window rate is almost invariant under t ↦ t + 1
  (autocorrelation 0.92–1.00 at j = 400; constant maxima over consecutive t at j = 800, 1600), because the dark predicate
  depends only on a = m − z (`ArithmeticFrontier.dark_shift`) and a shift of t is absorbed by a shift of the start state.

## Computation (COMPUTATIONAL; floats for discovery, exact integers for the worst cases)
1230 environments, K = ⌈2 log₂ j⌉, θ_d = 1/10: j = 400 (306 consecutive t + 294 scattered large t + 100 Haar),
j = 800 (153 + 147 + 50), j = 1600 (60 + 60 + 20), and 40 consecutive shifts at A = 5 (j = 800).
* Dangerous windows: 0 in every environment; fraction of shifts with F_j(t) > 2/9: 0.
* Max window rate: λ = 1 scattered 0.0912 / 0.0865 / 0.0841; Haar 0.0874 / 0.0779 / 0.0776 (j = 400/800/1600); A = 5: 0.026.
* Exact certification of the three worst shifts per j (j = 400: t = 1502, 1516, 1540; j = 800: 4353, 4024, 35284;
  j = 1600: 56425, 56430, 53301): all windows certified safe, exact worst rate 0.0912.
* Longest dangerous run: 0.  Two-window codimension (Parts XXVII–XXVIII) not computed.

## Lean (PROVED LEAN, `EOC/ArithmeticFrontier.lean`)
* `PowerOfTwoDangerousWindowSparsity j t U K d a b` — the named arithmetic input (docstring states it is OPEN, not known to
  follow from equidistribution, not claimed equivalent to Erdős's conjecture).
* `summedPressure_of_powerOfTwoSparsity`, `lowFreqDecay_of_powerOfTwoSparsity` — end to end for any K ≤ A log₂ j + 1
  (A = 2, 5, 7 all allowed), C = 2 + (3/5)a + (4/5)A + (2 + (3/5)b + 4/5)/8.
* `dark_iff_distZ`, `uInv_modEq_shift`, `dark_shift` (shift translation), `black_fiftyfourth_iff`
  (black at η = 1/54 ⇔ 2|y| < 3^{b−3}, i.e. three leading balanced-ternary digits vanish).
