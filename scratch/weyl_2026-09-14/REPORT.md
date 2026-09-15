# Weyl sums of least realizers and the post-fresh-bit count (2026-09-14)

Nothing committed or pushed. New Lean: `EOC/ShellWeyl.lean`, `EOC/PrefixSuffixBilinear.lean`
(both in `EOC.lean`; full build passes, 3315 jobs — the job count rose from 2282 because of the
Mathlib circle-character imports; standard axioms only; no sorry).

## Tools
* `weyl_words.c` — enumerate U-confined words, per shell: top-block histogram of r_w (B=16 bits) and
  exact additive Weyl sums W_s(h), h≤64. Data: c=0 N=10..24 (N=24: 8.2e8 words), c=1 N=20,22,
  c=2 N=21 (`weyl_m0_c*_N*.bin`, large; regenerable).
* `weyl_analyze.c`, `weyl_peaks.c`, `weyl_scaling.c`, `weyl_zeros.c`, `tilt_byshell.c`,
  `shell_profile.c` — shell statistics, Fourier peaks, across-N scaling, exact-zero test.
* `tilt_fourier.c` — Monte Carlo Haar (free critical-tilt) Fourier expectation, 1e8 seeds.
* `prefix_states.c` — prefix end states m_P = T^{j0}(r_P) by prefix shell; verifies the
  concatenation formula (0 mismatches on 1.6e5 pairs). `pstate_analyze.c` — collision excess.
* `bilinear_check.c` — end-to-end check of the prefix/suffix bilinear decomposition.
* `transfer_closure.py` — Haar-closure transfer matrices at resolution 2^q.

## Headline
* **Exact discrete Fourier identity (LEAN):** for the dyadic cutoff 2^K on shell s (n=s+1−K),
  #{r_w<2^K} = 2^{-n} Σ_{g∈Z/2^n} V_s(g), V_s(g)=Σ_w e(g⌊r_w/2^K⌋/2^n) (no smoothing, no log).
  Chain Weyl ⇒ least-realizer bound ⇒ #E_U∩[0,2^K) ≤ (C e^{λ*U}/2)(2^K)^{1−I₀A} (LEAN,
  `exceptional_count_le_of_weyl`). Pointwise sufficient: |V_s(g)| ≤ (C−1)2^{-n}M_s.
* **Required strength for A=0.7:** n ≈ (αA−1)K = 0.1095K; saving 2^{-0.11K} on 2^{0.11K}
  frequencies = 21% of square-root cancellation. Random-point ceiling A* = 2/(α+I₀) = 1.2017.
* **Cutoffs (LEAN):** top-block characters see only suffix lift digits; dyadic additive
  frequencies 2^{S_N−S_J}h see only the prefix realizer r_J (the "early blocks drop out" guess is
  inverted: late blocks drop out of dyadic additive phases).
* **Concatenation formula (LEAN):** r(P·v) = r_P + 2^{S_P+1}k, k<2^{S_v} unique with
  T^j(r_P)+2·3^j k ≡ r_v (mod 2^{S_v+1}). Confinement couples P,v only through S_P ⇒ the
  post-fresh count is a sum of bilinear incidence counts (prefix end states × suffix realizers).
* **Bilinear collision bound (LEAN abstract; MATH assembly):** L_{σ,s} ≤ Haar·(1+√(2^tδ_X/|V|)),
  δ_X = relative collision excess of {m_P mod 2^{t+1}}. Suffix side is collision-free (exact
  Parseval); suffix-side averaging alone is provably insufficient (|V| < 4^n). Needed:
  δ_X ≲ |V|/2^t ≈ 2^{-0.05t} (A=0.7: 2^{-0.0055K}); random model gives 2^{-0.84K}.
* **Data (COMPUTATIONAL):** Z = least-realizer/Haar = 1.000±0.001 for A≤0.75 (N=21–24,
  c=0,1,2), ±1.5% to A≈1; coarse-scale top-block sums sub-Poissonian (χ²/dof 0.1–0.4), fine-scale
  ≈ random with fat-tailed peaks ≤ 29√M (stable in N ⇒ |V|/M ∝ M^{-1/2}); no exact zeros; confined
  tilt F_N(h) decays ≈ 2^{-0.7N}, free ≈ 0.54^N (random rate 3^{-N/2}); prefix-state collisions at
  0.004–0.9× random. Bilinear bound with measured δ_X gives L ≤ 1.19·Haar (A=0.71–0.75, j0=20).
* **Closure transfer operator:** nilpotent (index q−1, spectral radius 0), per-step mean-zero norm
  → 1 as q grows (0.50…0.81 for q=3..7; exactly 1 at forced-digit states).
* **Mauduit–Rivat:** not applicable — carry property fails (small archimedean perturbations of r
  change the whole valuation word); the needed input is Type-II (prefix states), not digital.
* **Classification: LEVEL 1.** No unconditional A>1/α. The target is sharpened to a second-moment
  (collision) bound for prefix least-realizer end states at post-fresh modulus 2^{(αA−1)K}.
