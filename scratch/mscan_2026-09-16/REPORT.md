# The actual environment family λ2^{−m}: averaging, complexity, local windows (round of 2026-09-16, part 4)

Nothing committed or pushed; no Lean changes this round (Part LII: formalize only after the right averaged theorem is
identified — it turned out not to exist, see §1).  Scripts/data here: `mscan.py` → `MSCAN.txt`; `oddsuper.py` →
`ODDSUPER.txt`; `digits.py` → `DIGITS.txt`; `verify.py` → `VERIFY.txt`.

**Three decisive findings.**
1. **The chain needs the estimate POINTWISE in m** (PROVED MATH, read off the Lean chain): averaging in m/t/σ is
   not available, so Candidates A and B of Part L do not suffice downstream.  m = s + 1 and a single bad shell costs
   more than the entire budget.
2. **The generic exceptional set has no exploitable low complexity** (PROVED MATH): it is genuinely a depth-J union of
   cylinders, with ≥ 2^{(log₂3 − c)J} of them, while the relevant m-range has O(J) elements — cylinder counting
   (Parts XII–XIV) is vacuous.  **Stop condition 6 fires.**
3. **Logarithmic superblocks survive and are now the best route** (stop condition 5 does NOT fire): J/(2K) windows each
   contributing a factor proportional to K still give e^{−cJ}; numerically, with K ≍ log J, the worst-window pressure
   would give a combined rate 0.020–0.028 bits/step.  This converts the global arithmetic LD into a **local** statement
   about strips of ≍ log J rows.

## 1. Pointwise vs averaged (Parts II–IV, XXVIII–XXXIII) — PROVED (MATH)
In `WeightedChain.weighted_phi_decay_implies_exceptional_bound`, the shells are pairs (s, σ) with K ≤ s, σ < K, and
**m = σ + 1 + t = σ + 1 + (s − σ) = s + 1 depends only on s**, so σ-averaging and t-averaging give nothing new (Parts
XXXI–XXXIII): the (σ,t) family collapses to one m per s.  Each shell may use either the Fourier branch (cost 1 + ε) or
the trivial branch (cost 2^{s+1−K}); only the Haar-weighted sum must be ≤ C·budget, where
haarShare(s,σ) = |P_σ|·|V_{σ,s−σ}|·2^K·2^{−(s+1)} and (by `sum_fresh_split`) Σ_σ |P_σ||V| = #{words of total s}.
Hence the trivial branch at one shell costs exactly 2^{s+1−K}·haarShare = |P_σ|·|V| = **the raw word count of that
shell**, whereas the whole budget is C·Σ_{w} 2^K2^{−(total+1)} ≈ C·2^{K−1}.  A bulk shell has ≫ 2^K words, so **not a
single bulk shell may be dropped**: the Fourier bound (hence CriticalWhiteCount, hence the odd-dark pressure) is needed
for every m in the range.  The m-range is m = s + 1, s ∈ [N, barrier(U,N)], i.e. an interval of length Θ(N) = Θ(J).
Consequence: Candidate A (m-averaged) and Candidate B (sparse exceptional m) are **insufficient**; only Candidate C
(pointwise) closes the chain.  (Stop condition 1 is answered in the negative.)

## 2. The ξ-family is one orbit (Parts V, XXI, XXII, XLVII–XLIX) — PROVED (MATH) / verified
ord_{3^b}(2) = 2·3^{b−1} (2 is a primitive root mod 3^b; checked b ≤ 8 in `VERIFY.txt`).  Therefore every unit is a
power of 2, and **λ2^{−m} = 2^{ℓ(λ) − m}**: the whole family {λ2^{−m}} is a single orbit of the translation
x ↦ x − 1 in the discrete-log coordinate ℓ ∈ ℤ/(2·3^{b−1}), and λ only shifts the window by ℓ₂(λ).  Changing m by 1
translates the path's column window along the fixed Tao array.  Each unit cylinder mod 3^K is hit by exactly one
residue class of m mod 2·3^{K−1} (checked exactly for K = 6, λ = 5).  The m-interval (length Θ(J)) is a vanishing arc
of the period 2·3^{b−1}: full-period averaging (Part VI) is unavailable by a factor 3^{J−O(log J)}.

## 3. Black cells as cylinders; exceptional-set complexity (Parts VIII–XVII) — PROVED (MATH)
At η = 1/54, black(a,b) ⟺ the three leading balanced-ternary digits (positions b−3, b−2, b−1) of ξ2^{−a} vanish; as a
condition on ξ it is a union of cylinders of depth b, of Haar measure exactly 1/27 (three digits fixed).  Minimal
modulus: 3^b (not 3³) — the condition involves the top digits of ξ2^{−a} mod 3^b, so the required residue information
grows with the row.  Along a path the r-th and (r+1)-st conditions share one digit position: this is exactly the
2-state overlap used in the generic theorem.
**Complexity.**  Ψ_J(ξ) = (1/J)log₂E_conf,ξ[s^{N_odd}] depends on ξ mod 3^{J}; a change in the last δJ digits moves Ψ
by at most δ·log₂(s)/2 (0.29δ at s = 1.5, 0.79δ at s = 3), so E_J is, up to ε, a union of cylinders of depth
(1 − O(ε))J and no shallower.  With measure 2^{−cJ}, the number of cylinders is ≥ 2^{(log₂3 − c)J} (e.g. 2^{626} at
J = 400, c = 0.02), while the hit bound of Part XII gives #{m ∈ I : λ2^{−m} ∈ E_J} ≤ #cylinders·(|I|/period + 1) —
vacuous against |I| = Θ(J).  **Cylinder-counting/entropy-balance (Parts XIII–XVII) cannot derandomize this orbit.**

## 4. m-scan (Parts XIX–XXVII, XXI) — COMPUTATIONAL (exact environments, float DP)
Ψ_J(m) at s = 3 (the quantity `OddDarkPressure` must bound; the reduction needs Ψ ≲ 0.085 at β = 0.17, N₀ = 4, g = 0.1):
| J | window | mean | sd | 95% | 99% | max | density Ψ ≥ 0.085 | longest bad run |
|---|---|---|---|---|---|---|---|---|
| 50 | 2·10⁵ | 0.0395 | 0.0248 | 0.0863 | 0.1141 | 0.2123 | 0.0533 | 23 |
| 100 | 10⁵ | 0.0422 | 0.0166 | 0.0722 | 0.0895 | 0.1625 | 0.0154 | 17 |
| 200 | 2·10⁴ | 0.0447 | 0.0111 | 0.0646 | 0.0772 | 0.0955 | 0.0021 | 7 |
| 400 | 4·10³ | 0.0468 | 0.0070 | 0.0587 | 0.0645 | 0.0733 | **0 of 4000** | — |
The mean drifts up slowly (0.0395 → 0.0468) and the spread falls like ≈ 1/√J (sd·√J = 0.175, 0.166, 0.157, 0.140);
the exceptional density falls 0.053 → 0.015 → 0.0021 → 0, i.e. an empirical rate 0.085, 0.060, 0.045, > 0.030
bits/step — the orbit sees the same exponential rarity the generic (Haar) theorem predicts (the proven Haar bound at
this threshold is 2^{−0.0256J}: 0.17, 0.029, 8·10⁻⁴ at J = 100, 200, 400, so the orbit is *better* than the proven
generic bound).  Bad m are clustered (consecutive m share most of the array): autocorrelation at lag 1 exceeds the
independent value by 5–50×, with runs ≤ 23 (J = 50) falling to ≤ 7 (J = 200).  λ ∈ {1, 5, 7, 11, 13, 101, 1025} at
J = 100 give statistically identical scans (means 0.0420–0.0425, sd 0.0164–0.0169), as predicted by §2.
**At J = 400 no m in a window 10× longer than the entire relevant range is exceptional** — evidence for Candidate C,
not a proof.

## 5. Logarithmic superblocks (Parts XXXIV–XXXVIII) — COMPUTATIONAL / HEURISTIC
Blockwise Chernoff: E_conf[s^{N_odd}] ≤ poly·Π_windows sup_S M_K(S), so the exponent is J·P_K with
P_K = (1/2K)·log₂ max_{r0} sup_S M_K — **no 1/log J loss** (Part XXXVI's worry is unfounded).  Worst-window values
(sampled anchors, so lower bounds on the true sup):
| K | J = 200 | 400 | 800 | (s = 3) | | s = 1.5: 400 | 800 | | s = 2: 400 | 800 |
|---|---|---|---|---|---|---|---|---|---|---|
| ≈ log₂J | 0.239 | 0.288 | 0.244 | | | 0.096 | 0.080 | | 0.171 | 0.144 |
| ≈ 2log₂J | 0.190 | 0.158 | 0.138 | | | 0.052 | 0.044 | | 0.093 | 0.081 |
| ≈ 4log₂J | 0.109 | 0.099 | 0.111 | | | 0.030 | 0.032 | | 0.056 | 0.061 |
| 64 | 0.062 | 0.071 | 0.080 | | | 0.021 | 0.024 | | 0.039 | 0.045 |
Feeding these into the reduction (rate = min(c_shape(g+β), β·log₂((1+s)/2)/2 − P_K), N₀ = 4, g = 0.1) gives a positive
combined rate **0.0199 bits/step at K = 4log₂J** (β = 0.265, s = 3) and **0.0277 at K = 8log₂J** (β = 0.22).
So the route closes numerically *if* the worst-window bound holds uniformly in J.  The remaining input is local:
> **LocalWindowPressure(K, θ):** for every window of K ≍ log J consecutive pair blocks and every confined start state,
> sup_S M_K(S) ≤ 2^{2Kθ}.
Bad start states are exactly those whose next cells are black (inside a triangle), so this is a statement about black
density in strips of ≍ log J rows.  There are only J/(2K) strips, each needing a bound that a Haar environment
violates with probability J^{−c'}: a union bound then needs only c' > 1 — far weaker than the global LD.  Caveat: at a
fixed ratio K/log₂J the sampled worst-window values drift up slightly with J (0.099 → 0.111 at 4log₂J), so uniformity
is not established (HEURISTIC).

## 6. Digit statistics and literature (Parts XL–XLVI)
Ternary digits of 2^{−a} to depth 2·10⁴ (`DIGITS.txt`): for a in the band (700, 1401, 2102, 100003) digit frequencies
are 0.328–0.337 each, aligned 3-zero-window density 0.0353–0.0387 (Haar 0.03704), max zero run 7–12 ≈ log₃D,
autocorrelations ≤ 0.013 — indistinguishable from Haar (COMPUTATIONAL).  Small a (1, 5) is degenerate, which is the
region the buffer t = J/6 avoids.
Run formulation (Part XLIV/XLV): N_odd is a count of aligned 3-zero windows in the ternary expansions of the numbers
2^{−a} along the path, one window per row, so the needed lemma is a **zero-window-density** statement.
**Literature (EXTERNAL THEOREM where stated):** Stewart (1980), via Baker's method, gives for m ≥ 25 that the number of
nonzero base-3 digits of 2^m exceeds log m/(log log m + c) − 3 (after Senge–Straus 1971, which gives only → ∞).  We
need ≈ (1 − δ)J nonzero digits among J positions: the gap between log J/log log J and J is the whole problem.
Lagarias, "Ternary expansions of powers of 2" (JLMS 2009), studies exactly this 3-adic/×2 dynamical family and proves
smallness of the set of initial values whose iterates omit a digit; the Erdős ternary-digit conjecture (only 1, 4, 256
omit the digit 2) remains open.  Effective equidistribution of 2^n mod 3^k is available only for ranges of n that are
a positive power of the modulus, i.e. n ≥ 3^{ck}; our range is n ≍ k = O(log modulus) — no applicable result.
Multi-pattern Subspace-theorem (Part XLI): each black cell is |2^a y − 3^b z| ≤ 3^{b−3}/2-type; the Subspace theorem
gives finiteness/sublinearity of *large* solutions (the refuted size route), not density of shallow ones — not viable.

## 7. Status
* PROVED (MATH) this round: pointwise necessity (§1); one-orbit/discrete-log structure (§2); cylinder structure,
  Lipschitz depth and complexity lower bound of the exceptional set (§3); the blockwise-Chernoff exponent accounting (§5).
* COMPUTATIONAL: m-scan distributions and exceptional densities; λ-independence; superblock pressures; digit statistics.
* REFUTED this round: m/t/σ-averaging as a route; cylinder-counting derandomization.
* OPEN: `OddDarkPressure` pointwise, now best formulated as `LocalWindowPressure(K ≍ log J, θ)`.
* Best rigorous γ = 0; A > 1/α not proved; LEVEL 1.
