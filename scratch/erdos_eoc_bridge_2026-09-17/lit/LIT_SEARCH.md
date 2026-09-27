# Literature search: 2^n in Z_3, Erdős ternary problem, moving targets (2026-09-17)

Confidence tags: **[full]** = relevant pages/theorem statements read; **[partial]** = abstract + excerpts or model summary of HTML; **[abs]** = abstract only; **[mem]** = standard result cited from memory, not re-read.

## 1. Erdős ternary problem / Lagarias exceptional set

- **Lagarias, "Ternary expansions of powers of 2", J. LMS 79 (2009) 562–588, arXiv math/0512006.** [partial]
  Thm 1.4: for **every** nonzero λ ∈ Z_3, #{n ≤ X : λ2^n omits digit 2} ≤ 2·X^{log_3 2}. Real analogue (Thm 1.1): every λ>0, ≤ 25 X^{0.9725}. Thm 1.5: dim_H E^{(1)}(Z_3)=log_3 2; (1/2)log_3 2 ≤ dim_H E^{(2)} ≤ 1/2. Conjecture B: dim_H E(Z_3)=0.
  *λ=1:* the counting bound applies (it is Narkiewicz-type, exponent log_3 2); the dimension results do not.
- **Narkiewicz (1980)** N(X) ≤ 1.62 X^{log_3 2}. No exponent improvement found anywhere. A Lean formalization (GitHub `baobingzhang/jsp-000333-erdos406-lean`, dated 2026-09-17, JSP prize issue #312) states N(x) ≤ 2^{1−log_3 2} x^{log_3 2} (≈1.29) via "card ≤ 2^j on a period 2·3^j"; same exponent, not peer-reviewed. [abs]
- **Abram–Lagarias, "Intersections of multiplicative translates of 3-adic Cantor sets", J. Fractal Geom. 1 (2014) 349–390, arXiv 1308.3133.** [full, pp.1–9]
  Define E^{(k)}(Z_3) = {λ : ≥k values of 2^nλ omit 2}, Γ := lim_k dim_H E^{(k)}; dim_H E(Z_3) ≤ Γ. Thm 1.6: C(1,M_1..M_n)=Σ_3 ∩ ⋂ M_i^{-1}Σ_3 is a path-set fractal with dim = log_3 β, β Perron eigenvalue (computable). Thm 1.7: dim C(1,(1^k)_3) = log_3 β_k → 0 (β_k root of λ^k−λ^{k−1}−1). Thm 1.8: dim C(1,3^k+1)=log_3 φ ≈ 0.438 for all k. Thm 1.9: generalized exceptional set has dim ≥ ½log_3 2 (so arbitrary multipliers cannot give dimension 0; must use 2-power structure). Notes Senge–Straus/Stewart ⇒ n_3(2^n)→∞, and "dim C(1,M)→0 as n_3(M)→∞" would imply Conjecture B.
  *λ=1:* Haar/dimension statements only; no single-orbit consequence.
- **Abram–Bolshakov–Lagarias, "... II: two infinite families", Exp. Math. 26 (2017) 468–489, arXiv 1508.05967.** [partial]
  Family Q_k = 3^{2k}−3^k+1 gives dimension log_3 φ; yields **dim_H E(Z_3) ≤ Γ ≤ log_3 φ ≈ 0.438** (improving ½). Family P_k=2·3^k+1 has unboundedly many SCCs. Dimension-only.
- **Abram–Lagarias, "p-adic path set fractals and arithmetic", J. Fractal Geom. 1 (2014) 45–81, arXiv 1210.2478; "Path sets in one-sided symbolic dynamics", Adv. Appl. Math. 56 (2014), arXiv 1207.5004.** [abs] Framework: closure under ×(p-integral rationals), intersection; dim = log_p(spectral radius).
- **Dupuy–Weirich, "Bits of 3^n in binary, Wieferich primes and a conjecture of Erdős", J. Number Theory 158 (2016) 268–280.** [partial, via restatement in Li–Zhao] Averaged over the **full cycle** of p modulo q^m, the frequency of digit b among the lowest m base-q digits of p^n tends to 1/q (m→∞); proof via nonexistence of "higher Wieferich primes". For p=2,q=3 (2 primitive mod 3^m) this is essentially the elementary full-period equidistribution. Authors note a non-averaged version would imply Erdős. No single-n or short-range content.
- **Zhao–Li, "On β-adic expansions of powers of an algebraic integer omitting a digit", arXiv 2405.06220 (v2 Dec 2025).** [partial] Thm 1.8: #{n≤N : α^n omits a digit in β-adic expansion} ≤ C_1 N^{σ(β)}, σ=log(|Nβ|−1)/log|Nβ| (β unramified, residue degree 1). Generalizes Narkiewicz; **same exponent**, inexplicit constant; applies to every α (deterministic).
- **Li–Zhao, "Non-Wieferich property of prime ideals and a conjecture of Erdős", arXiv 2601.12753 (Jan 2026).** [abs] Number-field generalization of Dupuy–Weirich (full-cycle averages) + block complexity in ramified case.
- **Saye, "On two conjectures concerning the ternary digits of powers of two", J. Integer Seq. 25 (2022) Art. 22.3.4, arXiv 2202.13256.** [full] Verifies Erdős (no digit 2 ⇒ n∈{0,2,8}) and Sloane (no digit 0) for **all n ≤ 2·3^45 ≈ 5.9×10^21** (prior: Gupta n≤4373; Vardi n≤2·3^20). Method: Lemma 3.1 — u_k=2·3^{k−1} is ord of 2 mod 3^k, and d_{k+1}(2^{iu_k+j}) ≡ d_{k+1}(2^j) + i·d_1(2^j) (mod 3) — so each allowed k-digit tail lifts to exactly 2 allowed (k+1)-tails out of 3 (tree of size Θ(2^K)). Records ρ_χ(k) (OEIS A351927/A351928) match the "3-sided die" heuristic within ~4 orders of magnitude (outlier n=201015414581294 with 98 trailing non-2 digits).
- **Dimitrov–Howe, "Powers of 3 with few nonzero bits and a conjecture of Erdős", arXiv 2105.06440 (Rocky Mountain J. Math.).** [abs] Only 2^0,2^2,2^8 are sums of ≤25 distinct powers of 3; elementary congruence method.
- Minor: Aliyev, NNTDM 29(3) (2023) 474–485 [full pp.1–4] (combinatorics of "stairs" of 0/2 blocks; low k digits periodic with period 2·3^{k−1}); Roettger–Ren, arXiv 2511.03861 (2025) [abs] (numerics only, n≤10^6).

## 2. Shrinking targets / Borel–Cantelli for isometries, Z_p

- **Fan–Li–Yao–Zhou, "Strict ergodicity of affine p-adic dynamical systems on Z_p", Adv. Math. 214 (2007) 666–700.** [abs] x↦αx+β minimal iff α∈1+pZ_p (p≥3), β unit; then strictly ergodic, isometrically conjugate to x↦x+1; otherwise explicit strictly ergodic components. (x↦2x on Z_3: components are the spheres 3^jZ_3^×; on Z_3^× ≅ Z/2 × Z_3 it is a translation by a topological generator — an odometer.)
- **Fayad, "Two remarks on the shrinking target property", arXiv math/0501205.** [abs] Torus translation has monotone STP iff vector is of constant type; mixing does not imply MSTP. **Kurzweil (1955)** [mem]; **Tseng, arXiv math/0702853** (s-exponent MSTP for rotations) [abs]; **D.H. Kim** (Nonlinearity 2007; arXiv 1201.4568) [abs].
  All are statements for a.e. starting point with **fixed-center / monotone** targets.
- **Found no paper** on shrinking or moving targets for x↦ax on Z_p or for p-adic odometers specifically.
  *Applicability to λ=1:* none. Structural remark: since the system is a group translation, "2^n ∈ E_n" ⇔ n ∈ log-preimage of E_n (a union of residue classes mod 2·3^{k−1}). For one orbit the question is purely about how those residue sets sit in [1,N]. Generic-λ Borel–Cantelli is just averaging over translates.

## 3. Digits of 2^n in base 3

- **Low-order digits:** exact equidistribution over the period 2·3^{k−1} (2 is a primitive root mod 3^k) [elementary; Saye Lemma 3.1].
- **High-order digits:** governed by {n log_3 2} (Weyl; Benford-type). Discrepancy is controlled by the irrationality measure of log_3 2 (Baker) [mem].
- **Middle digits / normality of 2^n:** open. Only "complexity" results: **Senge–Straus (1973)**, number of nonzero base-3 digits of 2^n → ∞; **Stewart, J. reine angew. Math. 319 (1980) 63–72**, ≥ log n/(log log n + C) nonzero digits [mem/abs]; **Bugeaud–Kaneko, Math. Proc. Camb. Phil. Soc. 165 (2018) 533–540, arXiv 1704.00432** [abs] (S-units can't have few nonzero digits, quantitative). None counts occurrences of digit 2.
- Short exponential sums: see §6.

## 4. Furstenberg ×2×3

- Furstenberg 1967; Rudolph 1990; **Host, Israel J. Math. 91 (1995)** (×p-invariant ergodic positive-entropy μ ⇒ μ-a.e. x normal in base q); **Hochman–Shmerkin, Invent. Math. 202 (2015), arXiv 1302.5792**; **Shmerkin, Ann. Math. 189 (2019), arXiv 1609.07802** and **Wu, Ann. Math. 189 (2019), arXiv 1609.08053** (dim(A∩B) ≤ max(0, dim A+dim B−1) for ×p, ×q-invariant closed A,B). [mem] All are a.e.-μ or dimension statements for real sets.
- **Bourgain–Lindenstrauss–Michel–Venkatesh, "Some effective results for ×a×b", ETDS 29 (2009) 1705–1722.** [abs] Explicit (very slow, log-type) rate at which {a^n b^k x} becomes dense for **Diophantine-generic** x. It is the only single-orbit quantitative result, but it concerns real x and density, not counting in thin targets.
- **Glasscock–Moreira–Richter, J. LMS 109 (2024) e12902, arXiv 2007.05480** [abs]: integer analogues of intersection/sumset conjectures (mass/counting dimension). **Burrell–Yu, J. Number Theory 226 (2021), arXiv 1905.00832** [abs]: densities of integers with binary digits in bases 3, 4; zero-dim result.
  *λ=1:* {2^n} has counting dimension 0, so these give nothing for it.

## 5. Lacunary / Hardy–Littlewood–Pólya sequences

- Erdős–Gál (1955) LIL for lacunary trig sums; Philipp (1975) LIL for discrepancy of lacunary {n_k x}; **Philipp, Trans. AMS 345 (1994) 705–727**: LIL for discrepancy of {n_k x} with n_k the ordered S-units (e.g. 2^a3^b); **Fukuyama, Monatsh. Math. (2008)** exact constants [abs/mem]. Survey: **Aistleitner–Berkes–Tichy, "Lacunary sequences in analysis, probability and number theory", arXiv 2301.05561** [abs].
  All are **for Lebesgue-a.e. x**; they say nothing at rational x = a/3^k, which is exactly our case. I found no explicit theorem on Bohr-set measure {T : ‖N_iT‖<ε ∀i} for S-unit N_i beyond these (Riesz-product heuristics give ≈(2ε)^{#i}).

## 6. Korobov-type sums S = Σ_{n≤N} e(a b^n/m)

Source: **Vandehey, "Differencing methods for Korobov-type exponential sums", J. Anal. Math. (2019), arXiv 1606.07911** [full, §1–2.3], which restates the prior results:
- **Korobov (Lemma 2 in Mat. Sb. 89 (1972); Lemma 32 in *Exponential Sums and Their Applications*, Kluwer 1992):** gcd(a,m)=1, N ≤ ord(b,m) ⇒ |S| < √m (1+log m). Nontrivial only for N ≳ √m ≈ (period)^{1/2}.
- **Korobov, prime power (Thm 4 in 1972; Thm 33 in 1992):** p odd, m=p^α, α > 16β(p,b), r = log p^α / log N with 2 ≤ r ≤ α/(8β): |S| < 3N exp(−γ (log N)^3/(log p^α)^2), γ = 1/(2·10^6). Nontrivial once log N ≫ (log m)^{2/3}, i.e. **N ≥ exp(C k^{2/3})** for m=3^k. (p-adic/Vinogradov method; I did not find a published update using Bourgain–Demeter–Guth VMVT.)
- **Bourgain, J. Anal. Math. 106 (2008), Thm 8.28 / Cor 8.31:** for m^γ < N ≤ ord, |S| < N^{1−ε}. Vandehey estimates non-triviality needs N ≥ m^{C/√(log log log m)}.
- **Vandehey Thm 1.4:** m with prime factors in fixed P, N ≥ exp(log m/(log_2 log m − 3 log_2 log log m)) ⇒ |S|/N ≤ exp(−c (log log m)^{3/2}). Cor 1.2: N ≥ m^ε ⇒ |S| ≤ C m^{−δ} N(1+log m).
- **"Normal periodic systems"**: the digit application is Vandehey §7.1 (Korobov 1970 Mat. Zametki 8; 1972): digits of a/m in base b ↔ {a b^n/m}. I did not access Korobov's original statements beyond these restatements.

Translation to our setting: "digits j..j+w−1 of 2^n lie in pattern set P" ⇔ {2^n/3^{j+w}} ∈ a union of |P| intervals of length 3^{−(j+w)}·3^j. With Erdős–Turán, the count over n∈[M,M+N) is N·|P|3^{−w} + O(N/H + Σ_{h≤H} h^{−1}|S_h|) with m = 3^{j+w}. The shift M is absorbed into a.

## Results that directly bound how often 2^n mod 3^k (n in a SHORT range, length ~ poly(k)) lands in a digit-window set of density 3^{−c}

**None found.** Best available:
1. If the window's top depth K = j+w satisfies 2·3^{K−1} ≤ N, count exactly (complete periods).
2. Korobov prime-power bound: nontrivial for N ≥ exp(C K^{2/3}), which is superpolynomial in K.
3. Vandehey/Bourgain: N ≥ exp(K/log log K) or 3^{εK}.
4. Narkiewicz/Lagarias/Zhao–Li counting (≤ C N^{log_3 2}) holds for every λ, but only for the "all digits avoid 2" target. It comes from the 2-of-3 lifting tree, not from short-range equidistribution.

Note also that for N < K·log_2 3 and n starting at 0, 2^n < 3^K, so the top digits are 0. More generally, a with ‖a2^n/3^K‖ small for all n ≤ N plausibly exists when N ≲ cK, so no uniform-in-a bound can hold at linear length. Poly(k)-length equidistribution for all frequencies is an open regime.
