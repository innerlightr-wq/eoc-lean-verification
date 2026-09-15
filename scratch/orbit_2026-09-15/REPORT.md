# Shell (m) averaging and the power-of-2 orbit (round of 2026-09-15, seventh)

Nothing committed or pushed. Lean: `EOC/PowerOrbit.lean` (LTE `padicValNat_three_two_pow_sub_one`, `orderOf_two_zmod_three_pow`, orbit collision count, `Psi_shell_shift`, `ContinuationSpreading` ⇒ `WeightedFourier`); full build OK.

## Decisive answers
* Shell-shift identity (PROVED MATH): y'(m−1) = y'(m) mod 2^{m−1}, so |Φ_{m−1}(λ)| = |Φ_m(2λ)|.  Averaging over a window
  of W shells = averaging over the frequency set ∪_{k<W} 2^k·I_u: it adds log₂W bits of frequency entropy, no more.
* Effective m-window in the chain (COMPUTATIONAL, mwindow.c, A=0.7): 2^{H(s|σ)} = 11.4, 15.3, 18.0, 20.4, 21.9, 22.9 at
  K = 200…6400 with chain-contribution weights (Haar weights: 10.5 … 14.8) — bounded/logarithmic, while the nominal s-range
  is 0.11K and the orbit length ord_{3^n}(2) = 2·3^{n−1} is exponential.  Gain ≤ log₂W_eff ≈ 4.5 bits: θ unchanged.
* LTE: v₃(2^d − 1) = [d even](1 + v₃(d)); ord_{3^n}(2) = 2·3^{n−1}.  LTE controls only 3-adic closeness of orbit points;
  the λ-Dirichlet kernel needs archimedean closeness; |x| ≥ 3^{v₃(x)} gives a saving only for continuation depth
  k = n − N ≤ v₃ ≤ 1 + log₃W.  LTE-derived mean square ≈ trivial for k ≥ 1 (PROVED MATH).
* Orbit numerics (COMPUTATIONAL, ORBIT.txt): mean square / diagonal = 1.000 ± 0.02 for powers of 2, powers of 5, random
  units and path-weighted a (diagonal = 1/W); consecutive residues and frozen residue fail (up to 128 = W).
  So powers of 2 behave like random units, but the maximal gain from a W-window is a factor W (log₂W bits).
* Continuation as a walk on the exponent a ∈ ℤ/(2·3^{n−1}) with O(1) steps: mixing time Θ(3^{2n}) ≫ j0 steps.
* External theorems (Korobov-type sums over g^x mod p^n, Bourgain–Glibichuk–Konyagin) need windows of length at least
  superpolynomial in n (or a positive power of the modulus); available windows are polynomial: not applicable.
