# Transport bridge audit: the coordinates degenerate on genuine seeds (round of 2026-09-16, part 11)

Nothing committed or pushed; no new Lean (Part XLIV: the mathematics settles negatively, so nothing was
formalized).  Data: `lock.py` (exact, big-integer).

## Verdict: classification **C — no bridge** (PROVED (MATH) + COMPUTATIONAL)
The transport coordinates `(F, M, H, δ)` are non-trivial for *arbitrary admissible words*, where the least
realizer changes with `j`.  For the endgame object — a **genuine seed's own word** — they degenerate into
restatements of `L₁(m)`, and the proposed "no post-lock failure ⇒ huge matching precision" bridge is circular.

## 1. Anchor lock is trivially true (PROVED (MATH))
If `m` realizes `D_j` then `m ≡ r(D_j) (mod 2^{S_j})`; if moreover `m < 2^{S_j}` then `m = r(D_j)`, `β_j = 1`,
`χ_j = m`.  The lock time is `j₀ = min{j : S_j > log₂ m} = O(log m)`; measured values:
| m | 27 | 703 | 35 655 | 270 271 | 1 859 241 | 10 507 503 |
|---|---|---|---|---|---|---|
| `j₀` | 4 | 8 | 11 | 14 | 16 | 19 |
| `S_{j₀}` | 5 | 10 | 16 | 19 | 23 | 25 |
| `log₂ m` | 4.75 | 9.46 | 15.12 | 18.04 | 20.83 | 23.32 |
and `r(D_j) = m` for **every** `j ≥ j₀` on all six prefixes (verified exactly).

## 2. The coordinates collapse (PROVED (MATH), verified to 0.0e0)
After the lock, `χ_j = m`, hence along the seed's own prefix (`L = L₁(m)`):
* **`F_j = S_j − log₂ m = R_j + jα − log₂ m`** — the coarse depth is the drift plus a deterministic ramp
  (max deviation over all six seeds: `0.00e+00`).  So "deep negative `R`" and "high `F`" are the *same* variable
  up to the ramp: `F` grows by `d_{j+1}` every step regardless of the excursion structure (Parts I, III, IX).
* **`δ_{j+1} = d_{j+1} − (F_{j+1} − F_j) ≡ 0`** — the transport deficit vanishes identically after the lock, so
  **post-lock failures are impossible** (Parts XXVI–XXIX are correct, but as a *tautology*, not a theorem with
  content: a fixed seed is its own anchor forever).
* **`M_j = S_L − S_j`** (the depth still realizable by the same seed) and therefore
  **`H_j = F_j + M_j = S_L − log₂ m`, constant** — verified constant on all six prefixes, e.g. `H = 56.245` for
  `m = 27` and `283.675` for `m = 10 507 503`.  `H` is nothing but the seed's total confined depth.

## 3. Why the bridge is circular (Parts XXXIV–XLII)
The proposed chain was: post-lock transport must be perfect ⇒ `M_{j₀} ≥ S_N − S_{j₀} = Ω(m)` ⇒ an exponentially
precise congruence on a seed of size `m`.  But `M_{j₀} ≥ Q` unwinds to `m ≡ −C_{j}3^{−j} (mod 2^{Q+S_{j₀}})`,
i.e. exactly "m realizes the longer prefix", i.e. `L₁(m) ≥ N`.  So the requirement is **equivalent to the
hypothesis**, not an extra restriction: no transport-specific obstruction was found (Part XLIII: none of
zero-deficit sequences, cylinder nesting, lift-bit constraints or parity gives anything beyond the realizer
congruence).  Likewise `G_tot`, `G_max`, regeneration counts are identically zero after the lock, so no growth
demand can be extracted (Parts VIII, XII–XVI): **confinement alone imposes no nontrivial lower bound on
`H_max`, `G_tot` or the number of high-`F` excursions.**
The minimal-counterexample strengthening (`m_j ≥ m`, `U_j ≤ e^{2/3}`) does not change this: it constrains the
orbit heights, not the anchor, which is already pinned to `m`.

## 4. What remains true and useful
* `r_min(N,1) ≤ m` whenever `L₁(m) ≥ N` (m realizes its own word) — the identity that makes the seed scan the
  correct way to compute the record frontier.  Its converse direction (`m < 2^{S_j} ⇒ m = r(D_j)`) is the lock.
* The endgame target is unchanged: `L₁(m) < Cm` for some `C < 3 ln 2 = 2.07944`, equivalently
  `r_min(2^k,1) ≥ 2^k` for large `k` (Lean: `EOC/DirectDescent.lean`).

## 5. Status
* PROVED (MATH): anchor lock; `F_j = R_j + jα − log₂m`; `δ ≡ 0` post-lock; `H ≡ S_L − log₂m`; circularity of the
  matching-precision requirement.
* COMPUTATIONAL: the table above, exact on the six record seeds.
* REFUTED: the transport bridge as a source of new information about `L₁` (classification C); the
  "post-lock failure impossibility ⇒ contradiction" argument (true but vacuous).
* OPEN: `L₁(m) < 2m` eventually; the dyadic floor.  Collatz not proved.  LEVEL 1.
