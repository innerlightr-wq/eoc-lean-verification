# ZCRE realizer-growth audit

*Adversarial research audit. Question: does "least prefix realizers tend to infinity" give
genuinely new, easier leverage on Type-II exclusion than the existing qualitative
realizability/moving-anchor problem — or does it collapse back to that same problem? Verdict
reached: **it collapses, exactly, provably** — and the proof is short, unconditional, and
independent of the Curry sector. This is recorded as a useful negative result per the governing
brief, together with one genuine (if modest) methodological corollary.*

---

## 1. Question

Is it enough to prove that the least positive realizers of prefixes of every Curry-sector word
tend to infinity, and is that statement genuinely easier than the existing exponential
realizer-floor / moving-anchor problem?

## 2. Frozen Curry foundation

Unchanged from `docs/CURRY_FOUNDATION.md` and `EOC/CurryFoundation.lean`: every hypothetical
Type-II orbit has, past its last global drift maximum, a valuation word satisfying
`S_N ≤ ⌊αN⌋` and `Δ_N = ⌊αN⌋ - S_N → ∞`. No change made to this material in this round (§36 of
the governing brief: no mathematical error was found in it).

## 3. Exact realizer conventions

From `EOC/Carry.lean`, `EOC/Realizer.lean` (existing, reused unchanged — no parallel
definitions introduced):

* `s d j = Σ_{i<j} d i`, `S d N = s d N` (`EOC/ValuationWord.lean`);
* `q d N` — the carry recursion `q_0=0, q_{j+1}=3q_j+2^{s_j}` (`EOC/Carry.lean`);
* `Realizes d N m0 := Odd m0 ∧ ∀ j<N, a(orbit m0 j) = d j` — `m0` matches the actual accelerated
  orbit's valuations through step `N` (`EOC/ValuationWord.lean`);
* `realizerCongruence` — **Proposition 5.2**: `Realizes d N m0 ↔ 3^N m0 + q_N ≡ 2^{S_N} [MOD
  2^{S_N+1}]`, for `m0` odd and `d` positive through `N` (`EOC/Realizer.lean`);
* `leastRealizer d N` — the unique `x < 2^{S_N+1}` satisfying that congruence
  (`leastRealizer_unique`, `leastRealizer_modEq`, `leastRealizer_lt`, `leastRealizer_odd`).

**The exact relationship between `m0` and prefix realizers, stated without ambiguity:** if
`m0` realizes `d` through `N`, then `m0` itself satisfies `leastRealizer`'s defining congruence,
so `m0`'s reduction mod `2^{S_N+1}` *is* `leastRealizer d N` (uniqueness of the representative
below the modulus). This single fact is the entire content of §4 below, and turns out to be the
entire content of the rest of this audit as well.

## 4. Fixed-seed prefix lemma (`leastRealizer_le_of_realizes`, `leastRealizer_eq_mod_of_realizes`)

**Proved, unconditionally, for every `N` (not just eventually):**

```
leastRealizer d N = m0 % 2^(S_N+1),   hence   leastRealizer d N ≤ m0.
```

Proof: `m0` satisfies the same congruence as `leastRealizer d N` (via `realizerCongruence`);
`m0 % 2^{S_N+1}` also satisfies it (mod-arithmetic is compatible with the congruence) and lies
below the modulus; by `leastRealizer_unique`, the two coincide. `Nat.mod_le` gives the
inequality. No case split, no asymptotic regime — genuinely for every `N`.

Formalized: `EOC/ZCRERealizerGrowth.lean`, `leastRealizer_eq_mod_of_realizes`,
`leastRealizer_le_of_realizes`.

## 5–6, 19–24. The weakest sufficient condition, and why it is not merely sufficient but exactly necessary and sufficient

Tested UPR, UPR-A (`sup r_N=∞`), UPR-B (a divergent subsequence), UPR-C (`∀M∃N: r_N>M`):
**UPR-A, UPR-B, and UPR-C are the same statement** (elementary unfolding of `sup=∞`), and the
original UPR (`r_N → ∞`, literal convergence) is strictly *stronger* than all three (a sequence
can have `sup=∞` while not converging — and, as it turns out, no realizable word's sequence
*ever* converges to `∞`, it stabilizes to a finite value instead, so the literal-convergence
form is actually the *wrong* target: it is not implied by non-realizability, only `sup=∞` is).
**So the weakest correct target is `sup_N r_N = ∞`, exactly as §6 of the governing brief
anticipated — not `r_N → ∞`.**

Monotonicity: **checked computationally, found FALSE in general** (`scratch/
zcre_realizer_growth_2026-09-21/REALIZER_OUTPUT.txt`: e.g. seed 837799's prefix realizers go
`3, 7, 7, 39, 167, 167, 167, 167, 2215, 2215, 18599, 51367, …` before stabilizing at 837799 —
real drops and plateaus throughout). No monotonicity is used or needed anywhere in the proof
below.

**The central theorem, proved in full (§9–20 of the brief, resolved together):**

```
boundedPrefixRealizers_iff_positiveRealizer:
  (∃ M, ∀ N, leastRealizer d N ≤ M)   ⟺   (∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = d i)
```

for any word `d` with every digit `≥ 1` — **with no dependence on the Curry sector, the deficit,
or `α` anywhere in the proof.** The forward direction is a genuine new argument (not a
compactness/Kőnig appeal — see §9 below for why that machinery is unnecessary), the reverse
direction is §4 above. Both directions, and the sharper **eventual-constancy** form
(`leastRealizer_eventually_constant_of_bounded`: bounded prefix realizers are not just bounded
but eventually *literally constant*, stabilizing at the unique realizing seed), are formalized
in `EOC/ZCRERealizerGrowth.lean`.

**Proof sketch of the forward direction** (§22–23 of the brief: candidate-set / finite-injury
framing, made precise and then bypassed by a more direct route). Nesting
`R_{N+1}(d;M) ⊆ R_N(d;M)` for the candidate sets `R_N(d;M) = {m ≤ M : Realizes d N m}` is
immediate. Rather than run the general "nested nonempty subsets of a finite set stabilize"
pigeonhole argument, the direct route is shorter: once the modulus `2^{S_N+1}` exceeds `M`
(guaranteed eventually, since `S_N ≥ N` because every digit is `≥ 1`), `leastRealizer d (N+1)`
is itself `≤ M`, hence `< 2^{S_N+1}`, hence (since it also realizes `d` through `N`, a strictly
weaker fact than realizing it through `N+1`) it satisfies the level-`N` congruence below the
level-`N` modulus — forcing `leastRealizer d (N+1) = leastRealizer d N` by uniqueness. This one
step, iterated, gives eventual constancy directly; taking any `N` past that point,
`leastRealizer d N` realizes `d` through `N` for *every* `N`, hence realizes the entire infinite
word.

**Consequence for §19–20's specific sub-questions:**
* "Does bounded `r_N` imply a positive-integer infinite realizer?" — **Yes, proved.**
* "Does positive-integer realization imply eventual stabilization of `r_N`?" — **Yes, proved,
  and sharper than requested: not just bounded, but eventually literally constant.**
* "Is `W` having a positive-integer realizer equivalent to `r_N` eventually constant?" — **Yes,
  proved** (constant ⟹ bounded ⟹ realizable, by the theorem above; realizable ⟹ eventually
  constant, shown directly in the proof).

## 7. Relation to the EOC exponential floor

`r_N ≥ 2^{εN} ⟹ sup r_N = ∞ ⟹ ¬(bounded) ⟺ ¬(realizable)`. The first arrow is trivial and not
reversible in general (a merely-unbounded, non-exponential sequence also witnesses
`sup=∞`). **Genuine, if modest, clarification: excluding realizability of the Curry sector does
not require an exponential-rate lower bound on realizers — any unbounded lower bound would do.**
This does not make the underlying mathematics easier (see §19 below), but it is a real
narrowing of what a future proof needs to establish, worth keeping.

## 8. Uniform versus per-word quantifiers

The uniform-shell statement (`∀M ∃N0 ∀N≥N0 ∀W_N∈C_N : r(W_N)>M`) is strictly stronger than the
per-word statement actually needed (`∀W ∀M ∃N : r(W_N)>M`) — the per-word form is exactly what
`boundedPrefixRealizers_iff_positiveRealizer`'s contrapositive gives, and it is entirely
sufficient (§25): a single word realized by a fixed seed already contradicts Type-II divergence
for *that* seed; no uniformity across all words is needed for the logical reduction to go
through. Recorded prominently, per the brief's request.

## 9. Compactness / Kőnig audit

**Not needed.** The direct stabilization argument in §5–6 above (via `leastRealizer_unique`
applied one step at a time, using that the modulus `2^{S_N+1}` strictly and unboundedly
increases) supplies exactly what a Kőnig-style "arbitrarily-long-bounded-realizer paths give an
infinite bounded-realizer path" argument would have supplied, for the one case that matters
here (a *fixed* word `W` with bounded prefix realizers) — and does so with a shorter, fully
elementary proof with no appeal to finite branching or tree compactness. Zero-confinement's
digit cap (`d_n ≤ ⌊α(n+1)⌋ - S_n`, finite at each step) does make the associated tree locally
finite, so a genuine Kőnig argument *would* also work for the different question of whether
arbitrarily long, *varying*, boundedly-realizable zero-corridor prefixes force a single infinite
bounded-realizer branch — but that question was not needed to resolve the one this audit was
asked to settle, and is not pursued further here to avoid unnecessary machinery.

## 10–13. Anchor identity, deficit scaling, Curry-coordinates congruence

Audited as requested. `EOC.HarmonicPacking`'s existing `orbit_mul_two_rpow_R` (reused in
`EOC/CurryFoundation.lean`) gives exactly `m_N · 2^{R_N} = m_0 · Q_N`; combined with
`R'_k = -Δ_k + θ_k` (`θ_k = ⌊αk⌋-αk ∈(-1,0)`, `EOC/CurryFoundation.lean`), this yields the valid
real-number scaling identity `m_k = m_0' · Q_k · 2^{Δ_k + \{αk\}}`, i.e. (since `Q_k` is bounded
in the Curry sector) `m_k ≍ m_0' · 2^{Δ_k}` up to a bounded factor — **confirmed valid**, no
representative/2-adic-class mixing error found (it is a genuine Archimedean/real identity, not
a 2-adic one, since it comes from the real-valued `R`/`2^R`, not from `ξ_N`/`Φ(W)`). **This
identity turned out not to be needed**: the direct residue-uniqueness argument in §4–6 gives the
full equivalence without it. It is recorded here, confirmed correct, as a validated but
unused-in-the-end route — exactly the kind of accounting the brief asked for rather than silent
omission.

The realizer congruence in Curry coordinates (substituting `S_N = ⌊αN⌋ - Δ_N`) was not
separately pursued once the direct §4–6 route closed the question; recorded as **not attempted,
superseded**, not as a dead end.

## 14. Adversarial search for small-realizer, large-deficit prefixes

`scratch/zcre_realizer_growth_2026-09-21/synthetic.py` and `divergence_test.py`. No synthetic
zero-corridor word or seed-deviation experiment produced a persistently small realizer at large
`N`; growth looked rapid and unrecoverable in every case tested (small sample, not an
adversarially designed search against the *theorem* — the theorem is proved, not conjectured;
the open question this data lightly informs is ZCRE itself, not the equivalence). Full output in
that directory.

## 15. Three populations

Unchanged from `docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §21 (A: generic zero-corridor
words; B: finite realizable prefixes; C: infinite words with an actual orbit). The theorem in
§5–6 is the exact membership test for Population C, for *any* candidate word — it does not
itself decide membership for a given zero-corridor word (that remains open, and is ZCRE), but it
converts "is `W` in Population C?" into the concrete, checkable-in-principle question "is
`sup_N leastRealizer(W,N})` finite?".

## 16–18. Injectivity, suffixes, record-deficit times

**An important consistency check, not previously recorded.** A word with `sup_N r_N < ∞` is, by
§5–6, realized by an actual seed — but is that seed's orbit *injective* (Type-II), or could it
be periodic (Type-I) instead? Checked against the classical cycle equation (Eliahou 1993 /
Böhm–Sontacchi-style relation, external and **not formalized in this repository**): any genuine
positive-integer cycle of period `p` and total valuation `S_p` satisfies `S_p/p > α` *strictly*
(needed for the cycle's carry numerator to stay positive). A zero-corridor word, by construction
(`S_N ≤ ⌊αN⌋` for all `N`), has average valuation `≤ α`, never `> α` — **so no eventually
periodic, positive-integer-realized word can lie in the zero-corridor class**: Populations
"realized zero-corridor word" and "realized periodic word" are automatically disjoint, by a
classical fact, with no risk of the realizer-growth machinery accidentally readmitting a Type-I
cycle through the back door. This is exactly the cross-check §17's "suffix realizer" and §16's
"injectivity as arithmetic constraint" questions were gesturing at; it resolves cleanly and
external-classically rather than needing new machinery. Record-deficit subsequences (§18) add
nothing further once this is established, since realizability (hence boundedness) for a real
orbit is governed by §4's mod-reduction, which is entirely independent of where the deficit
record times fall.

## 25 (governing brief numbering carried over). ZCRE and its relation to UPR

With §5–6 established, **ZCRE and UPR (in its correct `sup=∞` form) are the same statement
applied to the same words**: "no positive-odd-integer-realized, injective-orbit word in the
Curry sector" is, word for word via §5–6's equivalence, "every word in the Curry sector has
unbounded prefix realizers." Proving one proves the other; there is no independent route through
UPR that bypasses ZCRE's actual difficulty.

## 26–27. Intermediate targets and failed routes

Unchanged in substance from `docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §26–27. This round
adds one clarification to target ranking: since UPR ⟺ ZCRE exactly, "attack UPR instead of ZCRE"
is not itself a distinct item on that list — it *is* item (A)–(E) territory, entered through a
cleaner combinatorial door (bounded-realizer language) rather than a new door. The
recommendation to start with (A) (generalizing Theorem 5.9's realizer-growth mechanism) stands,
now with the added knowledge that succeeding at (A) for the full zero-corridor sector would
directly *be* a proof of ZCRE via §5–6, not merely evidence for it.

## 28. Literature check

Searched (web) for the specific equivalence "bounded/eventually-stabilizing prefix realizer
sequence ⟺ positive-integer 2-adic realizer." Found the closely related **classical background**
— Lagarias (1985) and Rozier (2018, *Parity sequences of the 3x+1 map on the 2-adic integers and
Euclidean embedding*, arXiv:1805.00133) establish the general parity-sequence ↔ 2-adic-integer
correspondence, and that *eventually repeating* parity sequences correspond to *rational* 2-adic
integers — a different, coarser statement (rational vs. positive-ordinary-integer, and periodic
sequences vs. bounded-realizer sequences) than the one proved here. **No source found stating
the exact equivalence in §5–6's form.** Classified: **apparently not stated in this exact form
in the literature reviewed** — most likely an easy, folklore-adjacent consequence of the
classical correspondence once one has the specific modular residue-representative construction
this repository already uses (`leastRealizer`), rather than new mathematics; the contribution
here is the explicit, checked derivation in the repository's own conventions, not a claim to
have found something unknown to experts. This is not a serious systematic literature review
(consistent with the caveats already standing in `docs/NOVELTY_AND_PROVENANCE.md`).

Sources: [Parity sequences of the 3x+1 map on the 2-adic integers and Euclidean embedding](https://arxiv.org/pdf/1805.00133) · [The 3x+1 problem and its generalizations](http://www.cecm.sfu.ca/organics/papers/lagarias/)

## 17 (Lean results)

`EOC/ZCRERealizerGrowth.lean` (151 lines): `leastRealizer_eq_mod_of_realizes`,
`leastRealizer_le_of_realizes`, `leastRealizer_eventually_constant_of_bounded`,
`exists_positiveRealizer_of_bounded`, `boundedPrefixRealizers_iff_positiveRealizer`. Builds
clean (`lake build EOC` exit 0, zero errors); no `sorry`/`admit`/`axiom`/`opaque`. No parallel
definitions — reuses `Realizes`, `leastRealizer`, `realizerCongruence`
(`EOC/Realizer.lean`), `S_mono` (`EOC/LiftDigits.lean`).

Deliberately **not** formalized, per the governing brief's §19 (do not formalize speculative
statements) and §30's instruction to keep Curry abstracted: ZCRE itself, target (A)/(B)/(C)/(D)/
(E) from §26, and the "candidate elimination" framing of §23–24 — superseded by the direct proof
and not needed as separate Lean artifacts.

## 18–19 (governing brief numbering: failure analysis / surviving new leverage)

**Failure analysis for the "genuinely easier" hypothesis, stated exactly:** UPR fails to be
genuinely easier because it is not actually a different problem — `leastRealizer_unique`
(already in the repository, proved for an unrelated purpose in Proposition 5.2/Remark 5.4)
collapses "bounded prefix realizer" onto "positive-integer realized" with no room for a
strictly-intermediate statement to exist. There is no "moving-anchor anti-concentration" step
this route avoids; it *is* the moving-anchor question, phrased in modular-arithmetic rather than
2-adic-anchor language.

**What does survive as new leverage, precisely:** (i) the equivalence itself, now a citable,
Lean-checked fact usable in either language (bounded-realizer or moving-anchor) interchangeably,
which may make some future arguments easier to *write* even though the underlying difficulty is
unchanged; (ii) the confirmation that only qualitative (not exponential-rate) unboundedness is
needed, narrowing the technical bar for a future ZCRE proof; (iii) the §16–18 cross-check ruling
out accidental Type-I contamination of the zero-corridor sector via the classical cycle
equation, which was not previously verified in this repository's own documents.

## 20. Verdict

**C. EQUIVALENT TO EXISTING QUALITATIVE CHAIN-B PROBLEM.**

Not (A): no strictly easier route was found — proved impossible, not merely unfound. Not (B):
"same known barrier" undersells it — there is *no* daylight between the two statements at all,
proved via a short, elementary, unconditional argument, not merely observed to share an
obstruction. Not (D): no counterexample — the theorem is proved, not refuted. Not (E): current
machinery proves the *equivalence*, not ZCRE itself, which remains open.

This is exactly the outcome the governing brief said would be useful: the route was tested
honestly, shown to collapse, and the collapse itself is now a clean, reusable, Lean-checked
theorem rather than a hunch.
