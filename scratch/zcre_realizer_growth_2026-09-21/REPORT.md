# ZCRE realizer-growth: computational cross-checks

Companion to `docs/ZCRE_REALIZER_GROWTH_AUDIT.md` and `EOC/ZCRERealizerGrowth.lean`. These
tests do not prove anything; they stress-test the theorem
`boundedPrefixRealizers_iff_positiveRealizer` and probe the surrounding open questions before
committing to the Lean proof.

## `realizer.py` → `REALIZER_OUTPUT.txt`

Exact-arithmetic (`math.gcd`-free, `pow(base,-1,mod)` modular inverse) implementation of
`Carry.q`/`Realizer.leastRealizer`, matched definition-for-definition against
`EOC/Carry.lean` and `EOC/Realizer.lean`. **First run had a bug**: inverted `3` instead of
`3^N` when solving for the least realizer, which produced apparently-unbounded, non-stabilizing
sequences that would have *contradicted* the theorem proved in `EOC/ZCRERealizerGrowth.lean`.
Fixed (invert `pow(3, N, mod)`), and after the fix: for every tested real seed (3, 7, 9, 11, 13,
15, 27, 31, 63, 127, 6171, 837799), `leastRealizer d N ≤ m0` for every `N` tested, and the
sequence stabilizes exactly at `m0` at a finite `N`. This matches
`leastRealizer_le_of_realizes` and `leastRealizer_eventually_constant_of_bounded` exactly, and
is recorded here as the "adversarial check found and fixed an implementation bug before trusting
a computational result" instance this kind of audit is supposed to produce.

## `synthetic.py` → `SYNTHETIC_OUTPUT.txt`

Four strategies for constructing symbolic zero-corridor words (`min`: digit 1 always; `max`:
digit as large as the corridor allows; `rand`; `alt`: alternating) not derived from any real
orbit. In every case tested (length 40), the least realizer grows very quickly (looks
super-polynomial within the tested range) with no sign of boundedness. Consistent with — but
far from a proof of — ZCRE. No exception found in this limited search.

## `divergence_test.py` → `DIVERGENCE_OUTPUT.txt`

Takes a real seed's actual word for 8 steps, then deliberately deviates (bumps one digit within
the zero-corridor cap) and continues minimally. The least realizer leaves the seed's value at
the deviation step and does not return to any small value in the tested range — supportive,
again not conclusive, of the qualitative picture that departing from an actual orbit's word
forces rapid realizer growth.

## What these tests do NOT show

No search here was adversarial enough to be informative about whether ZCRE is *true* — only
whether the *theorem actually proved* (`boundedPrefixRealizers_iff_positiveRealizer`) is
consistent with real data (it is) and whether an obvious synthetic construction defeats it
(none found, but the search was small and not adversarially designed against the theorem — it
cannot be, since the theorem is proved, not conjectured).
