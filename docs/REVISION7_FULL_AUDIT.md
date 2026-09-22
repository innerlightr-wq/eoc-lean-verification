# Revision 7: audit of the remaining sections

*Every section not covered by the targeted review, checked at the same level. Branch
`rev7-full-audit`, base `02174e2` (verified against `origin`).*

The targeted review examined `thm:DEequiv`, `cor:Uall`/`prop:occstop`/`rem:Uallscope`, and the §14
table. This audit covers the other 39 numbered claims, every numerical constant, and every
computational diagnostic.

**Result: thirteen findings.** Seven in the mathematical text (§A), six in the formal-verification
table and its status labels (§A2). Among them: a false numerical witness, a statement false at its
boundary, a misreported figure, three overclaims of the same logical form the reviewer identified, a
proposition labelled "formalized" that had no Lean theorem, and a build target that did not reach 15
of the 16 modules it claimed were machine-checked. **Four were introduced by Revision 7 itself,
while correcting other things.**

No error was found in any of the core identities, in the exact realizer congruence, or in the main
no-go theorem. All thirteen are corrected on this branch — two of them by strengthening the
development (formalizing the missing proposition; making the default build check every cited
module) rather than by weakening the claim.

---

## A. Findings

| # | Location | Finding | Severity |
|---|---|---|---|
| 1 | `cor:explicit` | "longest: $m=27$, 41 accelerated steps" — **false**; $m=73$ takes **42** | numerical claim wrong; conclusion survives |
| 2 | `prop:futuremin` | "If $R_n\le0$ then $m_n>m_0$" — **false at $n=0$** | statement wrong as written; proof already used $n\ge1$ |
| 3 | `rem:selffin` | self-financing margin "$+1.83$" — actual minimum over **all** steps is **$1.7370$** | figure wrong; conclusion survives |
| 4 | `cor:cycles`, abstract, `op:DE`, conclusion | "(DE) is **strictly weaker** than Collatz" — **not established** | overclaim, same form as the one already corrected |
| 5 | `rem:Uallscope`(iii) | "a **strictly weaker** assumption" | same form |
| 6 | `conj:strong` | $K$ is a free variable — never bound | definitional gap |
| 7 | abstract | "the natural global valuation-word shadows" — broader than §9.3 now states | internal inconsistency |

### 1. `cor:explicit`: the witness is wrong

The corollary asserts every odd $m<90$ reaches $1$ and names the longest run as $m=27$ at 41
accelerated steps. Exhaustively: the longest is **$m=73$ at 42 steps**; $m=27$ and $m=55$ tie at
41. The **conclusion is unaffected** — every odd $m<90$ does reach $1$ — only the witness is wrong.

Likely provenance: $27$ is famous for the longest *classical* $3n+1$ trajectory among small seeds
(111 steps, verified here). That fact was transplanted to the accelerated map, where it is false.

### 2. `prop:futuremin`: false at $n=0$

As stated: "If $R_n\le0$ then $m_n>m_0$." At $n=0$, $R_0=0\le0$ while $m_0>m_0$ fails. The
proposition's own two proofs both use $n\ge1$ — the first through $E_n>0$, the second through
$C_n>0$, and $E_0=C_0=0$. The Lean statement (`DriftExit.zeroCorridor_implies_seed_lt`) is
formulated at $n+1$ and is correct; only the paper's prose dropped the hypothesis.

**This is the third instance of the same pattern**, after `prop:occstop`'s $m_0=1,c=0$ case
(reviewer-found) and finding 3 below. In every instance the Lean statement carried the hypothesis
and the prose did not.

### 3. `rem:selffin`: the margin is misreported

The remark states that over all odd $m<200001$, the minimum over **all steps** of
$\log_2(3m_n+1)-(\al-R_n)$ is $+1.83$. Recomputed:

| range | minimum | attained at |
|---|---|---|
| odd $m<200001$, **all** steps | **$1.7370$** | $m_0=3$, step $n=0$ |
| odd $m<200001$, steps $n\ge1$ only | $1.8301$ | $m_0=3$, step $n=1$ |

So $1.83$ is the minimum with the **seed step silently omitted**. The qualitative conclusion —
never negative — is unaffected.

### 4. "(DE) is strictly weaker than Collatz" is not established

This appears in the abstract, `cor:cycles`, Open Problem `op:DE`, and the conclusion, and is
justified by `cor:cycles`: (DE) is compatible with nontrivial cycles.

That argument does not deliver strictness. Write Collatz $=$ (no divergence) $\wedge$ (no
nontrivial cycle); by `thm:DEequiv`, (DE) $=$ (no divergence). Then:

* Collatz $\Rightarrow$ (DE) — always;
* (DE) $\Rightarrow$ Collatz — **if and only if no nontrivial cycle exists**.

So (DE) is strictly weaker *precisely when* a nontrivial cycle exists — an open question whose
expected answer is **no**, in which case the two are **equivalent**. The claim is therefore not
merely unproved; the expected state of affairs makes it false.

**Correction to this finding, second pass.** The first correction replaced "strictly weaker" with
"(DE) does not entail cycle-freeness". *That is also unproved*, and for the same reason: if no
nontrivial cycle exists, the entailment holds trivially, so non-entailment would be false in the
expected case. The finding is therefore about what has been **established**, not about what is true.

What is established, and no more:

1. Collatz ⟹ (DE);
2. (DE) excludes divergence (`thm:DEequiv`);
3. (DE) together with exclusion of nontrivial positive cycles ⟹ Collatz;
4. every point of a cycle has finite `τ₀`, so the drift-exit argument supplies no cycle exclusion.

The correct phrasing, now used throughout, is: **no implication from (DE) to cycle-freeness is
established here.** Neither "strictly weaker" nor "does not entail" is claimed.

> **This is the same error of form that the reviewer identified for Level 3 vs Level 4** — a
> non-implication of *mechanism* being read as strictness of *content*. It survived that correction
> because the correction was applied only at the hierarchy, and because I wrote, in
> `rem:strictness`, that Level 1's strict weakness "*is* established". It is not. That sentence was
> introduced by me while correcting the adjacent error, and is now withdrawn.

### 5–7. Smaller items

* `rem:Uallscope`(iii) called a fixed-corridor bound "strictly weaker" than the corridor-uniform
  one. Implication one way is trivial; the converse is not known. Reworded.
* `conj:strong` reads "there is $C_c$ with $\Occ_c(m_0)\le K\log_2m_0+C_c$" with **$K$ never
  bound**. It must mean $K=1/I(\al)$ as in `conj:sharp`. Bound explicitly.
* The abstract still said "the natural global valuation-word shadows", broader than the narrowed
  §9.3 and conclusion. Made consistent, with the exact-criterion counterpoint noted.

---

## A2. Findings in §14 and the `\status` labels

The §14 table was checked row by row against the Lean sources, and every `\status{…formalized…}`
against an actual theorem. **Six further findings, four of them self-inflicted in Revision 7.**

| # | Location | Finding |
|---|---|---|
| 8 | `prop:corridorvalue` | Labelled "formalized" — **there was no such Lean theorem**. Added in this round (`SeparatedReturns.corridor_value_lower`), so the label is now true |
| 9 | `prop:occstop` Remark* | Claimed "the Lean statement carries them [$n^*\ge1$ and $m_0>2^{c}$]". The Lean hypothesis is the **non-strict** $2^{c}\le m_0$; and only the reaches-$1$ corollary is formalized, not the general eventually-periodic display |
| 10 | `thm:cardinality` | `\status{proved; formalized}` covers items (a)–(d); **only (a)**, injectivity and the abstract countability argument are in Lean. (b), (c), (d) have no Lean theorem, and the barrier is never instantiated at $w_b$ |
| 11 | §14 table rows | `ZeroConfinedSeed` and `CurryFoundation` rows omitted the **`ReciprocalSummable` hypothesis** — i.e. conditionality on the external, unformalized Theorem `thm:GTC`. `prop:lastmax`'s status string reused Revision 6's wording that the Lean file itself calls an over-claim |
| 12 | §14 table rows | Module misattribution (the gap bracket is in `TransportRegeneration`, not `TerminalZeroGap`); "forced/excess split" has **no theorem**; "disjoint-run bound" has disjointness as a *hypothesis*, not a conclusion |
| 13 | §14 preamble | **Only 1 of the 16 named modules was reachable from the library root**, so `lake build` — the CI default target — did not check the other 15. "Machine-checked" was true but not evidenced by the repository's own build |

Findings 8, 9, 11 (the `prop:lastmax` string) and part of 12 were introduced by Revision 7 itself,
in the course of correcting other things.

**Fixes applied.** Finding 8 is fixed by *formalizing* the missing proposition rather than dropping
the label. Finding 13 is fixed by importing all 16 modules from the library root and confirming
that `lake build` — the full default target — succeeds. The rest are corrected in the text, with
each status label now naming the hypotheses its formalization actually carries. The preamble also
records that the axiom claim rests on `#print axioms` runs that are not themselves committed, so it
is reproducible but not self-evidencing from the source tree.

---

## B. What was checked and found correct

**Core identities — all verified.**

| Claim | Check |
|---|---|
| `lem:ER` Eliahou–Rozier | consistent with `lem:aggregate` and used throughout without error |
| `lem:aggregate` | proof correct; $C_0=0$, $C_{n+1}=3C_n+2^{S_n}>0$ ✓ |
| `lem:integral` | $R_n\le0\iff2^{S_n}\le3^n\iff S_n\le\lfloor n\al\rfloor$ ✓ ($S_n\in\mathbb{Z}$) |
| `lem:wedge` | $R_i\le E_i\le i/(3m_0\ln2)$ ✓; boundary $i=0$ fine ($0\le0$) |
| `prop:congruence` | **verified on 300 random words**: the stated residue is a realizer and is least; 0 failures |
| `prop:transfer` | proof correct; $F^{-1}$ minimality used correctly |
| `prop:futuremin` (both proofs) | correct **for $n\ge1$** — see finding 2 |
| `prop:weaker` | $m_n<m_0\iff R_n>E_n$ ✓; $m=1$ exception exact ($R_n=E_n=(2-\al)n$) ✓ |
| `prop:selffin` | proof correct; cap $2^{d_n}\le3m_n+1$ ✓ |
| `prop:cylinder` | both claims correct, including the sign witness $1$ vs $1-2^k$ |
| `prop:corridorvalue` | correct, including at $n=0$ |

**Numerical constants — all verified.** Everything in this subsection is a *finite computation over
a stated range*; none of it is a proof of a universally quantified statement, and none is
extrapolated beyond the range given.

* $I_{\mathrm{Collatz}}=\al(1-H_2(1/\al))=(1-H_2(\rho))/\rho=I(\al)$: the three expressions are
  **algebraically identical** (verified symbolically and to 25 digits). Value
  $0.0793186127748553871\ldots$; the paper's 16th digit `…554` is a correct round. $1/I(\al)=12.607381$
  matches "12.6074" ✓. $\rho=0.63092975$ ✓.
* $m^*(13,100,1)=90$ ✓ — and **least**: the inequality fails at $m=89$ ($185.07<185.18$) and holds
  from $90$ on.
* $\beta_*=0.9653844$, $\gamma_*=0.6090897$, $1/\beta_*=1.0358567$ ✓ (checked in the Curry audit).
* `lem:carrybudget` $m_k\not\equiv0\pmod3$ for $k\ge1$: **0 violations** over odd $m<20000$.
* Frontier ratio "under 10": max $\Occ_1(m)/\log_2m=8.4124$ at $m=27$ over odd $m<200001$ ✓.
* $\tau_0=\sigma$ away from cycle minima: **observed** with 0 exceptions over odd $3\le m<60001$ —
  a **computational check over a finite range, not a proof**. What is proved is $\tau_0\le\sigma$
  in general (`prop:weaker`) plus the polynomial window confining any strict example
  (`rem:howweak`); the equality itself is not proved for all seeds.

**`thm:cardinality` — proof checked line by line and correct.** The digit count
$\#\{i<n:i\equiv2\ (3)\}=\lfloor n/3\rfloor$ is right (checked at $n=2,3,4,5,6$); the cubing step
$3(n+\lfloor n/3\rfloor)\le4n$ with $16\le27$ is right; $(4/3-\al)=-0.2516\ldots$ ✓; injectivity via
$i=3k+2$ with $\lfloor i/3\rfloor=k$ ✓; the Cantor step ✓. This is the paper's principal no-go and
it survives audit intact.

**`thm:89` / `cor:injocc` — derivations reconstructed and correct.** $E_N\le\frac19\log_2N$ from
density-$\frac13$ distinct values; the $8/9$ then follows from $\max_{j<N}m_j\gtrsim3N$; and
$\#\{j<N:R_j>c\}\ll N^{1/9}$ follows since the $m_j$ are distinct integers below
$m_02^{-c}N^{1/9}$.

**`thm:GTC` uniqueness — not an error.** The paper calls $\gamma_*$ "the unique root of
$H(\gamma)=\gamma\log_23$" without Curry's interval $(1/2,1/\lambda)$. Checked: $H(\gamma)-\gamma\lambda$
is positive on $(0,\gamma_*)$ and negative on $(\gamma_*,1)$, so the root **is** unique on $(0,1)$
and dropping the interval is harmless. (The interval hypothesis is still needed inside Curry's
entropy step, which the paper does not reproduce.)

---

## C. The pattern worth recording

Three of the seven findings (2, 3, and the reviewer's `prop:occstop`) are the **same failure**: a
statement or figure that is right for $n\ge1$ but silently wrong at the initial index. Two more
(4, 5) are the **same failure** as the reviewer's Level-3/Level-4 finding: strictness asserted from
a non-implication of mechanism.

Both patterns share a cause worth naming: **the Lean statements carried the missing hypotheses in
every case, and the prose did not.** The formalization was not the weak point; the translation into
prose was. A useful discipline for Revision 8 would be to check each informal statement against the
Lean signature it claims to summarize, rather than the reverse.

---

## D. Verification performed

* All 42 theorem-class claims read; proofs checked where given (8 have `\begin{proof}`), and
  reconstructed where the paper asserts without proof.
* Every numerical constant recomputed at 40-digit precision; every computational diagnostic re-run
  independently (ranges stated above, all exhaustive over the stated range, none extrapolated).
* `prop:congruence` verified against a direct realizer search on 300 random words.
* Rebuilt: 27 pp, no undefined citations or references, **3 overfull boxes, all under 2.6pt** and
  all pre-existing (the 111.7pt table defect from the previous round remains fixed).
* Computational evidence is kept separate from proofs throughout, and no finite scan is used as
  evidence for a universally quantified claim.

**Not covered by this audit:** the companion-note results cited but not proved here
(`thm:periodic`, `thm:evperiodic`, `prop:bulkdefect`, `thm:launch`, `thm:rozier`,
`prop:inversion`, `prop:window`, `thm:band`), which are attributed to \cite{DJperiodic},
\cite{DJlaunch}, \cite{Rozier} and Revision 5 and would need their sources audited; and
`thm:GTC`/`prop:recip`, audited separately in `docs/CURRY_INDEPENDENT_AUDIT.md`.
