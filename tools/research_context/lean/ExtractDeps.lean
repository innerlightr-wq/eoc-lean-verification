/-
Declaration-level dependency extraction for the EOC library.

Method follows Aksenov, Bodnia, Freedman and Mulligan, "Compression is all you
need: Modeling Mathematics", arXiv:2603.20396 (2026), CC BY 4.0,
§"Constructing the dependency graph": traverse each declaration's signature
(type) and body (value), collect every `.const` node with multiplicity, and
treat `.sort` as a reference to a synthetic primitive `Sort`.

Two deviations, both deliberate and recorded in docs/AKSENOV_METHOD_NOTES.md:

* signature and body reference counts are kept SEPARATE, because the paper's
  compression measures `T_0` and `I_0` need `|S|` and `|B|` apart;
* we emit the whole dependency CLOSURE reachable from `EOC.*`, not only the
  EOC declarations, so that View A (expansion descending into Mathlib) is a
  real measurement rather than a relabelling of View B.

Wrapped length is NOT computed here. The paper uses the Lean parser's token
count; we approximate it in Python over the declaration's source range and
label it `wrapped_tokens_approx` throughout.

Output: newline-delimited JSON on stdout, one object per declaration.

    lake env lean tools/research_context/lean/ExtractDeps.lean \
      > research-index/raw_decls.jsonl
-/
-- BEGIN GENERATED IMPORTS -- python3 -m tools.research_context imports
-- Every Lean module physically present under EOC/ is imported below, so the
-- extractor sees the whole library regardless of what `EOC.lean` imports. In
-- the MVP round EOC.CurryFoundation and EOC.ZCRERealizerGrowth were silently
-- absent from the closure for exactly that reason: a module is missing from
-- EOC.lean precisely when it is new, which is when it matters most.
import EOC.ArithmeticFrontier
import EOC.AverageOddDark
import EOC.Basic
import EOC.BinomialEntropy
import EOC.BlockCube
import EOC.BlockCubeInstance
import EOC.BoundedDrift
import EOC.BoundedDriftCore
import EOC.CapacityBounds
import EOC.Carry
import EOC.ChangHistory
import EOC.ChordRotation
import EOC.CompositionCounting
import EOC.Confinement
import EOC.CurryFoundation
import EOC.DangerousWindows
import EOC.DecayInterface
import EOC.DirectDescent
import EOC.EntropyBounds
import EOC.ExceptionalPowerBound
import EOC.FinitePrefixPacking
import EOC.FiniteValuationWord
import EOC.FirstDivergence
import EOC.GoodAngles
import EOC.HarmonicFloor
import EOC.HarmonicPacking
import EOC.IntervalSieve
import EOC.LiftDigits
import EOC.LiftGap
import EOC.LocalWindow
import EOC.LogAbsorb
import EOC.LogCorridor
import EOC.MaxTriangle
import EOC.OddBlack
import EOC.PairValuation
import EOC.Periodic
import EOC.PeriodicCore
import EOC.PowerOrbit
import EOC.PrefixCollision
import EOC.PrefixStateFormula
import EOC.PrefixSuffixBilinear
import EOC.PrescribedMatching
import EOC.PressureBridge
import EOC.PsiShellBound
import EOC.PsiSieve
import EOC.Realizer
import EOC.RealizerLift
import EOC.RenyiBarrier
import EOC.RenyiInstance
import EOC.ResidueDiscrepancy
import EOC.ShapeBridge
import EOC.ShapeCertificate
import EOC.ShapeTail
import EOC.ShapeUnconditional
import EOC.ShellDecomposition
import EOC.ShellRefined
import EOC.ShellWeyl
import EOC.ShellwiseChain
import EOC.SignedBlock
import EOC.SignedRealizer
import EOC.SpacingChain
import EOC.SplitPrefix
import EOC.SuffixTransport
import EOC.SurvivorClusters
import EOC.SurvivorCounting
import EOC.SurvivorDensity
import EOC.SwapBound
import EOC.SwapCollatz
import EOC.TaoLike.AllShiftsAveragedPersistence
import EOC.TaoLike.ConditionalMixing
import EOC.TaoLike.Cylinder
import EOC.TaoLike.CylinderAppend
import EOC.TaoLike.CylinderDigitCounting
import EOC.TaoLike.EarlyLate
import EOC.TaoLike.HarmonicAP
import EOC.TaoLike.HarmonicExceptionalSetSummability
import EOC.TaoLike.LateShiftPersistence
import EOC.TaoLike.NormalizedHarmonicLaw
import EOC.TaoLike.PersistenceModel
import EOC.TaoLike.PersistenceRateCramer
import EOC.TaoLike.PrefixPartition
import EOC.TaoLike.ResidueTV
import EOC.TaoLike.RestartLawAlignment
import EOC.TaoLike.ShiftedPersistence
import EOC.TaoLike.TaoInterface
import EOC.ThreeBlock
import EOC.TransportCollapse
import EOC.TriangleArray
import EOC.TriangleHop
import EOC.TwistExpansion
import EOC.UpperCertificates
import EOC.UpperEscape
import EOC.ValuationWord
import EOC.WeightedChain
import EOC.WhiteContraction
import EOC.WhiteRun
import EOC.ZCRERealizerGrowth
-- END GENERATED IMPORTS
import Lean

open Lean

namespace EOCResearchIndex

/-- Reference multiset of an expression: every `.const` occurrence, with
`.sort` folded into a synthetic `Sort` primitive. Mirrors `collectElems` of
arXiv:2603.20396 §"Constructing the dependency graph". -/
partial def collectElems (e : Expr) (acc : NameMap Nat) : NameMap Nat :=
  match e with
  | .const declName _ => acc.insert declName ((acc.find? declName).getD 0 + 1)
  | .app fn arg => collectElems arg (collectElems fn acc)
  | .lam _ bt body _ => collectElems body (collectElems bt acc)
  | .forallE _ bt body _ => collectElems body (collectElems bt acc)
  | .letE _ t v b _ => collectElems b (collectElems v (collectElems t acc))
  | .mdata _ e' => collectElems e' acc
  | .proj _ _ s => collectElems s acc
  | .sort _ => acc.insert `Sort ((acc.find? `Sort).getD 0 + 1)
  | _ => acc

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def nameMapToJson (m : NameMap Nat) : Json :=
  Json.mkObj (m.toList.map fun (n, c) => (n.toString, Json.num (JsonNumber.fromNat c)))

/-- Lean-generated rather than human-written. Aksenov et al. omit such elements
when reporting wrapped lengths; we flag rather than drop, so the consumer can
choose and the omission stays auditable. -/
def isGenerated (n : Name) : Bool :=
  let s := n.toString
  n.isInternal
    || (s.splitOn "._").length > 1
    || (s.splitOn ".proof_").length > 1
    || (s.splitOn ".eq_").length > 1
    || (s.splitOn ".match_").length > 1
    || (s.splitOn ".brecOn").length > 1
    || (s.splitOn ".noConfusion").length > 1
    || (s.splitOn ".inj").length > 1
    || (s.splitOn ".sizeOf_spec").length > 1

end EOCResearchIndex

open EOCResearchIndex in
#eval show CoreM Unit from do
  let env ← getEnv
  -- 1. seeds: every declaration whose module is in this repository's EOC library
  let mut seeds : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if (`EOC).isPrefixOf env.header.moduleNames[idx.toNat]! then
        seeds := seeds.push n
  -- 2. BFS the reachable closure (EOC seeds plus everything they reference)
  let mut seen : NameSet := {}
  let mut work : Array Name := seeds
  for n in seeds do seen := seen.insert n
  let mut emitted : Nat := 0
  while h : work.size > 0 do
    let n := work[work.size - 1]
    work := work.pop
    let some ci := env.find? n | continue
    let sigDeps := collectElems ci.type {}
    let bodyDeps := match ci.value? with
      | some v => collectElems v {}
      | none => {}
    let modName : String := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "«core»"
    let isEOC := modName.startsWith "EOC"
    -- only EOC declarations get source ranges; Mathlib ranges are not needed
    let (sl, el) ← if isEOC then do
        match ← findDeclarationRanges? n with
        | some r => pure (r.range.pos.line, r.range.endPos.line)
        | none => pure (0, 0)
      else pure (0, 0)
    let obj := Json.mkObj [
      ("name", Json.str n.toString),
      ("module", Json.str modName),
      ("eoc", Json.bool isEOC),
      ("kind", Json.str (kindOf ci)),
      ("generated", Json.bool (isGenerated n)),
      ("has_body", Json.bool ci.value?.isSome),
      ("sig_deps", nameMapToJson sigDeps),
      ("body_deps", nameMapToJson bodyDeps),
      ("start_line", Json.num (JsonNumber.fromNat sl)),
      ("end_line", Json.num (JsonNumber.fromNat el))
    ]
    IO.println obj.compress
    emitted := emitted + 1
    for (d, _) in sigDeps.toList ++ bodyDeps.toList do
      unless seen.contains d do
        seen := seen.insert d
        work := work.push d
  IO.eprintln s!"[ExtractDeps] EOC seeds: {seeds.size}, closure emitted: {emitted}"
