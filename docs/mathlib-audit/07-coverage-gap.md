# Code Context

## Files Retrieved
1. `YangMills/Mathematics/SumOpensMeasurableSpace.lean:7-36` - generic `OpensMeasurableSpace` instance on sums.
2. `YangMills/Mathematics/MeasurableEquivWithDensity.lean:7-39` - generic map/withDensity transport.
3. `YangMills/Mathematics/ManifoldBoundaryChartFrontier.lean:7-50` - chart boundary frontier lemma.
4. `YangMills/Mathematics/SchwartzDirectionalEvaluation.lean:7-55` - CLM directional jet evaluation.
5. `YangMills/Mathematics/SchwartzHausdorff.lean:7-59` - separation and named T1/T2 structures.
6. `YangMills/Mathematics/EuclideanHalfSpaceOutwardRay.lean:7-73` - Euclidean half-space ray predicate/theorem.
7. `YangMills/Mathematics/ObservationGeneratedMeasurableSpace.lean:7-109` - dependent generated measurable space.
8. `YangMills/Mathematics/FiniteProductRestriction.lean:7-117` - finite product marginal restriction.
9. `YangMills/Mathematics/WeakMeasureConvergence.lean:7-124` - bounded-continuous test carrier and weak convergence.
10. `YangMills/Mathematics/BoundaryConditionedProductDisintegration.lean:7-176` - application-specific disintegration structure.
11. `YangMills/Mathematics/SimultaneousConjugacyQuotient.lean:7-242` - diagonal conjugacy orbit quotient.
12. `YangMills/Mathematics/MixedPartialLieBracket.lean:7-151` - mixed-partial/Lie bracket calculus.

## Key Code
- `sumOpensMeasurableSpace` proves `borel_le` by Mathlib's `measurableSet_sum_iff` and `isOpen_sum_iff` (lines 21-34). This is a tiny general theorem/instance, not physical code.
- `MeasurableEquiv.map_withDensity_comp` (lines 20-34) reduces to existing `equiv.map_apply`, `equiv.restrict_map`, and `lintegral_map_equiv`; it is a missing convenience theorem, not new mathematics.
- Boundary result (lines 21-48) directly composes Mathlib's `I.isBoundaryPoint_iff_of_mem_atlas` with `I.isClosed_range`, `extend_target_subset_range`, and frontier definitions.
- Schwartz evaluation (lines 20-49) is a wrapper around `TemperedDistribution.delta` and `LineDeriv.iteratedLineDerivOpCLM`; the closure result is already CLM `.isClosed_ker`.
- Schwartz Hausdorff (lines 21-57) uses `WithSeminorms.T1_of_separating`; Mathlib has the exact separation theorem but intentionally does not export these named instances.
- Product restriction (lines 49-115) factors through Mathlib `measurePreserving_piEquivPiSubtypeProd`, `measurePreserving_fst`, and `measurePreserving_piCongrLeft`.
- Observation generation (lines 20-108) is a direct `iSup` of `MeasurableSpace.comap`, with standard lattice minimality proofs.
- Boundary-conditioned disintegration (lines 30-56 and 75-110) is a bespoke structure that stores exact all-boundary-value and product identities; Mathlib supplies only generic `IsCondKernel`/`disintegrate`, not this stronger application contract.
- Simultaneous quotient (lines 24-70) is the standard `MulAction.orbitRel` for a diagonal conjugation action; later quotient topology/Borel compatibility is project-specific packaging.

## Architecture
These files are isolated Mathematics infrastructure. Most are thin wrappers over pinned Mathlib APIs and are upstream candidates; the disintegration, Euclidean ray predicate, weak-convergence predicate, and simultaneous quotient encode application-facing choices and should not be presented as already-Mathlib facts. The pinned checkout evidence includes: `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:808` (`measurableSet_sum_iff`), `Mathlib/MeasureTheory/Constructions/Pi.lean:726` (`measurePreserving_piCongrLeft`), `Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean:314` (`isBoundaryPoint_iff_of_mem_atlas`), `Mathlib/Analysis/LocallyConvex/WithSeminorms.lean:356` (`T1_of_separating`), and `Mathlib/Analysis/Distribution/DerivNotation.lean:252-259` (`iteratedLineDerivOpCLM`). No exact duplicate declarations were found in pinned Mathlib; the overlap is constituent APIs, not proof-copy equivalence.

## Findings / conservative ranking
1. **A — `SumOpensMeasurableSpace.lean:21-34`.** General instance with exact constituent overlap above. Destination: Mathlib `MeasureTheory.MeasurableSpace.Constructions` (or topology/measurable sum file). Refactor to Mathlib naming and avoid project namespace. Small PR, 1 commit, first.
2. **A — `MeasurableEquivWithDensity.lean:20-34`.** Generic theorem and proof entirely existing API (`equiv.map_apply`, `restrict_map`, `lintegral_map_equiv`). Destination `Mathlib.MeasureTheory.Measure.WithDensity`; small PR, 1 commit.
3. **A — `SchwartzDirectionalEvaluation.lean:20-49`.** Generic Schwartz/tempered-distribution CLM theorem; exact APIs in `DerivNotation` and delta. Destination `Mathlib.Analysis.Distribution.SchwartzSpace.Deriv` or TemperedDistribution; small/medium PR due namespace/API review.
4. **A — `SchwartzHausdorff.lean:21-57`.** Generic separation theorem and T1/T2 construction, though named instances are deliberately local. Destination SchwartzSpace.Basic/Topology; small PR, likely requires Mathlib maintainers to decide global instances.
5. **A — `ManifoldBoundaryChartFrontier.lean:21-48`.** General manifold-with-corners theorem, direct use of pinned boundary theorem. Destination `Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`; medium PR (chart-frontier API and assumptions review).
6. **B — `FiniteProductRestriction.lean:49-115`.** General finite-index measure theorem, but implementation is long reindexing glue and assumes one common probability law. Destination `MeasureTheory.Constructions.Pi`; medium PR. Refactor to expose a generic `Measure.pi` marginal theorem and let this specialization be a corollary.
7. **B — `ObservationGeneratedMeasurableSpace.lean:20-108`.** Correct lattice construction, but dependent target family and generated-space naming/API need Mathlib design review. Destination `MeasureTheory.MeasurableSpace.Constructions`; medium PR.
8. **B — `MixedPartialLieBracket.lean:20-151`.** General calculus but likely specialized to the project’s vector-field carriers; first compare every theorem against `FDeriv.Symmetric` and `VectorField` before extraction. Destination calculus differential forms/vector fields; medium/large PR.
9. **B — `WeakMeasureConvergence.lean:20-124`.** The bounded-continuous carrier is reusable, but the predicate is a custom finite-measure convergence variant rather than Mathlib’s standard weak topology/measure convergence. Destination probably `Probability/Measure` or topology of measures; medium PR only after aligning with existing convergence API.
10. **C — `EuclideanHalfSpaceOutwardRay.lean:20-73`.** Exact Euclidean/model-with-corners geometry, but the named ray predicate and strict-time interval are application-specific. Keep project-local; refactor only after a generic tangent-cone API proposal. Small project refactor, not upstream PR.
11. **C — `BoundaryConditionedProductDisintegration.lean:30-176`.** Structure intentionally strengthens generic a.e. disintegration to every boundary and exact product restrictions. This is a source-facing contract, not Mathlib infrastructure. Keep local; do not upstream structure. Large PR would be inappropriate.
12. **C — `SimultaneousConjugacyQuotient.lean:24-242`.** `MulAction.orbitRel` is already Mathlib, but simultaneous conjugation, compact/Polish quotient assumptions, and Borel conclusions are application packaging. Keep local; at most upstream a generic diagonal action quotient lemma separately (large refactor).

## Similarly obvious omitted modules
`YangMills/Mathematics/SchwartzDirectionalPermutation.lean`, `SchwartzTensorProduct.lean`, `FiniteConfigurationSchwartzTensor.lean`, and `ContinuousBilinearWedge.lean` are also Mathlib-only/general-mathematics candidates, but they need theorem-by-theorem source comparison before ranking. They should be the next audit tranche; no claim of exact duplication is made here.

## Start Here
Open `SumOpensMeasurableSpace.lean` first: it is the smallest clear upstream candidate and establishes the exact pinned Mathlib sum-measurability APIs. Then inspect `MeasurableEquivWithDensity.lean` and `SchwartzDirectionalEvaluation.lean` for similarly low-risk PRs.

```acceptance-report
{
  "criteriaSatisfied": [{
    "id": "criterion-1",
    "status": "satisfied",
    "evidence": "12 requested modules were inspected, assigned conservative A/B/C severity, given exact project line ranges and pinned Mathlib overlap locations, destinations, and PR ordering."
  }],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {"command": "grep -R constituent theorem names .lake/packages/mathlib/Mathlib", "result": "passed", "summary": "Pinned source locations verified."},
    {"command": "wc -l requested modules", "result": "passed", "summary": "All requested modules located and scoped."}
  ],
  "validationOutput": ["Review-only audit; no source edits."],
  "residualRisks": ["No exact duplicate declarations were found by name; semantic upstream suitability still needs maintainer/API review, especially MixedPartialLieBracket and WeakMeasureConvergence."],
  "noStagedFiles": true,
  "diffSummary": "No diff; findings written to /tmp/luna-coverage-gap.md.",
  "reviewFindings": ["No blocker in project source; C-ranked application contracts should not be upstreamed as-is."],
  "manualNotes": "Pinned Mathlib revision was inspected under .lake/packages/mathlib/Mathlib; checker and probe paths were excluded."
}
```