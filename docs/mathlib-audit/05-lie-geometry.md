# Code Context

## Files Retrieved
1. `YangMills/Geometry/LieGroup.lean` (lines 20-145) - compact-simple certificate and tangent Lie-algebra predicates.
2. `YangMills/Geometry/PrincipalBundleTorsor.lean` (lines 10-105) - bespoke algebraic torsor family.
3. `YangMills/Geometry/TopologicalPrincipalBundle.lean` (lines 20-155) - local-homeomorphism atlas and quotient/open-map derivations.
4. `YangMills/Geometry/SmoothPrincipalBundle.lean` (lines 20-150) - smooth atlas data and transition theorem.
5. `YangMills/Geometry/PointwisePrincipalConnection.lean` (lines 35-170) - connection one-form semantics.
6. `YangMills/Geometry/PrincipalCurvature.lean` (lines 35-125) - curvature formula from certified exterior derivative.
7. `YangMills/Mathematics/ManifoldDifferentialForms.lean` (lines 20-100) - pointwise alternating-map forms and pullback.
8. `YangMills/Mathematics/SmoothManifoldDifferentialForms.lean` (lines 20-125) - evaluation-tested smoothness carrier.
9. `YangMills/Geometry/AdjointBundleDifferentialForm.lean` (lines 45-190) - dependent adjoint-fiber form carrier.

## Key Code
- `HasSimpleGroupLieAlgebra` is a thin Prop wrapper around Mathlib `LieAlgebra.IsSimple ℝ (GroupLieAlgebra ...)`, locally installing finite-dimensional completeness and `minSmoothness` (LieGroup.lean:28-53). The resulting `CompactSimpleGaugeGroupData` adds compactness, connectedness and nontriviality (lines 87-107).
- `PrincipalBundleTorsorData` stores projection/action and fiberwise unique transitivity (PrincipalBundleTorsor.lean:20-41). `TopologicalPrincipalBundleData` then stores an atlas of `OpenPartialHomeomorph`s and proves projection open/quotient (TopologicalPrincipalBundle.lean:34-65, 84-155). `SmoothPrincipalBundleData` adds smoothness-on-source/target (SmoothPrincipalBundle.lean:39-64).
- `ManifoldDifferentialForm` is `(x : M) → ContinuousAlternatingMap ℝ (TangentSpace I x) V (Fin k)` with `pullback` via `mfderiv` (ManifoldDifferentialForms.lean:27-50). `IsSmooth` tests all locally smooth tangent fields after an explicit continuous-linear value coordinate (SmoothManifoldDifferentialForms.lean:34-58).
- `PointwisePrincipalConnectionData` requires vertical normalization and right equivariance; `PrincipalConnectionData` adds `form_smooth` (PointwisePrincipalConnection.lean:96-153). Curvature is derived as `dΘ + 1/2 [Θ∧Θ]` (PrincipalCurvature.lean:67-96).

## Architecture
The geometry layer is a large bespoke certificate stack: algebraic torsor → topological atlas → smooth atlas → pointwise/smooth connection → certified exterior derivative → curvature → associated adjoint dependent fibers/forms. Mathlib supplies manifold charts, `TangentSpace`, `mfderiv`, `ContMDiff`, `OpenPartialHomeomorph`, `FiberBundle`/`VectorBundle`, `Bundle.Trivialization`, `ContinuousAlternatingMap`, and `GroupLieAlgebra`, but does not appear to provide a ready-made principal-bundle/connection/curvature package. Consequently, the local wrappers are mostly project semantics rather than direct replacements.

## Findings (ranked)

### A — suitable upstream candidates (small, general, low semantic risk)
1. **`YangMills/Mathematics/ManifoldDifferentialForms.lean:27-50, 58-85`** — generic pointwise manifold form abbreviation, pullback through `mfderiv`, `evalOne`, and repeated-vector vanishing. Mathlib overlap: `ContinuousAlternatingMap`, `TangentSpace`, `mfderiv`; no obvious canonical pointwise V-valued form carrier in pinned APIs. Dependency closure is only manifold derivative + alternating maps. Destination: `Mathlib/Geometry/Manifold/DifferentialForm` (or Analysis/Normed/Module if split). Refactor difficulty low/medium: replace project namespace/docs and add conventional notation; avoid project-specific smoothness.
2. **`YangMills/Mathematics/SmoothManifoldDifferentialForms.lean:34-58, 83-112`** — coordinate-independent (up to CL-equivalence) local evaluation smoothness predicate and bundled smooth form. Mathlib overlap: `ContMDiffMFDeriv`, `ContMDiffSection`; likely reusable if API is carefully generalized. Destination: Mathlib manifold differential-form module. Difficulty medium: settle whether smoothness should be section-based rather than this field-test definition, and prove equivalence.
3. **`YangMills/Geometry/LieGroup.lean:28-82, 115-145`** — helper predicates/lemmas bridging finite-dimensional `LieGroup` to `GroupLieAlgebra` and simple→semisimple/no proper ideal. Mathlib overlap is direct (`GroupLieAlgebra`, `LieAlgebra.IsSimple`); only the local instance plumbing is repetitive. Destination: Mathlib `Geometry/Manifold/GroupLieAlgebra` companion. Difficulty low, but `HasSimpleGroupLieAlgebra` naming and compact-simple domain-specific certificate should remain project-side.

### B — potentially upstreamable infrastructure, but currently too policy/bundle-specific
4. **`YangMills/Geometry/TopologicalPrincipalBundle.lean:20-65, 84-155`** — generic equivariant local-trivialization structure and derived open/quotient projection. Mathlib overlap: `FiberBundle.Basic`, `OpenPartialHomeomorph`, `Bundle.Trivialization`; no obvious principal-bundle class. The derived open/quotient theorem is general and useful, but depends on the bespoke `PrincipalBundleTorsorData` and selected-chart function. Destination could be Mathlib `Topology/FiberBundle/Principal`; difficulty high: redesign around existing `FiberBundle`/local trivializations, atlas coverage, and typeclass conventions.
5. **`YangMills/Geometry/SmoothPrincipalBundle.lean:39-64, 112-145`** — smooth local trivializations and transition smoothness. Mathlib overlap: `ContMDiffOn`, `Bundle.Trivialization`, vector-bundle smooth infrastructure. Destination `Geometry/Manifold/VectorBundle` extension only after a principal-bundle abstraction exists. Difficulty high; current chart source/target and model-corner parameterization are not standard Mathlib API.
6. **`YangMills/Geometry/PointwisePrincipalConnection.lean:96-153`** — vertical normalization/right equivariance is mathematically standard (Freed 1.9–1.10), but the implementation uses bespoke principal action and `GroupLieAlgebra` plus custom form smoothness. Destination future Mathlib principal connection module, not immediate upstream. Difficulty very high; requires principal bundle and tangent-action foundations.

### C — retain project-side / missing-foundation risk
7. **`YangMills/Geometry/PrincipalCurvature.lean:51-125`** — curvature depends on a project `PrincipalConnectionExteriorDerivativeData` certificate and bespoke Lie-bracket wedge operations. Mathlib overlap is only low-level alternating-map operations; no general exterior derivative of manifold-valued forms is available in the needed form. Large missing foundation (exterior algebra, smooth sections, derivative uniqueness, naturality). Do not upstream now.
8. **`YangMills/Geometry/AdjointBundleDifferentialForm.lean:45-190`** — dependent quotient-fiber algebra/topology and coordinate CL-equivalences are highly bespoke. Mathlib overlap: `Bundle.TotalSpace`, `FiberBundle`, `VectorBundle`, `ContinuousAlternatingMap`; however the quotient orbit fiber and per-fiber installed instances are project semantics. Large closure through `AdjointBundle*`, dependent topology, transitions, and chart smoothness. Retain project-side until a genuine associated-bundle API exists.
9. **`YangMills/Geometry/PrincipalBundleTorsor.lean:20-105`** — useful semantic record but duplicates the conceptual role of a principal bundle without Mathlib typeclass integration. Upstreaming it as-is would create a parallel API. Refactor risk is high because every downstream geometry file depends on stored `rightAction` rather than `MulAction`/`IsFree`/`IsPretransitive`; retain as acceptance-contract carrier.

## Bespoke parallel APIs / risks
- `PrincipalBundleTorsorData`, `TopologicalPrincipalBundleData`, and `SmoothPrincipalBundleData` form a parallel principal-bundle hierarchy beside Mathlib `FiberBundle`/`VectorBundle`; they should not be presented as drop-in Mathlib replacements.
- `ManifoldDifferentialForm.IsSmooth` is an explicit project predicate, not proof that Mathlib's `ContMDiffSection` interface is equivalent. The coordinate equivalence requirement is a real abstraction cost.
- Curvature/exterior derivative are certificate-driven placeholders, not general differential geometry. Any upstream proposal must not carry `PrincipalConnectionExteriorDerivativeData` as an arbitrary witness.
- Compact-connected-simple is project convention: `connected` and `nontrivial` are explicit and Lie-algebra simplicity does not establish them.

## Sequencing
1. First upstream/generalize standalone pointwise form + small `evalTwo_same`/pullback lemmas (A1).
2. Resolve Mathlib smooth-form section API and prove/replace evaluation smoothness (A2).
3. Upstream only LieGroup helper plumbing (A3), keeping compact-simple certificate local.
4. Before any principal-bundle PR, design against `FiberBundle.Basic`/`Bundle.Trivialization` and eliminate parallel torsor storage (B4–B5).
5. Connections, exterior derivatives, associated bundles, and curvature remain blocked on that foundation (B6/C7–C9).

## Start Here
Open `YangMills/Mathematics/ManifoldDifferentialForms.lean` first: it has the smallest dependency closure and the clearest Mathlib-overlap candidate. Then inspect `SmoothManifoldDifferentialForms.lean` to decide whether its smoothness predicate can be reconciled with existing `ContMDiffSection` APIs.

## Residual risks
The audit did not inspect checker-copied modules or probes. Mathlib API names and exact upstream module destinations should be rechecked against the pinned revision before proposing a PR; in particular, absence of a ready-made principal-bundle and full exterior-derivative API is a high-impact assumption. No files in the repository were edited.

```acceptance-report
{
  "criteriaSatisfied": [{"id":"criterion-1","status":"satisfied","evidence":"Concrete A/B/C findings with exact files, declaration ranges, Mathlib overlap, dependencies, destinations, difficulty, risks, and sequencing are recorded above."}],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [],
  "validationOutput": ["Read-only audit; no build needed and no source files changed."],
  "residualRisks": ["Pinned Mathlib principal-bundle/exterior-derivative API availability should be verified before upstream design."],
  "noStagedFiles": true,
  "diffSummary": "No changes; findings written to /tmp/luna-lie-geometry.md.",
  "reviewFindings": ["C: bespoke torsor/principal hierarchy parallels Mathlib FiberBundle and should not be upstreamed unchanged.", "C: curvature relies on certificate-driven missing exterior-derivative foundation."],
  "manualNotes": "Probes and checker-copied modules were excluded as requested."
}
```