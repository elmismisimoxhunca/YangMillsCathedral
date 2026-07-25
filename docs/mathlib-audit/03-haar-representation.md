# Code Context

## Files Retrieved
1. `YangMills/Mathematics/NormalizedCompactHaarMeasure.lean:17-100` — probability normalization and left/right/inversion invariance.
2. `YangMills/Mathematics/CompactRepresentationHaarAverage.lean:36-130` — averaged Hermitian pairing, invariance and positivity.
3. `YangMills/Mathematics/CompactRepresentationExplicitUnitarization.lean:62-176` — coordinate conjugation and matrix unitarization.
4. `YangMills/Mathematics/CompactHaarIntertwinerAverage.lean:37-82`, `CompactHaarSchurBridge.lean:32-100`, `CompactHaarSchurSelf.lean:32-80`, `CompactHaarSchurTrace.lean:32-90` — averaging-to-Schur chain.
5. `YangMills/Mathematics/CompactUnitaryMatrixCoefficientOrthogonality.lean:37-125`, `CompactUnitaryCharacterOrthogonality.lean:33-130` — coefficient and character orthogonality.
6. `YangMills/Mathematics/CompactMatrixFourierCoefficient.lean:25-110`, `CompactMatrixFourierConvolution.lean:30-100`, `CompactContinuousConvolution.lean:54-190` — Fourier/convolution wrappers.
7. `YangMills/Mathematics/CompactRepresentationCompleteReducibility.lean:65-140` and `CompactRepresentationUnitaryCoordinateRealization.lean:47-125` — finite-dimensional decomposition and representation wrappers.

## Key Code
The project repeatedly specializes to `G →* Matrix (Fin n) (Fin n) ℂ`, continuous maps, and a separately defined `normalizedCompactHaarMeasure`. The dependency chain is:
`NormalizedCompactHaarMeasure → CompactRepresentationHaarAverage → ExplicitUnitarization → HaarIntertwinerAverage → SchurBridge/Self/Trace → MatrixCoefficientOrthogonality → CharacterOrthogonality/Fourier extraction → finite coefficient spaces/density`.

Mathlib overlap confirmed directly against the pinned tree:
- `Mathlib.MeasureTheory.Group.Measure` (`IsHaarMeasure`, `IsHaarMeasure.smul`, `map_mul_left_eq_self`, `isHaarMeasure_eq_of_isProbabilityMeasure`) already supplies the abstract Haar API used by the normalization wrapper.
- `Mathlib.Analysis.Convolution` defines generic `MeasureTheory.convolution`, `ConvolutionExists`, and continuity theorems (`Continuous.convolution_integrand_fst`, `HasCompactSupport.continuous_convolution_right/left`, lines 401 onward and 601-691). Project `CompactContinuousConvolution` is a bounded compact-probability specialization, not missing basic convolution.
- `Mathlib.RepresentationTheory.Irreducible` already supplies `Representation.IsIrreducible.bijective_or_eq_zero`, explicitly consumed by `CompactHaarSchurBridge`.
- `Mathlib.RepresentationTheory.FDRep` (notably around lines 25 and 159) has categorical finite-dimensional Schur lemma/Hom dimension material. It does not provide the analytic compact-Haar averaging or compact-group Peter–Weyl result.
- `Mathlib.RepresentationTheory.Character` documents finite-group character orthogonality, while `Analysis.Fourier.FiniteAbelian.Orthogonality` is finite abelian. No compact topological-group Haar matrix-coefficient orthogonality/Peter–Weyl API was found.

## Architecture / ranked findings

### C — wrappers, assumptions, or duplicates (do not upstream as-is)
- `NormalizedCompactHaarMeasure.lean`: Mathlib already models Haar measures and normalization invariance. Keep a project-local convenience definition only if its exact probability convention is needed; otherwise refactor callers to a `Measure μ` plus `[IsProbabilityMeasure μ] [Measure.IsHaarMeasure μ]`. The current proof assumes `BorelSpace`, `CompactSpace`, etc. that should be inferred or minimized.
- `CompactContinuousConvolution.lean`, `CompactMatrixFourierCoefficient.lean`, and all `...Apply/Add/Smul` lemmas: direct wrappers around Mathlib integral/convolution API. Upstream only if reformulated for arbitrary locally compact groups, Radon/Haar measures, topological vector spaces and continuous bilinear maps; current `C(G,ℂ)`/matrix-only API is unlikely accepted.
- `MatrixRepresentationCharacter.lean`: project bridge from `Representation` to matrices/traces; useful locally, but finite-index matrix conventions and `Matrix.trace` are not a Mathlib gap.
- `CompactRepresentationAveragedInnerProductCore/Topology/NormedRealization/AveragedOrthonormalCoordinates`: substantial proof but coordinate `Fin n → ℂ` and custom topology are implementation scaffolding. Mathlib maintainers would expect arbitrary finite-dimensional normed/inner-product spaces, not a bespoke averaged topology.
- `CompactRepresentationCompleteReducibility.lean` and `SimpleSummandCoordinates.lean`: duplicate/use of existing semisimple representation infrastructure plus project decomposition bookkeeping; not a compact-group theorem in this form.
- finite coefficient/character subspace, finite Plancherel, density and approximation sequence files: downstream wrappers/conditional records, often requiring supplied “faithful” selected dual data; not unconditional reusable theorems and not upstreamable under current assumptions.

### B — real reusable candidates after substantial generalization
1. **Compact Haar averaging of finite-dimensional representations** (`CompactRepresentationHaarAverage.lean:41-130`): theorem that averaging an inner product over a compact group yields invariant positive-definite Hermitian form. This is genuinely reusable and absent in pinned Mathlib, but upstream as `V` finite-dimensional over `ℝ/ℂ`, continuous representation into `Module.End`, compact group with canonical Haar measure, and `ContinuousMap`/Bochner hypotheses. Avoid coordinate matrices and avoid installing a global instance; return a bundled sesquilinear form plus positivity.
2. **Haar averaging of an intertwiner** (`CompactHaarIntertwinerAverage.lean:37-82`): compact-group averaging projection onto intertwiners is reusable. Generalize to continuous finite-dimensional representations and a continuous linear map; state equivariance and integrability abstractly. This should precede Schur applications.
3. **Compact-group Schur orthogonality** (`CompactUnitaryMatrixCoefficientOrthogonality.lean:88-125`, character file): genuinely missing broad analytic theorem. Upstream in a new compact-representation/Peter-Weyl module, with two irreducible finite-dimensional unitary representations, Haar probability, and inner products; derive coefficient integral `δ` with explicit dimension factor and character pairing. Do not encode only `Fin n` matrices.
4. **Compact Peter–Weyl density/completeness** (project `CompactMatrixGroupCoefficientDensity`, `CompactMatrixGroupL2CoefficientCompleteness`, selected-dual files): genuinely missing from Mathlib, but much larger than a lemma. Needs locally compact compact-group hypotheses, second countability/separability, all irreducible unitary representations (not a caller-supplied faithful finite family), `L²` Hilbert-space direct sum, and a precise topology/density statement.

### A — highest-priority upstream infrastructure
- The averaging theorem and abstract intertwiner projection are the best first PR: mathematically standard, independently useful, and currently absent. A should mean “strong candidate once generalized,” not current code.
- Full compact Peter–Weyl (density, coefficient orthogonality, Plancherel) is A in importance but likely multiple PRs; maintainers will reject a project-specific finite selected dual or matrix-only statement.

## Refactor and PR sequencing
1. Refactor local users to Mathlib Haar classes and generic `Measure μ`; retain normalized measure as a thin local alias. Delete/relegate duplicate continuity/additivity wrappers where `convolution` and integral lemmas suffice.
2. Extract abstract finite-dimensional representation averaging (positive invariant sesquilinear form), with hostile tests for trivial/nontrivial and zero-dimensional carriers.
3. Extract abstract Haar intertwiner averaging/projection, then connect to existing `Representation.IsIrreducible`/`FDRep` Schur APIs.
4. Add compact unitary coefficient and character orthogonality, with explicit convention tests (`ρ(g⁻¹)` versus `ρ(g)`, transpose/conjugation, dimension weight).
5. Only then pursue Peter–Weyl density/Plancherel under second countability; keep centralization, faithful-family approximation, heat kernels and project acceptance bridges downstream/local.

## Maintainer/API objections and residual risks
- Compactness alone does not supply the intended measurable/Borel compatibility in every abstraction; use standard topological-group/Haar assumptions and avoid duplicated `BorelSpace` fields where instances suffice.
- “Finite-dimensional representation” must be a genuine continuous linear representation, not merely a monoid hom into matrices; matrix `Fin n` APIs are too narrow.
- Character orthogonality requires irreducibility and unitarity (or an explicitly constructed invariant inner product); project files sometimes make these class assumptions and sometimes carry conditional data.
- Peter–Weyl requires the correct separability/second-countability hypotheses and quantification over all irreducibles; supplied faithful finite lists are not equivalent.
- No source files were edited; checker closure/probes were intentionally excluded.

```acceptance-report
{
  "criteriaSatisfied": [{"id":"criterion-1","status":"satisfied","evidence":"Concrete ranked findings cite exact project files/declaration ranges and pinned Mathlib files/API searches; overlap, dependency, sequencing, and residual risks are recorded above."}],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {"command":"grep project Mathematics declarations/imports","result":"passed","summary":"Mapped compact Haar, representation, Schur, convolution, coefficient and character declarations."},
    {"command":"grep pinned .lake/packages/mathlib for Haar/convolution/Schur/character APIs","result":"passed","summary":"Confirmed existing Haar, convolution and algebraic Schur APIs; no compact Haar Peter-Weyl API found."}
  ],
  "validationOutput": ["Read-only audit completed; no edits or build required."],
  "residualRisks": ["Compact Peter-Weyl scope and exact second-countability API require a future detailed design review."],
  "noStagedFiles": true,
  "diffSummary": "No diff; read-only review.",
  "reviewFindings": ["B: CompactRepresentationHaarAverage and CompactHaarIntertwinerAverage are genuine candidates only after abstract generalization.", "A: Compact Haar coefficient orthogonality/Peter-Weyl are missing Mathlib infrastructure but current project statements are too specialized.", "C: normalized Haar, convolution, matrix character and finite selected-dual files are wrappers or conditional downstream infrastructure."],
  "manualNotes": "Start with abstract averaging, then intertwiner projection, then orthogonality, then Peter-Weyl; do not upstream project wrappers verbatim."
}
```