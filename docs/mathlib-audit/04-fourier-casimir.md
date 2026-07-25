# Code Context

## Files Retrieved
1. `YangMills/Mathematics/CompactMatrixFourierCoefficient.lean` (lines 21-150) — coordinatewise matrix Fourier coefficient, integrability, trace/add/smul/zero laws.
2. `YangMills/Mathematics/UnitaryMatrixDualL2Span.lean` (lines 25-130) — actual Mathlib `Lp ℂ 2` carrier, synthesis inner-product bridge, conditional Peter–Weyl target.
3. `YangMills/Mathematics/CompactMatrixGroupL2CoefficientCompleteness.lean` (lines 20-80) — dense-range consequences under faithful selected-dual hypothesis.
4. `YangMills/Mathematics/UnitaryMatrixDualCasimirHeatCharacterSeries.lean` (lines 35-210) — supplied weights/summability and unconditional uniformly convergent character series.
5. `YangMills/Mathematics/SmoothUnitaryMatrixCoefficientCasimirLaplacianBridge.lean` (lines 35-165) — explicit conditional coefficientwise Casimir/Laplacian bridge and finite-synthesis consequences.
6. `YangMills/Mathematics/UnitaryMatrixDualCasimirHeatDerivativeSeries.lean` (lines 45-180), `UnitaryMatrixDualCasimirHeatEquation.lean` (declarations surfaced by grep, 20-130), and `UnitaryMatrixDualCasimirHeatInitialIdentity.lean` (lines 35-85) — derivative/heat equation/initial-limit layers.
7. `YangMills/Mathematics/UnitaryMatrixDualCasimirHeatConvolutionSemigroup.lean` (lines 35-90), `UnitaryMatrixDualCasimirHeatPositivity.lean` (lines 35-190) — conditional convolution/positivity layers.

## Key Code
- `matrixFourierCoefficient` is literally `fun row column => ∫ g, f g * ρ (g⁻¹) row column ∂μ` (`CompactMatrixFourierCoefficient.lean:38-45`). `integrable_matrixFourierCoefficient_integrand` (`:56-72`) is a compact-domain continuous-integrand argument. `matrixFourierCoefficient_trace` (`:74-90`) follows finite-sum/integral interchange; add/smul/zero are `:93-133`.
- `unitaryMatrixDualL2CoefficientSynthesis` (`UnitaryMatrixDualL2Span.lean:53-63`) maps finite-support coefficients through `ContinuousMap.toLp`; `unitaryMatrixDualL2CoefficientSynthesis_inner` (`:66-83`) proves the L2 inner product equals the project's algebraic Fourier pairing. `HasL2PeterWeylCompleteness` (`:100-106`) is only `closedSpan = ⊤`; no unrestricted Peter–Weyl theorem is assumed.
- `unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful` (`CompactMatrixGroupL2CoefficientCompleteness.lean:39-46`) depends on `unitaryMatrixDual_hasL2PeterWeylCompleteness_of_faithful`, i.e. selected-dual density is a bridge assumption/theorem upstream of this file. Approximation and coefficient-test separation (`:48-80`) are ordinary Hilbert-space consequences.
- `UnitaryMatrixDualHeatTraceSummabilityData` (`UnitaryMatrixDualCasimirHeatCharacterSeries.lean:45-56`) supplies nonnegative `casimirWeight` and summability of `dim(q)^2 exp(-(t/2)c_q)`. Everything through uniform character-series convergence (`:145-200`) is proved from this premise. `countable_unitaryMatrixDual_of_heatTraceSummability` (`:97-112`) is a useful small standalone consequence.
- `SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData` (`Smooth...Bridge.lean:40-56`) stores, rather than proves, the coefficientwise Laplacian eigen-equation. Its real/imaginary transport (`:72-107`), eigenvalue uniqueness at identity (`:109-135`), and finite-synthesis linearity (`:137-165`) are proved but remain conditional.

## Architecture
The modules form: coordinate Fourier primitives → finite algebraic synthesis → Mathlib `Lp` and closed span → selected-dual/faithful density bridge → (separately) supplied Casimir weights and uniformly convergent character series → supplied smooth Casimir/Laplacian bridge → derivative, convolution, positivity, heat-equation and initial-identity records. Mathlib already supplies the generic `Lp`, inner-product, topological closure, `Summable`/`tsum`, finite-sum integration, and derivative/interchange machinery used here; the project-specific representation indexing, Haar normalization, selected dual, Casimir semantics, and Peter–Weyl/heat identification are not Mathlib facts.

## Audit and ranking
### A — strongest upstream candidates (small, unconditional, broadly reusable)
- `integrable_matrixFourierCoefficient_integrand` (`CompactMatrixFourierCoefficient.lean:56-72`): generic compact-space continuous scalar/matrix coordinate integrability. The exact proof is Mathlib API composition and could be generalized to any finite-dimensional continuous representation/integrand; destination likely `Mathlib.MeasureTheory.Function.LocallyIntegrable` or compact-group Fourier file. Refactor cost low (remove project Haar imports, generalize matrix representation assumptions).
- `matrixFourierCoefficient_trace` (`:74-90`) and add/smul/zero (`:93-133`): elementary finite-coordinate integral identities. No Peter–Weyl dependency. Destination a future `Mathlib/Analysis/Fourier/Compact` namespace; low cost, but matrix convention and integrability assumptions should be API-designed first.
- `unitaryMatrixDualL2CoefficientSynthesis_inner` (`UnitaryMatrixDualL2Span.lean:66-83`): a valid finite-synthesis `toLp` inner-product computation, but currently tied to project coefficient space. Upstream only after replacing `UnitaryMatrixDualCoefficientSpace` with a generic finite index/finsupp family; medium refactor cost.
- `unitaryMatrixDualL2CoefficientSynthesis_norm_sub_lt_of_faithful` (`CompactMatrixGroupL2CoefficientCompleteness.lean:48-56`) and coefficient-test uniqueness (`:58-80`): generic dense-range Hilbert consequences, but existing Mathlib likely already has equivalent `DenseRange.exists_dist`, continuous equalizer, and `inner_self_eq_zero`; upstream value is mainly as a compact theorem pattern, low value/low cost.

### B — useful conditional bridges (not standalone upstream mathematics)
- `unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful` (`CompactMatrixGroupL2CoefficientCompleteness.lean:39-46`): depends on selected-dual density and faithful finite matrix representation. Must not be advertised as unconditional Peter–Weyl. Destination stays project bridge or a Mathlib theorem only once assumptions match a canonical compact-group dual API; high refactor cost.
- `HasL2PeterWeylCompleteness` and `unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense` (`UnitaryMatrixDualL2Span.lean:100-113`): exact carrier/specification and closure equivalence are clean, but the selected dual is project-defined and no inhabitant is constructed. Keep project-side unless Mathlib develops a representation-theoretic dual interface.
- `UnitaryMatrixDualHeatTraceSummabilityData` plus `countable_unitaryMatrixDual_of_heatTraceSummability` (`UnitaryMatrixDualCasimirHeatCharacterSeries.lean:45-56,97-112`): summability ⇒ countability is unconditional *relative to supplied data*; the data itself is a requirement, not theorem. Countability lemma could upstream generically as “summable strictly-positive family has countable index”, low/medium cost; full structure cannot.
- Uniform character series and analysis (`:145-210`): mathematically sound Weierstrass/tsum consequences, but custom character and selected dual. Medium refactor; candidate only after generic indexed bounded-function theorem extraction.
- `SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData` and `laplacian_smoothCoefficient` (`Smooth...Bridge.lean:40-70`): explicitly conditional bridge. `laplacian_smoothRealCoefficient`, identity uniqueness, and finite synthesis (`:72-165`) are proved deductions and potentially reusable once generic smooth coefficient/Laplacian APIs exist. Medium/high refactor; do not upstream the record as a theorem.

### C — freeze / research-dependent
- `UnitaryMatrixDualCasimirHeatDerivativeSeries`, `UnitaryMatrixDualCasimirHeatEquation`, `UnitaryMatrixDualCasimirHeatConvolutionSemigroup`, `UnitaryMatrixDualCasimirHeatInitialIdentity`, and `UnitaryMatrixDualCasimirHeatPositivity`: declarations are mathematically conditional on supplied summability, derivative interchange, geometric Laplacian/Casimir bridge, positivity, Haar normalization, and/or dual density. Their probes explicitly label “conditional heat equation”, blocked changed laws, and blocked initial-limit/convolution laws. No unrestricted heat kernel or semigroup theorem is upstreamable from these files now.
- Any theorem asserting heat coefficients are geometric Casimir eigenvalues (`Smooth...Bridge`) is research/bridge debt: the stored equation is not proved by Mathlib. Likewise selected-dual completeness remains frozen even though finite-support approximation consequences are valid.

## Dependencies, destination, and PR order
1. First PR: extract generic compact-domain integrability and finite-sum integral/trace lemmas from `CompactMatrixFourierCoefficient.lean`; compare against pinned Mathlib’s existing `integral_finsetSum`, `Continuous.integrableOn_compact`, matrix trace APIs and avoid duplication.
2. Second: introduce a generic finite-index matrix Fourier coefficient API (inverse convention documented), then add add/smul/zero/trace lemmas; retain YangMills wrappers as compatibility only if needed.
3. Third: extract generic `toLp` finite synthesis inner-product lemma and dense-range corollaries only if Mathlib lacks them; otherwise delete/avoid upstream duplication. Do not include Peter–Weyl density.
4. Fourth: generic summable-positive-family countability lemma and uniform-series infrastructure; keep Casimir/selected-dual structures project-local.
5. Last/hold: Casimir bridge, derivative/interchange, convolution, positivity, heat equation and initial identity pending canonical representation/Casimir mathematics.

## Risks
Pinned Mathlib may already contain equivalent compact Haar, `toLp`, finite integral, dense-range, and `Summable` lemmas; exact declaration names should be checked before any PR. The project uses custom `UnitaryMatrixDual`, matrix representation certificates, and normalized Haar wrappers, so direct upstreaming would leak domain-specific assumptions. “Faithful” selected-dual completeness is especially easy to misread as unrestricted Peter–Weyl. No source files were edited.

## Start Here
Open `YangMills/Mathematics/CompactMatrixFourierCoefficient.lean:56-133` first: it contains the smallest genuinely unconditional Fourier mathematics and the clearest candidates for a Mathlib-quality generic extraction.

```acceptance-report
{
  "criteriaSatisfied": [{"id":"criterion-1","status":"satisfied","evidence":"Concrete ranked findings with exact YangMills/Mathematics paths, declaration ranges, dependencies, destinations, costs, and PR order are recorded above."}],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [],
  "validationOutput": ["Read-only audit; no source changes and no build run."],
  "residualRisks": ["Pinned Mathlib duplicate-name/API overlap was not exhaustively searched; verify before upstream PR.", "Peter-Weyl density and Casimir/heat identification remain conditional or research-dependent."],
  "noStagedFiles": true,
  "diffSummary": "No files changed.",
  "reviewFindings": ["No blocker to the current project; upstreamability is limited to generic Fourier/L2 helper extraction. Keep selected-dual density and heat/Casimir layers conditional."],
  "manualNotes": "Probes/checker closure were excluded as requested."
}
```