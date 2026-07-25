# Code Context

## Files Retrieved
1. `YangMills/Mathematics/ConditionalExpectationPiSystem.lean` (lines 1-61) - pi-system conditional-expectation closure theorem.
2. `YangMills/Mathematics/WeakMeasureConvergence.lean` (lines 1-93) - finite-measure weak convergence predicate and bounded continuous carrier.
3. `YangMills/Mathematics/LinearMapGraphCoreGenerator.lean` (lines 1-220, continued to 345) - semigroup orbit continuity and graph-core closure utilities.
4. `YangMills/Mathematics/UnitaryMatrixDualDensitySemigroupHom.lean` (lines 1-88) - continuous-map integral CLMs and pullback integration.
5. `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` (line 251) - exact upstream conditional expectation uniqueness theorem.
6. `.lake/packages/mathlib/Mathlib/MeasureTheory/PiSystem.lean` (lines 72-78, 693+) - `IsPiSystem` and `MeasurableSpace.induction_on_inter`.
7. `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean` (line 138) - `ContinuousMap.integral_apply`.

## Key Code
- `ae_eq_condExp_of_piSystem_setIntegral_eq` packages Mathlib's `ae_eq_condExp_of_forall_setIntegral_eq` plus `MeasurableSpace.induction_on_inter`; hypotheses explicitly separate `generator_eq`, `generator_pi`, `total_eq`, and generator set-integral equality.
- `WeaklyConvergesFiniteMeasures` defines finiteness plus convergence against every custom `BoundedContinuousRealFunction`; `one_test` derives total-mass convergence.
- `continuous_nnreal_semigroup_orbit_of_contractive_of_tendsto_zero` proves orbit continuity from semigroup law, contraction, and right-limit at zero. Graph definitions (`IsLinearMapDomainGraphDenseAt`, `IsLinearMapGraphDenseAt`) and contraction/dense-core convergence are elementary reusable lemmas, not concrete operator results.
- `compactContinuousMapIntegralCLM` and `compactContinuousMapPullbackIntegralCLM` construct bounded complex-linear functionals using compact integrability and `norm_integral_le_of_norm_le_const`.

## Architecture
The conditional-expectation file is a thin theorem-level adapter around exact Mathlib primitives, with no new measure-extension or uniqueness theorem. The weak-convergence predicate is project-specific packaging. The graph-core file is independent functional analysis and semigroup infrastructure; it does not establish density or generator facts for Yang–Mills objects. The density-semigroup file builds continuous-test integration as CLMs and later uses finite coefficient identities to transport measure data.

## Findings / Ranking

### A (strong upstream candidate)
- `ConditionalExpectationPiSystem.lean:25-61`, `ae_eq_condExp_of_piSystem_setIntegral_eq`: **A-, small PR, low difficulty**. Exact overlap is intentional composition of Mathlib declarations: upstream `ae_eq_condExp_of_forall_setIntegral_eq` (`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:251`) and `MeasurableSpace.induction_on_inter` (`Mathlib/MeasureTheory/PiSystem.lean:693+`). This is a useful reusable theorem whose explicit pi-system-to-generated-sigma-algebra bridge is absent as a single declaration. Destination should be Mathlib `Probability/ConditionalExpectation` or `MeasureTheory/Function/ConditionalExpectation` (likely a new PiSystem file), after renaming to Mathlib style and reducing project namespace. Dependency closure is already narrowly Mathlib (`Basic`, Bochner Set, PiSystem). Refactor: avoid local `C` if a standard induction idiom is preferred; add tests for `univ` omission and scalar/vector variants. Order first.
- `UnitaryMatrixDualDensitySemigroupHom.lean:31-83`, `compactContinuousMapIntegralCLM` / `compactContinuousMapPullbackIntegralCLM`: **A-/B+, medium PR, medium difficulty**. Exact overlap evidence: Mathlib has `ContinuousMap.integral_apply` in `Integral/Bochner/ContinuousLinearMap.lean:138`, but not these explicit `C(X,ℂ) →L[ℂ] ℂ` and pullback functionals (search found no matching CLM definitions). The project definitions are plausible upstream infrastructure, but should likely generalize to arbitrary complete normed scalar/vector targets and expose equality with `ContinuousMap.integral`; pullback could be expressed via composition CLM. Destination `MeasureTheory/Integral/Bochner/ContinuousLinearMap` (or a compact-space extension). Check assumptions: T2/Borel/finite are stronger than needed in pieces.

### B (useful but refactor/generalization required)
- `WeakMeasureConvergence.lean:20-55,65-91`, `BoundedContinuousRealFunction` and `WeaklyConvergesFiniteMeasures`: **B-, medium PR, medium difficulty**. No exact Mathlib declaration found under MeasureTheory for this project name/carrier. Mathlib already has weak/vague convergence APIs elsewhere, and finite regular-measure extensionality; this custom predicate duplicates a notion but hard-codes real-valued functions, an explicit measurable field, and finiteness as `univ ≠ ⊤`. Upstream only after aligning with existing weak convergence filters/topologies or proving a clear bridge. Destination likely `Probability/ProbabilityMassFunction`-adjacent or `MeasureTheory/Measure/Regular` rather than this bespoke file. Risk: “bounded continuous” functions require bound nonnegative (the structure does not state it, though `abs_le_bound` implies it); probability normalization is intentionally absent.
- `LinearMapGraphCoreGenerator.lean:25-104`, semigroup orbit theorem: **B, medium PR, medium difficulty**. No matching Mathlib declaration found by graph-core/semigroup searches. The theorem is generic metric semigroup analysis and likely upstreamable, but `NNReal`-specific subtraction proof and manual metric epsilon proof should be generalized (ordered additive monoid/time parameter, normed group where possible). Destination `Analysis/Seminorm` or `Analysis/Normed/Operator` plus a semigroup file. Refactor split from this file: semigroup continuity versus graph-core operator lemmas.
- `LinearMapGraphCoreGenerator.lean:120-345`, graph density definitions and closure/contraction lemmas: **B-, medium/large PR, medium-high difficulty**. No exact overlap evidence. Concepts overlap Mathlib's dense range, closures, continuous linear maps, generators, but exact `∀δ` graph predicates and quantifier-warning theorem are project-specific. Upstreamable as foundational lemmas only after replacing ad hoc predicates with a graph norm/subtype or established operator-theory interfaces. Destination `Analysis/Normed/Operator` or semigroup generator infrastructure. Avoid claiming this proves any concrete generator core.

### C (not presently upstream-ready)
- Application-heavy files in this partition, including `UnitaryMatrixDualCasimirHeat*`, `Compact*Character*`, and `UnitaryMatrixDualDensitySemigroupHom` theorems after the CLM definitions: **C, large PR/high difficulty**. Their declarations are tied to project-specific normalized Haar measures, selected Peter–Weyl coefficient presentations, and custom semigroup data. Mathlib has adjacent Haar/integral/continuous-map primitives, but no exact overlap for these application contracts. Keep project-local; upstream only extracted generic lemmas after dependency minimization.
- Measure-extension/uniqueness requests: search found no project file in this Mathematics subset that introduces a standalone measure uniqueness/extension theorem beyond use of Mathlib pi-system induction and integral identities. Do not invent an upstreamability claim; audit downstream usages instead.

## Residual Risks
- Names alone are not novelty evidence: conditional expectation and pi-system machinery are direct Mathlib reuse, and continuous-map integration already has `ContinuousMap.integral_apply`.
- Weak convergence may duplicate existing Mathlib topology APIs; a full import graph/API search is needed before PR design.
- No edits were made. No tests/build commands were run (read-only audit).

## Start Here
Open `YangMills/Mathematics/ConditionalExpectationPiSystem.lean:25` first: it is the smallest, clearest upstream candidate and its exact Mathlib dependency closure is demonstrable.

```acceptance-report
{
  "criteriaSatisfied": [{"id":"criterion-1","status":"satisfied","evidence":"Concrete A/B/C findings with exact project paths, line ranges, Mathlib overlap evidence, destination and risk assessment are recorded above."}],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [],
  "validationOutput": ["Read-only audit completed; no source changes."],
  "residualRisks": ["Weak convergence API duplication and broader application dependency closure require follow-up."],
  "noStagedFiles": true,
  "diffSummary": "No changes.",
  "reviewFindings": ["A: ConditionalExpectationPiSystem is a thin, likely upstreamable pi-system adapter over exact Mathlib primitives.","B: weak convergence and graph-core utilities need substantial API alignment/generalization.","C: Casimir/Peter-Weyl application declarations remain project-local."],
  "manualNotes": "Excluded probes and checker files as requested."
}
```