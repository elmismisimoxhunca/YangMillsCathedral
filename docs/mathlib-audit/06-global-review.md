## Review

### Scope and evidence
- Reviewed the standalone source under `YangMills/`, excluding `checker/`, every `*Probes.lean`, and the dimension/acceptance material as requested.
- The pinned Mathlib revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`lake-manifest.json`, input revision `v4.31.0`). Candidate source files were compared against the Mathlib APIs they import; Mathlib already supplies the underlying primitives in several cases (for example `Module.Basis.ext_multilinear`, `AlternatingMap.alternatizeUncurryFin`, `InnerProductSpace.canonicalCovariantTensor_eq_sum`, `extDeriv`, and `MeasurePreserving.skew_product`). Thus the novelty below is theorem/API-level and must not be read as a claim that the mathematical ideas are absent from Mathlib or the literature.
- The requested `plan.md` and `progress.md` do not exist at the requested path (both reads returned `ENOENT`). This review therefore does not rely on project-document novelty claims.
- The working tree was clean at inspection (`git status --short` produced no entries). No build or source audit was run in this review.

### Ranked upstream candidates

#### A — strongest candidates (small, generic, and plausibly Mathlib-shaped)

1. **`YangMills/Mathematics/FiniteGroupIncrementTelescope.lean:17-61`** — `finiteRightIncrementProduct_eq_endpoints` and prefix version. It is genuinely arbitrary `Group`, has no Yang--Mills types, and imports only basic list/group APIs plus `List.ofFn`. The noncommutative endpoint identity is a useful finite-index lemma not just a project wrapper. The two theorems form one small PR. Prefer a Mathlib namespace/name around finite products and remove the `YangMills.Mathematics` namespace on extraction. Import minimality is excellent; proof is short and direct (`induction`, `group`). Check whether an equivalent list telescope already exists under another name before proposing.

2. **`YangMills/Mathematics/ContinuousMultilinearMapBasis.lean:15-37`** — `continuousMultilinearMap_eq_zero_of_basis_evaluation` and its nonzero detection converse. It is independent of finite dimensionality, uses exactly Mathlib's `Module.Basis.ext_multilinear`, and has a clean anti-vacuity companion. Imports are two narrowly relevant Mathlib modules. This is a particularly good two-theorem PR, though the name should likely live beside `ContinuousMultilinearMap` rather than under a project namespace. Verify no existing `ext`/basis-detection theorem in the pinned source before calling it novel.

3. **`YangMills/Mathematics/AlternatingMapDegreeTwoBilinear.lean:19-71`** — exact `Fin 0`, `Fin 1`, and `Fin 2` adapters, including the continuous wrapper. It is generic algebraic infrastructure with only alternating-map imports, and evaluation is definitionally exact. The useful PR granularity is this file minus any project-specific commentary. The continuous adapter intentionally forgets continuity, so API documentation should say that it does not construct a continuous bilinear map. Search Mathlib's alternating curry API for an existing `Fin 2` adapter first; if absent, this is a strong small contribution.

4. **`YangMills/Mathematics/ContinuousAlternatingMapProjectionIndependence.lean:16-75`** — `ContinuousAlternatingMap.eq_update_of_sub_mem_ker` and `eq_of_linearMap_apply_eq`. The finite multilinear telescoping proof is reusable at arbitrary arity, includes arity zero, and imports only `Alternating.Basic`. The declarations are placed in the root `ContinuousAlternatingMap` namespace, which is closer to Mathlib convention than most repository files. Concrete API cleanup: the proof does not use topology/continuity, so the result should probably be generalized to `AlternatingMap` (or split an algebraic theorem from a continuous alias), reducing assumptions and import weight.

5. **`YangMills/Mathematics/OrthonormalBilinearContraction.lean:22-72`** — `canonicalBilinearQuadraticContraction_eq_sum`, scaling, and basis independence. The file uses Mathlib's canonical tensor rather than installing a codomain inner-product instance, and the three theorems give a coherent usable API. It is generic in the output module and pairing, with only two Mathlib tensor/canonical-tensor imports. This is mathematically more substantial than a wrapper and has a sensible standalone PR. Names should be moved to an `InnerProductSpace`/tensor namespace and the construction should be checked against any existing canonical contraction notation. The proof's `simp` block is concise but a Mathlib PR should include explicit tests for zero-dimensional spaces and non-inner-product codomains.

6. **`YangMills/Mathematics/PositiveBilinearUnitEllipsoid.lean:20-72`** — finite-dimensional coercivity/boundedness of `{v | B v v < 1}`. The argument is complete (compact sphere minimum, positivity, scaling, and the subsingleton case), does not assume symmetry, and concludes the exact bornological notion consumed by Mathlib. Imports are Mathlib-only. This is a good candidate if maintainers want the specific bounded-ellipsoid lemma; it is less certain than 1–5 because the result is specialized and may be better expressed as a norm coercivity theorem followed by a boundedness corollary. The `nontrivial` split and all edge cases are a strength.

7. **`YangMills/Mathematics/ContinuousAlternatingMapSmoothEvaluation.lean:19-60`** — reconstruction of `ContDiffOn` for a finite-dimensional continuous alternating-map-valued family from all fixed-tuple evaluations. It is Mathlib-only, handles arity zero and successors, and explicitly uses the existing finite-dimensional CLM characterization and alternatization. This is a plausible upstream theorem but needs a careful duplicate/API search because `contDiff_clm_apply` is already the central primitive. A PR should be split from any Yang--Mills form code and document why the finite-dimensional domain, rather than codomain, is required.

8. **`YangMills/Mathematics/ContinuousBilinearDiagonalPrecomposition.lean:20-55`** — a generic continuous bilinear diagonal-precomposition operation and finite-dimensional smoothness theorem. It is short, Mathlib-only, and proof quality is good, but novelty is weaker: the theorem is essentially two applications of existing `contDiff_clm_apply`. It is suitable as a utility PR only if an actual Mathlib consumer is supplied; otherwise it is likely too thin for upstream acceptance. The current nested CLM carrier is API-compatible and does not install global instances.

#### B — attractive but requiring a stronger extraction case or substantial API reshaping

9. **`YangMills/Mathematics/SchwartzTensorProduct.lean:18-139`** — `scalarSchwartzTensorProduct` and explicit derivative/decay bounds. It is generic in two real normed spaces and imports only Schwartz/finite-dimensional-calculus primitives. The proof is real mathematics rather than a wrapper, and the factor/product estimates are useful. However, the module explicitly stops before packaging continuity as a bilinear map, so the standalone upstream interface is incomplete; the theorem should either be presented as a self-contained bundled product first or accompanied by the topology/continuity API. It also needs a Mathlib naming review around `SchwartzMap` and tests at zero derivative/zero arity.

10. **`YangMills/Mathematics/RootedGroupDifference.lean:17-246`** — upper/lower noncommutative rooted difference measurable equivalences. The exact inverse identities are strong and the measurable extension is genuinely reusable for arbitrary measurable groups. It is more than a Yang--Mills wrapper and has a useful companion measure-preservation file, but the orientation-specific API is large for one PR and the nested `YangMills.Mathematics.RootedGroupDifference` namespace is project-shaped. Extract first as an algebraic equivalence PR, then a measurable-equivalence PR, then measure preservation. Do not upstream `RootedGroupDifferenceMeasurePreserving.lean` in the same change.

11. **`YangMills/Mathematics/ConditionalExpectationPiSystem.lean:15-57`** — a monotone-class bridge from pi-system set-integral equality to equality with `condExp`. It is generic and Mathlib-only, with a compact, readable induction proof. It deserves an upstream issue/PR only after checking whether `ae_eq_condExp_of_forall_setIntegral_eq` plus an existing pi-system induction already covers it. The `m ≤ m₀`, trimmed-measure, and two-integrability assumptions are subtle; API documentation and a proposition specialized to scalar-valued functions may be needed before acceptance.

12. **`YangMills/Mathematics/GradedLieBracketWedge.lean:17-244`** — arbitrary-degree continuous alternating Lie-bracket wedge and cubic self-bracket/Jacobi cancellation. The alternating-sum construction and degree-one coherence are potentially valuable, but the file imports a project-local `LieBracketWedge` and `ManifoldDifferentialForms`, and it installs project-specific extensions on Mathlib carriers. Extracting it requires first identifying the intended Mathlib differential-form wedge carrier and separating the purely algebraic/continuous operation from manifold wrappers. It is not a small direct PR in its current shape.

13. **`YangMills/Mathematics/ContinuousBilinearWedge.lean:17-204`** — generic continuous bilinear wedge with a one-form, including omitted-slot formula and linearity. The core is reusable, but the file also contains a group-Lie-algebra coordinate coherence theorem and uses project-local bracket APIs; these must be removed into a downstream bridge. The use of `set_option backward.isDefEq.respectTransparency false` around the coherence theorem (`around lines 180-204`) is inappropriate for a clean upstream module. Upstream only the core operation after an API/design review.

### Attractive-looking modules that should **not** be proposed now (C / reject for this submission)

- **`YangMills/Mathematics/NormedSpaceExteriorDerivative.lean:15-92`**: mostly aliases/wrappers around Mathlib's `extDeriv`, plus a project `ManifoldDifferentialForm` bridge. It does not add a standalone exterior derivative implementation and would create competing terminology/API.
- **`YangMills/Mathematics/FiniteMatrixRealContinuousBilinear.lean:15-86`**: finite complex matrix multiplication is specialized to the project carrier and duplicates existing matrix multiplication infrastructure. The explicit real-linear packaging is useful downstream but is not a strong general Mathlib theorem.
- **`YangMills/Mathematics/MatrixRepresentationCharacter.lean`** and the large compact-representation/Fourier stack (`CompactRepresentation*`, `CompactUnitary*`, `UnitaryMatrixDual*`): mathematically substantial, but tightly coupled to project-selected duals, custom normalized-Haar definitions, and a very long dependency chain. Existing Mathlib representation-character and Haar APIs make import minimality and namespace design poor for an initial PR. These should remain project infrastructure until a narrowly isolated theorem has an independent consumer.
- **`YangMills/Mathematics/CompletedProjectiveTensorProduct.lean:15-55`**: explicitly an acceptance interface for missing mathematics, not a construction or theorem. An interface cannot be submitted as completed Mathlib infrastructure; it should remain a named project debt.
- The Euclidean half-space chain (`EuclideanHalfSpaceOutwardRay.lean`, `...NormalLinearMap.lean`, `...BoundaryDerivative.lean`, and dependents) is useful for the project's manifolds-with-boundary proof but is highly niche and tied to the project boundary interpretation. It is not a first submission candidate.
- The Geometry/AdjointBundle, Principal* and Cartan/Bianchi files, including `YangMills/Geometry/PrincipalCurvatureCoordinateBianchiBridge.lean`, depend on project-specific principal-bundle carriers, charts, source contracts, and bridges. Their theorem statements are not presently Mathlib-native even where the underlying mathematics is standard. Do not propose the physical/geometry wrapper modules as global candidates.

### Cross-cutting review findings

- **Import minimality:** Candidates 1–8 are Mathlib-only and mostly import one or two focused modules; this is the clearest submission pool. Candidates 9–13 either stop short of their natural API or import project-defined carriers.
- **Proof quality:** The A files inspected contain ordinary kernel-checked proofs with explicit induction/finite-sum/tensor arguments and no visible `sorry` or project axiom. This review did not run `audit_lean.py` or `lake build`, so that observation is not a replacement for the repository gates.
- **Namespacing:** Generic results are usually under `YangMills.Mathematics`; that namespace must be removed or replaced by canonical Mathlib namespaces. The projection results already extend `ContinuousAlternatingMap` at root, which is the better model. Avoid preserving names such as `YangMills`, `finite...` prefixes, or source-specific “coordinate” language in an upstream API.
- **Novelty:** Do not cite project README/status prose as novelty evidence. For every proposed declaration, search the pinned Mathlib source for statement-equivalent results, not only identical names; several files deliberately build directly on an existing Mathlib theorem and may be judged as wrappers.
- **PR granularity:** One generic concept and its laws per PR is the feasible unit. In particular, split rooted differences into algebraic/measurable/measure-preserving PRs; split continuous bilinear wedge from Lie-group coherence; and never carry a Yang--Mills bridge into a generic module.

### Dependency-ordered extraction strategy

1. **Algebraic base:** extract `AlternatingMapDegreeTwoBilinear` (or a more general curry/evaluation adapter if duplicate search shows that is preferable), and `ContinuousMultilinearMapBasis`. These have no project dependencies and establish the naming/API conventions.
2. **Finite group combinatorics:** extract `FiniteGroupIncrementTelescope` as an independent group/list PR. It is independent of the analytic track.
3. **Alternating-map projection:** extract the algebraic generalization of `ContinuousAlternatingMapProjectionIndependence`; add the continuous namespace theorem only if the final assumptions genuinely need continuity.
4. **Finite-dimensional smooth families:** extract `ContinuousAlternatingMapSmoothEvaluation`, after proving its statement is not already a corollary of a more general CLM-valued smoothness theorem in pinned Mathlib.
5. **Tensor/contraction utilities:** extract `OrthonormalBilinearContraction`; separately consider `PositiveBilinearUnitEllipsoid`. These should be independent of differential-form and Yang--Mills code.
6. **Finite-dimensional bilinear calculus:** only if an external consumer exists, extract `ContinuousBilinearDiagonalPrecomposition` as a small utility; otherwise leave it downstream because it is mostly a convenience wrapper.
7. **Schwartz analysis track:** extract `SchwartzTensorProduct` after adding/choosing a continuity API. Keep it separate from the Euclidean OS source-space modules.
8. **Measure/group track:** extract algebraic `RootedGroupDifference`; follow with measurable and then measure-preserving layers only after the first API is accepted. Treat `ConditionalExpectationPiSystem` as a separate proposal, not a dependency.
9. **Differential-form track (optional):** redesign the core of `ContinuousBilinearWedge`/`GradedLieBracketWedge` against Mathlib carriers, remove all project bridge declarations and transparency options, then seek maintainer feedback before implementation. Do not upstream the manifold/connection/Bianchi modules as part of this effort.

### Residual risks

- No `lake build`, targeted Lean build, `scripts/audit_lean.py`, source verifier, or `git diff --check` was run during this review. Compilation and transitive axiom checks remain required before relying on any candidate.
- The pinned-source comparison here is API-level inspection, not a complete theorem-equivalence search. Exact duplicate searches and Mathlib naming/linter checks are required for every A/B candidate.
- `plan.md` and `progress.md` were unavailable, so any task-specific prioritization in those files could not be incorporated.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "This report gives 13 concrete repository candidates with file paths and line ranges, A/B/C ranking, explicit non-proposals, severity-style residual risks, and a dependency-ordered extraction strategy."
    }
  ],
  "changedFiles": [
    "/tmp/luna-global-review.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "pwd; find .. -maxdepth 2 -type f (plan.md|progress.md); wc -l ...; git status --short; git log -5 --oneline",
      "result": "passed",
      "summary": "Confirmed repository, missing requested plan/progress files, clean working tree, and recent commits."
    },
    {
      "command": "find YangMills -type f -name '*.lean' excluding probes/dimension files",
      "result": "passed",
      "summary": "Enumerated eligible source and inspected generic Mathematics candidates plus pinned Mathlib manifest revision."
    }
  ],
  "validationOutput": [
    "Pinned Mathlib revision: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f (v4.31.0).",
    "No staged files; working tree was clean at inspection."
  ],
  "residualRisks": [
    "Build, source verification, and axiom audit were not run.",
    "Complete statement-equivalence duplicate search in pinned Mathlib remains required.",
    "plan.md and progress.md were absent at the requested path."
  ],
  "noStagedFiles": true,
  "diffSummary": "Added the required global Mathlib-submission review report only; no repository source files changed.",
  "reviewFindings": [
    "note: YangMills/Mathematics/FiniteGroupIncrementTelescope.lean:17-61 is the strongest small generic candidate.",
    "note: YangMills/Mathematics/ContinuousMultilinearMapBasis.lean:15-37 and AlternatingMapDegreeTwoBilinear.lean:19-71 are strong Mathlib-only algebraic candidates.",
    "note: YangMills/Mathematics/NormedSpaceExteriorDerivative.lean:15-92 and CompletedProjectiveTensorProduct.lean:15-55 should not be proposed as completed upstream mathematics.",
    "note: no critical implementation blocker was established from the inspected source; upstream duplicate search and full validation remain prerequisites."
  ],
  "manualNotes": "Project documentation novelty claims were intentionally not trusted. The parent should prioritize the A list and split every extraction at the generic/project boundary."
}
```