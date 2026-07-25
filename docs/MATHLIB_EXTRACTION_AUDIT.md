# Mathlib extraction audit

## Verdict

The repository contains a real but limited upstream pool. It should **not** be submitted wholesale.
The viable path is a sequence of small Mathlib-native PRs extracting generic lemmas, while the
checker, acceptance records, source-indexed bridges, probes, conditional Peter--Weyl/Casimir stack,
and bespoke principal-bundle hierarchy remain local.

No Mathlib PR has been opened. Every ranking below is a feasibility verdict against the pinned
Mathlib revision, not maintainer preapproval.

## Audit basis

- Mathlib input revision: `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Seven fresh read-only Luna (`openai-codex/gpt-5.6-luna`) scouts covered discrete algebra,
  measure/probability, Haar/representation theory, Fourier/Casimir analysis, Lie/manifold geometry,
  omitted Mathlib-only files, and one skeptical global review.
- The scouts compared declarations directly with `.lake/packages/mathlib/Mathlib`.
- The parent audit inspected the highest-ranked source files and performed additional semantic
  duplicate searches. This changed some scout rankings; in particular the finite increment
  telescope is a specialization of existing `List.prod_range_div'` after replacing `f k` by the
  inverse-valued family.
- `checker/CHECKER_FILES.txt` and all `*Probes.lean` files are excluded from the immediate
  extraction pool. Generic checker dependencies are listed separately so they are not accidentally
  deleted.

Raw advisory reports are retained under `docs/mathlib-audit/`. They are evidence inputs, not the
final adjudication.

## Immediate candidates

### A: prepare a small extraction branch

| Priority | Project source and declarations | Mathlib comparison | Extraction plan | Risk |
|---:|---|---|---|---|
| 1 | `Mathematics/MeasurableEquivWithDensity.lean`: `MeasurableEquiv.map_withDensity_comp` | No exact declaration found; proof composes `map_apply`, `restrict_map`, `lintegral_map_equiv`, and `withDensity_apply` | Move into `MeasureTheory.Measure.WithDensity`; retain `MeasurableEquiv` namespace; minimize hypotheses and add map/restrict examples | Low; maintainers may regard it as a convenience lemma |
| 2 | `Mathematics/SchwartzDirectionalEvaluation.lean`: `iteratedDirectionalEvaluationCLM`, application and closed-kernel lemmas | Mathlib has `TemperedDistribution.delta` and `iteratedLineDerivOpCLM`, but not the composed directional-jet functional | Submit beside Schwartz/tempered derivative APIs; preserve ordered direction convention; test arity zero and one | Low/medium API-placement risk |
| 3 | `Mathematics/ConditionalExpectationPiSystem.lean`: `ae_eq_condExp_of_piSystem_setIntegral_eq` | No packaged theorem found; it composes `ae_eq_condExp_of_forall_setIntegral_eq` with `MeasurableSpace.induction_on_inter` | New conditional-expectation π-system file or addition to the existing conditional-expectation module; document why total integral is separate when `univ` is absent | Medium: subtle trim, sigma-finiteness and vector-valued hypotheses |
| 4 | `Mathematics/ContinuousMultilinearMapBasis.lean`: basis evaluation zero/detection pair | Mathlib has algebraic `Module.Basis.ext_multilinear`, not the continuous-map convenience pair | Generalize scalar ring if practical; place with continuous multilinear maps; make the detection theorem a direct contraposition API | Medium: may be judged too thin unless a consumer is shown |
| 5 | `Mathematics/PositiveBilinearUnitEllipsoid.lean`: `positiveBilinear_unitEllipsoid_isVonNBounded` | No matching finite-dimensional positive-bilinear ellipsoid theorem found; nearby Mathlib coercivity results assume stronger packaged coercivity | First state a quantitative coercivity/lower-bound lemma, then derive norm and von Neumann boundedness; retain the subsingleton case | Medium: specialized conclusion and preferred coercivity API need maintainer review |

### B: useful, but redesign or split before proposing

| Project source | Why it may be useful | Required redesign |
|---|---|---|
| `SumOpensMeasurableSpace.lean` | The underlying theorem is A-level and follows cleanly from `measurableSet_sum_iff` and `isOpen_sum_iff` | Treat the current global instance as B until maintainers confirm that it has no instance-diamond or import-cost consequences |
| `FiniteOrientedEdgeWord.lean` | Its generic signed-edge involution, reversal, evaluation and noncommutative fold laws have no exact pinned-Mathlib counterpart | B design candidate only: remove holonomy/Yang--Mills terminology, make multiplication order explicit, and decide whether this belongs with free-group words or remains application combinatorics |
| `CompactMatrixFourierCoefficient.lean` (integrability, trace, add/smul/zero kernel only) | The coordinate integrability and finite trace/integral identities are unconditional and separable from selected-dual/Casimir data | B pending an abstract compact-group Fourier API; current matrix coordinates and custom normalized Haar wrapper are too narrow, and most proofs are compositions of compact integrability and finite-sum integration |
| `ContinuousAlternatingMapProjectionIndependence.lean` | Reusable arbitrary-arity projection-independence proof | Prove the algebraic result for `AlternatingMap`/`MultilinearMap`; expose a continuous corollary only if needed |
| `ContinuousAlternatingMapSmoothEvaluation.lean` | Reconstructs smoothness from all fixed-tuple evaluations in finite dimension | Search for a more general CLM-valued smoothness theorem and align statement with it |
| `RootedGroupDifference.lean` | Exact noncommutative finite-chain equivalences and measurable versions | Three PRs: algebraic equivalence, measurable equivalence, then measure preservation; neutral naming and orientation documentation |
| `SchwartzHausdorff.lean` | Proves the Schwartz seminorm family separates points | Prefer upstream global `T1Space`/`T2Space` instances only with maintainer approval; named local structures suggest prior instance caution |
| `ManifoldBoundaryChartFrontier.lean` | General chart-coordinate frontier theorem | Check whether it should be a corollary in `InteriorBoundary`; review regularity and atlas assumptions |
| `ObservationGeneratedMeasurableSpace.lean` | General dependent family of observation-generated measurable spaces | Align with existing `iSup`/`comap` API and demonstrate a non-project consumer |
| `LinearMapGraphCoreGenerator.lean` | Generic semigroup-orbit continuity and graph-core lemmas | Split continuity from graph density; replace ad hoc graph predicates with a graph norm/operator-domain API |
| `CompactRepresentationHaarAverage.lean` and `CompactHaarIntertwinerAverage.lean` | Mathlib appears to lack compact-group invariant-inner-product and intertwiner averaging theorems | Rewrite for abstract finite-dimensional continuous representations and standard Haar classes; remove `Fin n` matrix and custom normalized-measure scaffolding |
| compact unitary coefficient/character orthogonality | Important missing compact-group representation theory | Only after abstract averaging/intertwiner PRs; redesign around canonical representations and explicit Haar probability conventions |

## Do not submit as current mathematics

### Existing theorem or thin specialization

- `FiniteGroupIncrementTelescope.lean`: useful locally, but
  `List.prod_range_div' n (fun k => (value k)⁻¹)` already contains the central noncommutative
  endpoint telescope. Only the `Fin`/`List.ofFn` prefix packaging lies outside that direct semantic
  specialization, and it is unlikely to justify a PR by itself.
- `FiniteProductRestriction.lean`: long reindexing glue over existing Pi-measure-preservation
  theorems; only reconsider after a genuinely more general marginal theorem is designed.
- `NormalizedCompactHaarMeasure.lean`, compact convolution wrappers, and matrix character wrappers:
  standard Mathlib Haar/convolution/trace APIs already provide the underlying machinery. This
  rejection does not include the small unconditional kernel of `CompactMatrixFourierCoefficient`,
  which is separately B-ranked above.

### Project contracts or conditional research

- every `Dimensions/` acceptance record and every `*Probes.lean`;
- `CompletedProjectiveTensorProduct.lean`, which explicitly records missing infrastructure;
- boundary-conditioned disintegration records;
- selected-dual density and unrestricted Peter--Weyl interfaces;
- Casimir/heat derivative, positivity, convolution, and initial-identity layers that depend on
  supplied bridge data;
- the principal/associated-bundle, connection, curvature, Cartan and Bianchi hierarchy in its
  present form, because it is a parallel project certificate API rather than Mathlib's
  `FiberBundle`/`VectorBundle` design;
- finite graph/face-weight, Yang--Mills lattice, source-indexed 2D, OS acceptance, and physical
  spectrum wrappers.

## Generic mathematics retained by the checker

The following potentially reusable modules are in the standalone checker closure and are therefore
not part of the immediate “remaining repository” extraction pass:

- `AlternatingMapDegreeTwoBilinear.lean`;
- `OrthonormalBilinearContraction.lean`;
- `ManifoldDifferentialForms.lean` and its smooth-form helpers;
- `ConsecutiveDifferenceCoordinates.lean`;
- `FiniteConfigurationSchwartzTensor.lean` and `SchwartzTensorProduct.lean`;
- selected Lie-algebra and smooth-bracket helpers.

They may be upstreamed later without removing them from the frozen checker snapshot. The strongest
future candidates among them are the degree-two alternating-map adapter, canonical orthonormal
bilinear contraction, and a Mathlib-native pointwise differential-form API. They require separate
maintainer design review and must not block checker publication.

## Proposed PR sequence

1. Create a clean extraction branch based on the exact pinned Mathlib version; copy only one module
   at a time into a scratch Mathlib checkout.
2. Submit or first discuss `MeasurableEquiv.map_withDensity_comp`.
3. Extract directional Schwartz jet evaluation.
4. Extract the conditional-expectation π-system theorem.
5. Propose the continuous-multilinear basis evaluation pair if duplicate review remains negative.
6. Redesign the positive-bilinear coercivity/ellipsoid result and seek analysis-maintainer feedback.
7. In parallel, open design discussions—not code dumps—for:
   - global sum `OpensMeasurableSpace` and Schwartz separation instances;
   - rooted group differences;
   - compact representation Haar averaging.
8. Stop after maintainer rejection rather than broadening a PR with project infrastructure.

For every PR, required gates are: latest-target Mathlib rebase, semantic duplicate search, minimal
imports, Mathlib naming/docstrings, `lake env lean` on the extracted file, Mathlib lint/test commands,
and a downstream project compatibility check. No PR should mention Yang--Mills as its mathematical
motivation unless that motivation is necessary to explain a generally useful API.

## Expected salvage

A realistic near-term result is approximately three to six small PR proposals, not wholesale
upstreaming of the repository. The compact-representation track could become a larger contribution
only after an accepted abstract API design. Rejection of a convenience lemma does not invalidate
the project proof; it only means Mathlib prefers callers to compose existing primitives locally.
