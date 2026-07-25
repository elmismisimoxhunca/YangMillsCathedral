# Code Context

## Files Retrieved
1. `YangMills/Mathematics/FiniteOrientedEdgeWord.lean` (lines 15-145) - defines oriented edges, reversal, finite holonomy, and inversion/append laws.
2. `YangMills/Mathematics/FiniteGraphRefinement.lean` (lines 15-170) - word substitution, holonomy refinement, chains, and `FiniteGraphRefinementData`.
3. `YangMills/Mathematics/FiniteOrientedEdgeFaceWeight.lean` (lines 15-100) - measurable word holonomy, finite face density products, and weighted measures.
4. `YangMills/Mathematics/FiniteConfigurationSchwartzTensor.lean` (lines 15-130) - finite configuration split/merge and Schwartz pure tensors.
5. `YangMills/Mathematics/ConsecutiveDifferenceCoordinates.lean` (lines 15-125) - difference/anchor linear equivalence and Schwartz lift.
6. `YangMills/Mathematics/FiniteProductRestriction.lean` (lines 15-125) - measure-preserving restriction of finite product coordinates.
7. `YangMills/Mathematics/FiniteBoundaryConnectedWordProbes.lean` and `FiniteGroupIncrementTelescopeProbes.lean` - excluded probes; no production counterpart was found in the finite-file inventory.
8. `.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean` (lines 709-744, 774-820) - direct upstream APIs used by product restriction (`measurePreserving_piCongrLeft`, subtype/product split, `piUnique`).

## Key Code
- `OrientedEdge Edge := forward Edge | reverse Edge`; `OrientedEdge.eval` maps reverse edges to group inverses.
- `finiteOrientedWordHolonomy` recursively multiplies tail on the left; proved `finiteOrientedWordHolonomy_append` and `finiteOrientedWordHolonomy_reverse`.
- `refineOrientedWord` is `List.flatMap` substitution and has reverse and composition theorems; `FiniteGraphRefinementData` adds nonempty composable paths and endpoint certificates.
- `finiteProductRestriction` is coordinate precomposition; its proof factors through Mathlib's `MeasurableEquiv.piEquivPiSubtypeProd` and `measurePreserving_piCongrLeft`.
- `finiteConfigurationSplit` is assembled from Mathlib `ContinuousLinearEquiv.piCongrLeft`, `finSumFinEquiv`, and `sumPiEquivProdPi`; `consecutiveDifferenceAnchorLinearEquiv` is a bespoke finite-dimensional linear coordinate change.

## Architecture
The genuinely general core is list/group algebra and finite-index product bookkeeping. Graph refinement and face weights add domain-specific structures (edge orientation, endpoint coherence, face parameters, Haar weighting), so should not be proposed as-is upstream. Schwartz configuration utilities depend on project `SchwartzTensorProduct`; their finite-index equivalences could be upstreamed only after removing project names and proving a Mathlib-facing API. Product restriction is mostly a wrapper around existing Mathlib Pi-measure equivalences and is not novel enough for upstream.

## Ranked candidates (up to 12)

1. **A (strong): `FiniteOrientedEdgeWord.lean`** — declarations `OrientedEdge`, `underlying`, `flip`, `eval`, `finiteOrientedWordHolonomy`, `reverseFiniteOrientedWord`, and append/reversal laws. Mathlib search found no oriented-edge word or finite holonomy API (only unrelated `Graph` tactic and generic `List.IsChain`). Novelty is plausible, and the dependency closure is only `Mathlib.Algebra.Group.Defs` plus list/group lemmas. Destination: `Mathlib/Algebra/Group/Word` (or `Mathlib/Combinatorics/FreeGroup` if generalized). Refactor to generic `Mul`/`Inv` assumptions where possible, neutralize YangMills naming and convention, add tests for multiplication convention. Small/medium PR, about 1–2 files; **PR order 1**.

2. **B (refactor): `ConsecutiveDifferenceCoordinates.lean`** — `reconstructFromConsecutiveDifferences`, `consecutiveDifferenceAnchorLinearEquiv`, continuous version, and lift. The exact finite-product equivalence APIs already exist (`piCongrLeft`, `finSumFinEquiv`, product Pi equivalences); no matching consecutive-difference API was located. General linear algebra is useful, but current file hardcodes real normed spaces, finite-dimensionality, Schwartz functions, and the project’s anchor convention. Destination: `Mathlib/LinearAlgebra/FiniteDimensional/Coordinates` (coordinate equivalence only); Schwartz lift belongs elsewhere. Refactor to split coordinate equivalence from analytic lift and generalize ring/module assumptions. Medium PR; **order 2**.

3. **B (refactor): `FiniteConfigurationSchwartzTensor.lean`** — `FiniteConfiguration`, `finiteConfigurationSplit/Merge`, `scalarSchwartzTensorProductOnFiniteConfiguration`, zero/one tests, `scalarSchwartzPureTensor`. Mathlib already has the underlying continuous Pi equivalences and `SchwartzMap.compCLMOfContinuousLinearEquiv`; no exact pure finite-family tensor API found. Novelty is mainly a convenient composition layer, with direct closure through `SchwartzTensorProduct` (project dependency). Destination: likely `Mathlib/Analysis/Distribution/SchwartzSpace/TensorProduct` only after independent tensor API review. Remove physical “configuration” terminology and prove generic finite Pi tensor lemmas. Medium/high PR; **order 3**.

4. **B (refactor): `FiniteProductRestriction.lean`** — `finiteProductRestriction`, `measurePreserving`, `map_eq`. Mathlib directly supplies all key ingredients: `measurePreserving_piEquivPiSubtypeProd` (Pi.lean 709), `measurePreserving_piCongrLeft` (726), and product projection preservation. This is a useful convenience theorem but currently duplicates an obvious composition proof and is tied to equal probability measures. Destination: `Mathlib/MeasureTheory/Constructions/Pi` or `Integral/Marginal`; generalize to dependent measures and avoid private selected machinery. Small PR after API generalization; **order 4**.

5. **C (unsuitable): `FiniteGraphRefinement.lean`** — `refineOrientedEdge`, `refineOrientedWord`, `FiniteGraphRefinementData`, refinement composition and measurable family theorems. No Mathlib graph-refinement/holonomy analogue was found, but the structure mixes bespoke oriented-edge words, finite graph endpoint certificates, and Lévy/Yang–Mills semantics. `List.IsChain` itself is already Mathlib. Keep project-local or split only the generic word substitution into candidate 1. Large PR and weak general-purpose scope; **order 5 (do not upstream)**.

6. **C (unsuitable): `FiniteOrientedEdgeFaceWeight.lean`** — `finiteOrientedFaceDensityProduct`, `finiteOrientedFaceWeightMeasure`. Measurability is standard (`Measurable.mul`, `Finset.measurable_fun_prod`) and finite Haar product is project-specific. Face density, parameters, boundary words, and `withDensity` encode a physics construction interface without normalization. Keep local; no credible Mathlib destination. Small code but semantically unsuitable; **order 6 (reject)**.

7. **C (unsuitable): `FiniteGraphRefinement`’s `FiniteGraphRefinementData` endpoint/chain certificates** — proof-irrelevant equality theorem and identity refinement are bespoke wrappers around `List.IsChain`; no existing Mathlib graph model can absorb them without a new graph theory design. Project dependency closure includes oriented words and Haar/measurability layers. Do not upstream; **order 7**.

8. **C (unsuitable): `FiniteConfigurationSchwartzTensor`’s zero/one configuration and pure tensor constructors** — useful internally for OS source carriers but strongly tied to complex Schwartz conventions and project tensor products. Existing Mathlib Schwartz composition APIs cover the mechanical part. Keep as project bridge; **order 8**.

9. **C (unsuitable): `NormalizedCompactHaarFiniteProduct.lean` (dependency of face weights)** — finite products of normalized compact Haar measures are a Yang–Mills measure setup, not a discrete-algebra primitive. Mathlib has Haar and Pi measure infrastructure; upstreaming would duplicate/commit to a specialized normalization interface. **Order 9**.

10. **C (unsuitable): `FiniteBoundaryConnectedWordProbes.lean`, `FiniteGroupIncrementTelescopeProbes.lean`, and all `*Probes.lean`** — explicitly excluded by task; probes are project validation artifacts, not upstream candidates.

## Dependency closure and risks
The strongest candidate’s closure is tiny and independent of geometry. Every graph/face candidate transitively depends on `FiniteOrientedEdgeWord` and then introduces project-specific measure/Haar layers. The finite configuration candidates depend on project Schwartz tensor infrastructure, while Mathlib’s `SchwartzMap.compCLMOfContinuousLinearEquiv` is already available. Product restriction is API overlap rather than missing mathematics. A major risk is upstreaming a convention (tail-times-head holonomy) without making multiplication order explicit; another is presenting graph endpoint certificates as a general graph API when Mathlib has no corresponding graph data model.

## Start Here
Open `YangMills/Mathematics/FiniteOrientedEdgeWord.lean`: it is the only clear standalone discrete-algebra nucleus and the dependency root for the graph files.

```acceptance-report
{
  "criteriaSatisfied": [{
    "id": "criterion-1",
    "status": "satisfied",
    "evidence": "Concrete ranked findings cite exact project files, declarations, Mathlib overlap, dependency closure, destinations, refactors, size, and order."
  }],
  "changedFiles": [],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {"command": "rg -n 'OrientedEdge|IsChain|Graph|FiniteGraph' .lake/packages/mathlib/Mathlib", "result": "passed", "summary": "No oriented-edge/finite graph refinement API; generic List.IsChain and unrelated tactic Graph found."},
    {"command": "rg -n 'measurePreserving_piCongrLeft|measurePreserving_piEquivPiSubtypeProd|measurePreserving_piUnique' .lake/packages/mathlib/Mathlib/MeasureTheory", "result": "passed", "summary": "Direct Pi-measure APIs confirmed."}
  ],
  "validationOutput": ["Read-only audit; no files edited."],
  "residualRisks": ["Exact Mathlib destination and generalization of the oriented-word API require a maintainer design review."],
  "noStagedFiles": true,
  "diffSummary": "No changes.",
  "reviewFindings": ["No blockers; graph/face wrappers are unsuitable while oriented-word algebra is a plausible standalone upstream candidate."],
  "manualNotes": "Checker-listed paths and all *Probes.lean were excluded from candidate recommendations."
}
```