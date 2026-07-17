# Verified status

This file records evidence for the current checkout. It is not a roadmap and does not infer
physical adequacy from compilation.

## 2026-07-15 — standalone initialization

Verified:

- Repository initialized independently on branch `cathedral`.
- Lean toolchain pinned to `leanprover/lean4:v4.31.0`.
- Mathlib input pinned to `v4.31.0`; `lake-manifest.json` resolves it to
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `lake build` completed successfully for the root library.
- The Clay PDF was independently downloaded from its canonical URL and matched the pinned bytes;
  Poppler 25.03.0 reproduced the searchable extraction byte-for-byte.
- Clay source manifest verified the PDF and text extraction. A legacy 404 HTML response was
  deliberately excluded.
- Conservative source audit found no proof placeholder or axiom-like project declaration.
- The root build ran `Lean.collectAxioms` over every loaded `YangMills` declaration and found no
  transitive `sorryAx` or project-defined axiom.
- Mutation checks confirmed rejection of source corruption, unmanifested artifacts, unsafe/control
  manifest paths, symlinks, proof placeholders, elaborated `sorryAx` dependencies and project
  axioms.
- The retired `LeanMillenniumPrizeProblems` clone is absent and is not a dependency.

## 2026-07-15 — first mathematical stone: dimensions

Verified:

- `EuclideanDimension` admits exactly natural dimensions one through four.
- The four named dimensions have spatial arithmetic `0`, `1`, `2`, and `3` respectively, without
  asserting reconstruction.
- Mathlib Euclidean spacetime carriers have the declared real finrank.
- Hostile probes reject zero, values above four, equality of dimensions two and four, and a linear
  equivalence between their spacetime carriers.
- The complete build imports the production module and probes before running the kernel axiom
  audit.

## 2026-07-17 — second mathematical stone: signatures

Verified:

- A coordinate-vector carrier is introduced without silently selecting a metric or topology.
- The positive Euclidean sum-of-squares form and mostly-minus Minkowski form are separate
  dimension-indexed declarations.
- Coordinate zero has positive Minkowski weight; every available spatial basis direction has
  negative weight.
- The Euclidean form is nonnegative.
- In dimension one the algebraic forms agree because no spatial coordinate exists; this is not
  presented as equivalence of Euclidean and Minkowski theories.
- From dimension two onward the forms are proved unequal, with dedicated 2D and 4D hostile probes.
- No group action, analytic continuation, or reconstruction claim is introduced.

## 2026-07-17 — third mathematical stone: Lie-algebra simplicity

Verified:

- The project adopts Mathlib's existing `LieAlgebra.IsSimple` rather than inventing a competing
  meaning of “simple.”
- A proved source-facing equivalence exposes its two requirements: every Lie ideal is zero or whole,
  and the bracket is non-abelian.
- Derived theorems and hostile probes reject abelian and subsingleton carriers and proper nonzero
  ideals.
- This reusable layer makes no claim that a group is compact, connected, smooth, or physically
  admissible.

## 2026-07-17 — fourth mathematical stone: compact-simple gauge-group semantics

Verified:

- `CompactSimpleGaugeGroupData G E` preserves the actual carrier `G` and requires a
  finite-dimensional real smooth Lie-group model without replacing `G` by a universal cover.
- Hausdorff and second-countable manifold conventions, topological compactness, connectedness,
  carrier nontriviality, and tangent-Lie-algebra simplicity are explicit.
- The `C∞`-to-`GroupLieAlgebra` regularity/completeness bridge is implemented from Mathlib rather
  than hidden as an axiom.
- Hostile probes independently reject noncompact, disconnected, subsingleton, abelian-tangent, and
  proper-nonzero-ideal mutations.
- Connectedness is labelled as a project strengthening of the terse Clay wording; abstract-group
  simplicity and simple connectedness are not imposed.

## 2026-07-17 — gauge-geometry provenance stone

Verified:

- Daniel Freed's versioned `hep-th/9206021v1` PDF and reproducible Poppler text extraction are
  pinned and hashed.
- Printed pp. 6–9, §1 supply exact locators for principal bundles, gauge transformations,
  connection forms, curvature, Bianchi identity, and gauge covariance.
- The ledger confines this Chern–Simons paper to its general connection-geometry review and does
  not use it as evidence for Yang–Mills existence, action semantics, or a mass gap.
- No geometry declaration was added merely because the source is now available.

## 2026-07-17 — fifth mathematical stone: fiberwise principal torsors

Verified:

- `PrincipalBundleTorsorData G B P` stores one projection and one right action, avoiding unrelated
  action/projection witnesses.
- Every base point has a fiber, fibers are exactly right-action orbits, and the solving group
  element between two points in one fiber is unique.
- Surjectivity, transitivity, freeness, and the set-level orbit/fiber equivalence are derived.
- The product family `B × G → B` supplies a concrete trivial-torsor constructor.
- Hostile probes reject empty total carriers over nonempty bases, missing fibers, base-moving and
  law-breaking actions, nonidentity stabilizers, and nontransitive fibers.
- The module and ledger explicitly deny that this algebraic core supplies topology or smooth local
  triviality.

## 2026-07-17 — sixth mathematical stone: algebraic bundle maps and gauge automorphisms

Verified:

- `PrincipalBundleTorsorMap` couples one base map to one total map and requires projection
  compatibility and right-action equivariance.
- Identity and composition are defined with named evaluation laws and positive probes; same-fiber
  points map to same-fiber points.
- `TorsorGaugeTransformation` is an actual total-space equivalence over the identity base map, not
  an arbitrary endomorphism.
- Gauge transformations carry a proved group structure with identity, composition, inverse, and
  pointwise evaluation laws; an explicit forgetful bridge produces their underlying bundle map.
- Hostile probes reject projection mismatch, failed equivariance, base movement, and noninjective
  gauge candidates; identity and inverse probes give positive consistency evidence.
- Every name and ledger row labels this as algebraic: no smooth gauge transformation is claimed.

## 2026-07-17 — seventh mathematical stone: topological principal bundles

Verified:

- `PrincipalBundleLocalTrivialization` is an open partial homeomorphism to `baseSet × G` whose
  source is exactly the projection preimage and whose coordinates preserve projection and right
  multiplication.
- `TopologicalPrincipalBundleData` requires continuous projection/action and a designated atlas
  with a selected chart covering every base point.
- Selected chart sources are proved to cover the entire total carrier, and right action preserves
  each applicable chart source.
- The global product `B × G → B` gives a concrete topological principal-bundle constructor for any
  topological group.
- Hostile probes independently reject discontinuity, selected charts outside the designated atlas,
  missing coverage, malformed source/target sets, and failed local equivariance.
- No smooth chart compatibility, smooth gauge map, connection, or curvature is inferred.

## 2026-07-17 — eighth mathematical stone: smooth principal bundles

Verified:

- `SmoothPrincipalBundleData` is layered over a fixed topological principal bundle and generic
  Mathlib models with corners.
- Base, structure group, and total carrier have explicit manifold structures; the structure group
  is a `C∞` Lie group.
- Projection and uncurried right action are smooth.
- Every designated atlas chart and its inverse are smooth on their exact source/target domains,
  providing coherent inputs for a future named overlap-transition theorem rather than unrelated
  transition witnesses.
- The smooth product bundle is a concrete positive inhabitant.
- Hostile probes independently reject nonsmooth projection/action, nonsmooth charts, and nonsmooth
  inverse charts; selected charts inherit both directions.

## 2026-07-17 — ninth mathematical stone: smooth gauge transformations

Verified:

- `SmoothGaugeTransformation` is tied to one fixed `SmoothPrincipalBundleData` and retains one
  underlying algebraic gauge automorphism.
- Both the total-space equivalence and its inverse are required to be `C∞`; a forward-smooth
  bijection alone is insufficient.
- Identity, composition, and inverse close to a proved group, with pointwise evaluation laws.
- Projection preservation and right-action equivariance are inherited through the explicit
  algebraic bridge.
- Every smooth principal bundle has the identity smooth gauge transformation.
- Hostile probes reject nonsmooth forward/inverse maps, base movement, and failed equivariance.

## 2026-07-17 — tenth mathematical stone: typed pointwise differential forms

Verified:

- `ManifoldDifferentialForm I M V k` is a degree-indexed family of continuous alternating maps on
  tangent spaces, with the form degree fixed by `Fin k`.
- Pullback takes an explicit `C∞` map proof, uses Mathlib's manifold derivative, and preserves the
  same degree in its result type.
- One-form evaluation and two-form alternation are exposed; equal two-form arguments vanish.
- Every degree has a concrete zero form, and pullback preserves zero.
- Hostile probes reject a nonalternating two-form and a nonzero pullback of zero.
- The module explicitly does not claim smooth dependence on the base point or provide an exterior
  derivative.

## 2026-07-17 — eleventh mathematical stone: Lie-group adjoint action

Verified:

- `lieGroupAdjoint I g` is the continuous linear derivative at the identity of conjugation by `g`.
- Conjugation smoothness is derived from the existing `C∞` Lie-group operations.
- The adjoint map at the identity is the identity map.
- Group multiplication becomes continuous-linear-map composition in the correct order.
- Adjoint action by `g⁻¹` is proved to be both a left and right inverse to action by `g`.
- Hostile probes reject wrong identity, multiplication-order, and inverse behavior.
- This reusable layer introduces no connection or gauge-field witness.

## 2026-07-17 — twelfth mathematical stone: pointwise principal connection conditions

Verified:

- Principal orbit maps and fixed-element right translations are proved smooth before their
  manifold derivatives define fundamental vectors and translated tangent vectors.
- `PointwisePrincipalConnectionData` stores a Lie-algebra-valued degree-one form.
- Vertical normalization recovers each infinitesimal generator and derives injectivity of the
  fundamental-vector map.
- Right equivariance uses exactly `Ad(g⁻¹)` and the derivative of right translation, matching
  Freed's equations (1.9)–(1.10).
- Hostile probes reject broken normalization, noninjective infinitesimal action, and the wrong
  equivariance law.
- This remains explicitly pointwise: no smooth dependence of the form and no concrete connection
  witness are claimed.

## 2026-07-17 — thirteenth mathematical stone: smooth principal connection definition

Verified:

- `ManifoldDifferentialForm.IsSmooth` tests local form evaluation on every tuple of locally smooth
  tangent-vector fields, avoiding a false product topology on a raw dependent family.
- An explicit continuous-linear value-coordinate bridge handles intrinsic tangent Lie-algebra
  values; `groupLieAlgebraModelEquiv` identifies them with Mathlib's normed model, and
  `isSmooth_iff_valueCoordinates` proves that equivalent coordinate choices do not alter the
  smoothness predicate.
- `SmoothManifoldDifferentialForm` bundles the exact pointwise form with this local regularity, and
  every degree has a smooth zero form as positive infrastructure evidence.
- `PrincipalConnectionData` promotes one unchanged `PointwisePrincipalConnectionData` form with
  smooth-section regularity; `toSmoothForm` is definitionally coherent.
- Hostile probes reject a failed local evaluation, concretely reject the nonsmooth absolute-value
  degree-zero form, exercise both directions of the Lie-algebra coordinate bridge, reject missing
  connection smoothness, and reject broken normalization after promotion.
- No concrete principal connection is constructed, and no curvature is inferred.

## 2026-07-17 — fourteenth mathematical stone: derived bundle quotient and overlap maps

Verified:

- Local sections extracted from the selected equivariant trivializations prove that every
  topological principal-bundle projection is open.
- Continuity, surjectivity, and openness then give explicit `IsOpenQuotientMap` and
  `Topology.IsQuotientMap` theorems rather than an unrelated quotient-topology witness field.
- `principalBundleOverlapDomain` and `principalBundleTransition` name the actual change of local
  product coordinates obtained by composing one inverse chart with another chart.
- Designated smooth atlas charts yield `transition_smoothOn`; the overlap domain is open, the
  transition preserves the base coordinate, and reversing the ordered transition recovers the
  original coordinate.
- Hostile probes reject nonopen/nonquotient projections, nonopen overlap domains, nonsmooth
  designated overlap transitions, reversed/malformed transition behavior, and base-moving
  transitions.

## 2026-07-17 — fifteenth mathematical stone: continuous Lie-bracket wedge

Verified:

- `ContinuousLieBracket` isolates joint bracket continuity as standard reusable topological
  Lie-algebra infrastructure.
- A continuous alternating one-form is coherently converted to a continuous linear map in its sole
  input.
- `ContinuousAlternatingMap.lieBracketWedgeOne` constructs a genuine continuous alternating
  two-form by antisymmetrizing both bracket orders.
- The self-wedge evaluates to `2 • [α(v₀), α(v₁)]`, explicitly validating the normalization paired
  with the factor `1/2` in Freed (1.13).
- The operation lifts pointwise to manifold differential forms; hostile probes enforce continuity,
  term order, factor two, alternation, and the zero case.
- No exterior derivative, curvature, connection witness, or Yang–Mills field is constructed.

## 2026-07-17 — sixteenth mathematical stone: tangent Lie-bracket continuity bridge

Verified:

- `instContinuousLieBracketGroupLieAlgebra` transports Mathlib's tangent Lie bracket to the
  finite-dimensional normed model, packages its two linear variables as continuous linear maps,
  and transports joint continuity back to the intrinsic tangent Lie algebra.
- The bridge uses the actual `GroupLieAlgebra` bracket, not a parallel user-supplied operation.
- Probes force the bracket continuity theorem and confirm that tangent-Lie-algebra-valued one-forms
  reach the concrete bracket-wedge construction, including its zero case.
- Finite-dimensionality internally supplies Mathlib's formal `CompleteSpace` prerequisite; a probe
  verifies the project's usual `C∞` context and its explicit smoothness downgrade.
- No concrete gauge group, connection, exterior derivative, or curvature is constructed.

## 2026-07-17 — seventeenth mathematical stone: local-model exterior derivative

Verified:

- `NormedSpaceDifferentialForm` names Mathlib's native continuous alternating coefficient family on
  a real normed vector space.
- `NormedSpaceDifferentialForm.exteriorDerivative` packages Mathlib's Fréchet-derivative
  `extDeriv` and raises degree by exactly one.
- The derivative of a zero-form is tied to `fderiv`; the zero form differentiates to zero.
- For `C∞` coefficient families, the second exterior derivative is zero, and the operation obeys
  Mathlib's sufficiently smooth pullback theorem.
- `toManifoldForm` gives a definitionally coherent view in the project's pointwise manifold form
  carrier on a normed model space; `toManifoldForm_pullback` proves agreement of the `fderiv` and
  `mfderiv` pullback constructions.
- Hostile probes enforce degree, zero-form semantics, nilpotence, exterior-derivative naturality,
  and both evaluation and pullback bridge coherence.
- This is local-model infrastructure only: no arbitrary-manifold exterior derivative, curvature,
  connection witness, or Yang–Mills field is constructed.

## 2026-07-17 — eighteenth mathematical stone: smooth bracket-wedge closure

Verified:

- `SmoothLieBracketCoordinates` states smoothness of a Lie bracket in an explicit normed value
  model, strengthening mere joint continuity exactly where smooth form closure needs it.
- `ManifoldDifferentialForm.IsSmooth.lieBracketWedgeOne` proves that the existing pointwise
  antisymmetrized bracket-wedge of two smooth one-forms is a smooth two-form.
- `SmoothManifoldDifferentialForm.lieBracketWedgeOne` bundles the derived proof without changing the
  underlying pointwise operation.
- `groupLieAlgebraCoordinateBracketCLM` exposes the transported finite-dimensional bracket as two
  continuous linear variables, and `instSmoothLieBracketCoordinatesGroupLieAlgebra` derives
  smoothness for Mathlib's actual tangent bracket.
- Hostile probes enforce smoothness closure, pointwise/bundled coherence, factor-two self-wedge
  normalization, zero behavior, and the usual finite-dimensional `C∞` group integration path.
- No exterior-derivative certificate, curvature, connection witness, or Yang–Mills field is
  constructed.

## 2026-07-17 — nineteenth mathematical stone: manifold one-form Cartan certificates

Verified:

- `ManifoldTangentField.IsSmoothOn` names the same tangent-bundle section regularity used by smooth
  differential forms.
- `oneFormCartanExpressionCoordinates` states
  `D(ω(Y))·X - D(ω(X))·Y - ω([X,Y])` using `mfderivWithin` and Mathlib's intrinsic
  `mlieBracketWithin`, with an explicit normed value-coordinate bridge.
- Swapping the two vector fields negates the expression.
- `SmoothManifoldOneFormExteriorDerivativeCertificate` ties one smooth two-form to that exact
  formula on every open, uniquely differentiable local set and every pair of smooth tangent fields.
- Two certificates agree on every admissible local field test; the zero one-form has a concrete
  zero certificate.
- `extDerivWithin_eq_oneFormCartanExpression` proves compatibility with Mathlib's normed-space
  exterior derivative and `lieBracketWithin` formula.
- Hostile probes reject malformed formulas, a missing nonzero bracket term, wrong swap sign, and
  disconnected certificate derivatives.
- This remains a certified `1 → 2` interface: no canonical general-degree arbitrary-manifold
  exterior derivative, principal curvature, connection witness, or Yang–Mills field is constructed.

## 2026-07-17 — twentieth mathematical stone: derived principal curvature

Verified:

- Addition and real scalar multiplication preserve `SmoothManifoldDifferentialForm.IsSmooth` and
  retain the exact pointwise operations.
- `PrincipalConnectionExteriorDerivativeData` ties a Cartan certificate to the unchanged smooth
  one-form of one `PrincipalConnectionData`; it cannot name an unrelated connection form.
- `PrincipalConnectionData.curvatureForm` derives a smooth degree-two form as
  `dΘ + 1/2 [Θ ∧ Θ]`, exactly Freed (1.13).
- `curvatureForm_apply` uses the proved factor-two self-wedge normalization to reduce pointwise
  evaluation to `dΘ(v₀,v₁) + [Θ(v₀), Θ(v₁)]`.
- Hostile probes reject nonsmooth, formula-disconnected, factor-confused, and nonalternating
  curvature candidates; no standalone curvature witness field exists.
- No principal connection, exterior-derivative certificate for a nonzero connection, curvature
  witness, horizontality/equivariance theorem, Bianchi identity, gauge covariance, or Yang–Mills
  field is constructed.

## 2026-07-17 — twenty-first mathematical stone: invariant Lie-algebra inner products

Verified:

- `InvariantInnerProductData` records a continuous symmetric positive-definite real bilinear pairing
  on the intrinsic tangent Lie algebra. Continuity, bilinear symmetry, and positive definiteness are
  explicit project strengthenings of Clay's terser “invariant quadratic form” wording.
- Invariance quantifies over `lieGroupAdjoint` for every element of the same explicit group carrier,
  preserving the gauge group's global form.
- The associated quadratic value is nonnegative, detects zero exactly, and is adjoint invariant.
- `positiveScale` proves that positive normalization changes remain admissible; the checker does not
  pretend Clay's `Tr` convention canonically fixes a scale.
- Hostile probes reject degenerate, asymmetric, negative, and adjoint-noninvariant pairings.
- No particular invariant pairing, integral, metric, Hodge star, coupling, action value, or
  Yang–Mills field is constructed.

Not yet achieved:

- No concrete inhabitant of the gauge-group certificate has been constructed. Mathlib's algebraic
  `SU(n)` API does not supply the complete manifold/compactness/connectedness/tangent-simplicity
  chain, so positive consistency infrastructure remains open.
- No general smooth bundle-map layer, concrete principal-connection/curvature witness,
  curvature horizontality/equivariance/Bianchi/gauge-covariance result, symmetry-group,
  quantum-theory, acceptance, existence, or mass-gap declaration exists.
- No Yang–Mills acceptance declaration exists.
- No standalone Git remote exists or has been pushed. The tested candidate
  `git@github.com:elmismisimoxhunca/lean-yangmills-adaly.git` does not exist, and the available SSH
  credential was scoped to the retired repository. Local commits can proceed; remote publication
  remains an explicit infrastructure blocker.
- Clay, Hall, Aharony–Seiberg–Tachikawa, and Freed artifacts are pinned. Clay equation (1) now
  anchors the action formula and invariant quadratic form, but additional metric/Hodge/integration
  infrastructure remains pending. OS/Wightman, spectral, observable, and lattice sources remain to
  be independently acquired and verified before their corresponding declarations become canonical.

The absence of an acceptance declaration is intentional: no placeholder theorem or arbitrary
structure is introduced merely to make the project appear advanced.
