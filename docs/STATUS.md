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

## 2026-07-17 — twenty-second mathematical stone: curvature structure certificates

Verified:

- `PrincipalTwoForm.IsHorizontal` detects vertical tangent arguments by the derivative of the actual
  bundle projection and requires vanishing on any such insertion.
- `PrincipalTwoForm.IsRightAdEquivariant` evaluates pullback through the derivative of the actual
  principal right action and compares it with `Ad(g⁻¹)` on the intrinsic tangent Lie algebra.
- `PrincipalCurvatureStructureCertificate` is indexed by one connection and one exterior-derivative
  certificate and applies (1.14)–(1.15) only to their exact derived `curvatureForm`; no disconnected
  two-form field can be substituted.
- Zero-form consistency probes and hostile nonhorizontal/nonequivariant probes validate the exact
  predicate shapes.
- This is explicitly a certificate surface, not an automatic proof of (1.14)–(1.15). Deriving those
  laws from the Cartan certificate and connection laws remains manifold-calculus debt; Bianchi and
  gauge covariance also remain pending.
- No structure-certificate witness, connection, or curvature is constructed.

## 2026-07-17 — twenty-third mathematical stone: set-level adjoint bundle

Verified:

- `adjointBundleRightAction` acts on `P × g` by `(p,X)·g = (p·g, Ad(g⁻¹)X)` and satisfies the exact
  identity and multiplication laws.
- `adjointBundleSetoid` proves the same-orbit relation reflexive, symmetric, and transitive rather
  than postulating a quotient relation.
- `AdjointBundle` is the resulting quotient carrier `P ×_G g`; its projection to the original base
  is derived from principal-action invariance.
- `mk_rightAction` and `mk_eq_mk_iff` prove the exact representative identification and characterize
  class equality by an actual group-orbit witness.
- Hostile probes reject wrong action order, missing diagonal identification, disconnected quotient
  equality, and base-moving representative changes.
- This is only a set-level associated bundle. No topology, smooth vector-bundle atlas, section,
  descended curvature, connection, or Yang–Mills field is constructed.

## 2026-07-17 — twenty-fourth mathematical stone: adjoint-bundle quotient topology

Verified:

- Mathlib's generic `Quotient` topology installs exactly the coinduced topology from the
  representative carrier `P × g`; no competing project-specific topology instance is introduced.
- `mk_isQuotientMap` and `mk_continuous` expose the representative-class map as the defining
  continuous quotient map.
- `projection_continuous` derives continuity from the original principal projection through the
  quotient universal property.
- Continuous zero classes over principal points prove associated-fiber nonemptiness without choosing
  a global section of the principal bundle.
- `projection_isQuotientMap` derives the declared base topology from the already proved principal
  quotient projection; it is not stored as an unrelated topology witness.
- Hostile probes reject a nonquotient representative map, discontinuous/nonquotient base projection,
  empty associated fibers, and a base-moving zero class.
- No local vector-bundle trivialization, smooth structure, section, descended curvature, or
  Yang–Mills field is constructed.

## 2026-07-17 — twenty-fifth mathematical stone: adjoint-bundle local coordinates

Verified:

- A principal chart with group coordinate `k` sends `(p,X)` to `(π(p), Ad(k)X)`; outside the chart
  source the representative function is extended by zero only to define a total quotient lift.
- `adjointBundleChartRepresentative_invariant` proves that the coordinate is unchanged by the exact
  diagonal relation `(p,X)·g = (p·g, Ad(g⁻¹)X)`, including the inverse-order cancellation.
- `AdjointBundle.localCoordinate` therefore descends to the quotient rather than selecting a
  representative.
- `localCoordinateInverse` uses the canonical local representative `chart⁻¹(b,1)`, and both local
  inverse laws are proved on `projection⁻¹(baseSet)` and `baseSet × g`.
- The coordinate's first component is proved to be the associated-bundle projection.
- Hostile probes reject representative dependence, a malformed off-source zero extension or
  `Ad(k)` formula, base movement, and either broken local inverse law.
- These are set-level coordinate laws only. Continuity, local-homeomorphism/vector-bundle packaging,
  smoothness, sections, descended curvature, and Yang–Mills fields remain pending.

## 2026-07-17 — twenty-sixth mathematical stone: conditional topological adjoint trivializations

Verified:

- `lieGroupAdjointCoordinates` transports the derivative-defined `Ad(g)` to the declared normed
  model without replacing the intrinsic tangent Lie algebra.
- `ContinuousLieGroupAdjointData` isolates only continuity of `g ↦ Ad(g)` in those coordinates;
  joint continuity of `(g,X) ↦ Ad(g)X` and `(g,X) ↦ Ad(g⁻¹)X` is derived.
- At this stone the certificate made parameter-dependent manifold differentiation debt explicit;
  the next stone discharges that debt generally from pinned Mathlib infrastructure.
- Given the certificate, the representative coordinate is continuous on the principal chart source,
  and quotient-map locality derives continuity of `AdjointBundle.localCoordinate` on its associated
  open source.
- The inverse map is continuous on `baseSet × g` directly from the principal partial homeomorphism
  and quotient representative map.
- `AdjointBundle.localTrivialization` packages the exact existing forward/inverse maps, sources,
  targets, inverse laws, openness, and continuity as an `OpenPartialHomeomorph`.
- Hostile probes reject discontinuous adjoint actions, disconnected coordinate maps, malformed
  sources/targets, and substituted forward/inverse maps.
- No smooth vector-bundle structure, section, descended curvature, or Yang–Mills field is
  constructed.

## 2026-07-17 — twenty-seventh mathematical stone: derived smooth adjoint regularity

Verified:

- `inTangentCoordinates_const_const` proves that Mathlib's tangent-hom coordinate transport reduces
  to the original family when both tangent base maps are the same constant point.
- `lieGroupAdjointCoordinates_contMDiff` specializes Mathlib's parameter-dependent
  `ContMDiffAt.mfderiv` theorem to the jointly smooth conjugation family and constant identity
  evaluation point.
- Consequently `g ↦ Ad(g)` is `C∞` in the declared normed model coordinates, without a
  finite-dimensional assumption.
- Joint model-coordinate evaluation `(g,X) ↦ Ad(g)X` and its inverse-parameter form
  `(g,X) ↦ Ad(g⁻¹)X` are derived smooth.
- `continuousLieGroupAdjointData` canonically inhabits the retained compact continuity interface;
  adjoint regularity is no longer an external requirement or open debt.
- `AdjointBundle.canonicalLocalTrivialization` consequently packages every principal chart without
  caller-supplied regularity data while retaining the exact coordinate maps.
- Hostile probes reject nonsmooth operator families, nonsmooth joint evaluation, and discontinuity
  of the canonical certificate.
- This is reusable manifold calculus only. It constructs no gauge group, principal bundle,
  connection, curvature, or Yang–Mills field.

## 2026-07-17 — twenty-eighth mathematical stone: generic adjoint-bundle trivializations

Verified:

- `AdjointBundle.bundleTrivialization` promotes each canonical quotient local homeomorphism to
  Mathlib's `Bundle.Trivialization` interface without changing the adjoint quotient carrier or its
  quotient topology.
- The promoted base set, source, target, forward coordinate, inverse coordinate, and projection law
  are definitionally tied to the existing principal chart and representative-independent adjoint
  coordinates.
- The principal bundle's selected chart at each base point induces a selected associated
  trivialization covering that point.
- Selected associated trivialization sources cover the entire adjoint quotient.
- Hostile probes reject malformed base sets, shrunken sources, truncated fibers, disconnected maps,
  missed points, and an empty selected cover.
- This is deliberately only generic bundle-trivialization packaging. No `FiberBundle`,
  `VectorBundle`, charted manifold, smooth vector bundle, section, or descended curvature is
  claimed.

## 2026-07-17 — twenty-ninth mathematical stone: exact adjoint overlap transitions

Verified:

- `adjointBundleOverlapDomain` is the open base-dependent domain on which the principal overlap at
  group coordinate `1` is defined.
- `adjointBundleTransition` is the actual composition of the second promoted quotient coordinate
  with the inverse of the first; no independent transition witness is accepted.
- `adjointBundleTransition_eq` proves the exact formula
  `(b,X) ↦ (b, Ad(k₁₂(b))X)`, where `k₁₂(b)` is the group component of the actual ordered principal
  transition at `(b,1)`.
- Reversing the ordered associated transition recovers the original coordinate through the proved
  quotient-coordinate inverse laws.
- Base preservation, zero preservation, additivity, and real-linearity of the fiber map are derived
  from the same adjoint continuous linear map.
- Hostile probes reject base movement, a disconnected fiber operator, a broken reverse transition,
  zero translation, nonadditivity, and failure of scalar compatibility.
- Smoothness and manifold-atlas packaging remain pending; no `FiberBundle`, `VectorBundle`, or
  smooth adjoint bundle is claimed.

## 2026-07-17 — thirtieth mathematical stone: smooth adjoint overlap formulas

Verified:

- `adjointBundleTransitionGroup_contMDiffOn` derives smoothness of the actual group-valued overlap
  coordinate `k₁₂(b)` from the designated smooth principal transition.
- `adjointBundleTransitionCoordinates` states the associated overlap in the declared normed model
  as `(b,X) ↦ (b, Ad(k₁₂(b))X)`.
- `adjointBundleTransitionCoordinates_contMDiffOn` derives its `C∞` regularity by composing the
  principal transition with the previously proved joint smooth adjoint action.
- `adjointBundleTransition_eq_coordinates` ties the smooth model formula pointwise to the exact
  totalized quotient transition on its natural overlap; no smooth surrogate is disconnected from
  the quotient maps.
- Hostile probes reject nonsmooth group coordinates, nonsmooth associated transitions, and a
  disconnected smooth formula.
- This provides overlap regularity only. A charted-space/groupoid atlas, manifold instance,
  `FiberBundle`, `VectorBundle`, sections, and curvature descent remain pending.

## 2026-07-17 — thirty-first mathematical stone: named quotient chart atlas

Verified:

- `AdjointBundle.modelBundleTrivialization` explicitly transports each intrinsic tangent-Lie-algebra
  fiber coordinate through `groupLieAlgebraModelEquiv`; the atlas does not rely silently on
  Mathlib's implementation-level tangent/model definitional equality.
- `AdjointBundle.productChartedSpace` defines a named `ChartedSpace (B × EG)` directly on the
  existing orbit quotient and existing quotient topology, using exactly the transported promoted
  charts from the designated principal atlas.
- Its selected chart at an associated point is the transported chart selected by the principal
  atlas at that point's projection; selected sources cover every quotient point.
- `AdjointBundle.modelChartedSpace` composes the product atlas with the base charted structure to
  obtain the standard `ModelProd HB EG` model.
- Both charted structures are named values rather than global instances, so distinct explicit
  principal-bundle atlas data cannot silently compete for one quotient type.
- Hostile probes reject disconnected selected charts, missed points, omitted designated charts, an
  empty atlas, and bypassing the explicit tangent-model bridge.
- No fiberwise-linear compatibility groupoid, `IsManifold`, `FiberBundle`, `VectorBundle`, section,
  or descended curvature is claimed. Those remain separate pending stones.

## 2026-07-17 — thirty-second mathematical stone: smooth invertible adjoint operators

Verified:

- `lieGroupAdjointCoordinatesEquiv g` packages the existing coordinate adjoint map as a continuous
  linear equivalence of the declared normed model.
- Its inverse is definitionally the coordinate adjoint at `g⁻¹`; the two inverse laws are derived
  from the already proved intrinsic `Ad(g⁻¹) ∘ Ad(g)` and `Ad(g) ∘ Ad(g⁻¹)` identities.
- The forward continuous-linear-map family is exactly `lieGroupAdjointCoordinates` and is `C∞`.
- The inverse continuous-linear-map family is also `C∞`, by composing the same derived regularity
  theorem with smooth group inversion.
- Hostile probes reject disconnected forward or inverse maps, broken inverse behavior, and
  nonsmooth forward or inverse operator families.
- This is reusable Lie-group infrastructure needed by Mathlib's `contMDiffFiberwiseLinear`
  groupoid. It constructs no gauge group, bundle witness, connection, curvature, or Yang–Mills
  field.

## 2026-07-17 — thirty-third mathematical stone: smooth transition equivalences

Verified:

- `adjointBundleOverlapDomain_eq` identifies the exact associated overlap source with
  `(first.baseSet ∩ second.baseSet) × univ`; no smaller or fiber-dependent source is substituted.
- `adjointBundleTransitionEquiv b` packages the actual ordered principal overlap coordinate as the
  previously derived continuous linear adjoint equivalence.
- The forward operator-valued transition family is `C∞` on the base-set intersection.
- The inverse operator-valued transition family is `C∞` on the same intersection.
- Both results are derived from the designated smooth principal overlap and the general smooth
  forward/inverse adjoint-equivalence families, not stored as atlas assumptions.
- Hostile probes reject malformed overlap sources, disconnected operators, and nonsmooth forward
  or inverse transition-equivalence families.
- These are the precise source and operator inputs required by `contMDiffFiberwiseLinear`; groupoid
  membership and the quotient manifold structure remain pending.

## 2026-07-17 — thirty-fourth mathematical stone: smooth quotient manifold atlas

Verified:

- `AdjointBundle.productHasGroupoid` proves pairwise compatibility of every two designated model
  charts with Mathlib's `contMDiffFiberwiseLinear B EG IB ∞` structure groupoid.
- Each compatibility proof uses the exact base overlap, actual ordered principal transition,
  continuous-linear-equivalence fiber operator, smooth forward and inverse operator families, and
  the exact transported quotient-chart composition.
- `AdjointBundle.modelIsManifold` composes this fiberwise-linear groupoid with the base manifold
  groupoid to provide a named `C∞` manifold structure on the existing adjoint quotient.
- Both the groupoid and manifold structures are named values, not global instances; explicit
  principal-bundle atlas data remains visible.
- The original representative quotient-map theorem coexists with the named manifold structure,
  confirming that no replacement carrier or topology was introduced.
- Hostile probes reject designated transitions outside the fiberwise-linear groupoid and verify the
  availability of the named manifold together with the original quotient map.
- No dependent fiber family, `FiberBundle`, `VectorBundle`, section, descended curvature, or
  Yang–Mills field is constructed.

## 2026-07-17 — thirty-fifth mathematical stone: dependent adjoint fibers

Verified:

- `AdjointBundle.Fiber b` is the subtype of the actual orbit quotient lying over `b`; it does not
  introduce a replacement associated-bundle carrier.
- `totalSpaceToQuotient` forgets only the dependent packaging, while `quotientToTotalSpace` places
  each quotient point over its actual projection.
- `totalSpaceEquivQuotient` proves these maps form a canonical carrier equivalence between
  Mathlib's dependent `Bundle.TotalSpace` shape and the original quotient.
- The equivalence preserves the base projection exactly, and every dependent fiber is nonempty by
  the already proved surjectivity of the quotient projection.
- Hostile probes reject base movement, broken round trips, noninjective forgetting, and empty
  dependent fibers.
- This bridge is deliberately set-level. No total-space topology, topology-coherence theorem,
  homeomorphism, fiber algebra, `FiberBundle`, `VectorBundle`, or smooth bundle is claimed.

## 2026-07-17 — thirty-sixth mathematical stone: dependent topology coherence

Verified:

- `dependentTotalSpaceTopology` is explicitly the topology induced from the established quotient
  topology along the exact dependent-package forgetting map.
- `dependentTotalSpaceHomeomorphQuotient` upgrades the carrier equivalence to a homeomorphism under
  that named topology; no independent topology choice is accepted.
- Its forward and inverse maps remain exactly the previously proved forgetting and packaging maps.
- The homeomorphism preserves the bundle base exactly.
- Both topology and homeomorphism are named values rather than global instances, preventing a
  hidden topology diamond before Mathlib bundle packaging is complete.
- Hostile probes reject a disconnected topology, disconnected homeomorphism, base movement, and
  discontinuous forgetting.
- No fiber algebra, `FiberBundle`, `VectorBundle`, smooth bundle, section, or descended curvature is
  claimed.

## 2026-07-17 — thirty-seventh mathematical stone: dependent fiber algebra

Verified:

- `fiberModelEquiv` identifies any dependent quotient fiber with the declared normed model through
  an explicit designated associated trivialization containing the base point.
- `selectedFiberModelEquiv` uses exactly the principal bundle's explicit selected chart at each base
  point.
- `fiberAddCommGroup` and `fiberModule` transport additive commutative group and real module
  structures through that same selected equivalence.
- `selectedFiberLinearEquiv` proves that the selected coordinate is a real linear equivalence under
  the named transported structures.
- All algebra structures are named values rather than global instances, preserving visibility of
  the selected atlas data.
- Hostile probes reject broken fiber-coordinate round trips, nonadditive or nonscalar coordinates,
  and a nonzero image of fiber zero.
- Linearity of every other designated trivialization and `FiberBundle`/`VectorBundle` packaging
  remain pending; no smooth bundle, section, or descended curvature is claimed.

## 2026-07-17 — thirty-eighth mathematical stone: all designated fiber coordinates are linear

Verified:

- `fiberCoordinateChangeLinearEquiv` is the exact model-coordinate adjoint action of the principal
  overlap from the selected chart to an arbitrary requested designated chart.
- `fiberModelEquiv_eq_coordinateChange` derives, from the quotient transition formula, that each
  requested fiber coordinate is precisely that linear change after the selected coordinate.
- `fiberModelLinearEquiv` packages every designated fiber coordinate as a real linear equivalence
  for the named transported fiber structures.
- `fiberModelLinearEquiv_apply` proves its underlying map is the original quotient-derived
  coordinate, preventing replacement by an unrelated linear surrogate.
- Hostile probes reject disconnected linear replacements and nonadditive or nonscalar behavior in
  arbitrary designated coordinates.
- Dependent-space bundle trivializations, per-fiber topology, `FiberBundle`/`VectorBundle`
  packaging, and smooth bundle claims remain pending.

## 2026-07-17 — thirty-ninth mathematical stone: dependent trivializations

Verified:

- `fiberTopology` pulls each dependent fiber topology back through its exact selected model
  coordinate, and `selectedFiberModelHomeomorph` packages that coordinate as a homeomorphism.
- `dependentModelBundleTrivialization` transports each established quotient trivialization across
  the exact base-preserving dependent-total-space homeomorphism.
- Forward maps remain the original quotient-derived coordinates after package forgetting; inverse
  maps are exact quotient packaging after the original inverse coordinate.
- Base domains remain exactly those of the corresponding principal charts.
- Total-space and fiber topologies remain named structures, with only local instance installation;
  no generated topology silently replaces the quotient-induced topology.
- Hostile probes reject disconnected fiber topologies or homeomorphisms, replacement dependent
  coordinates, and changed base domains.
- `FiberBundle`, `VectorBundle`, smooth bundle, section, and descended-curvature claims remain
  pending.

## 2026-07-17 — fortieth mathematical stone: topology-coherent dependent fiber bundle

Verified:

- `continuous_totalSpaceMk` derives continuity of each dependent fiber inclusion from the preserved
  quotient topology and exact selected quotient trivialization.
- `isInducing_totalSpaceMk` proves each fiber inclusion induces exactly the named selected-coordinate
  fiber topology, using the transported trivialization restricted to its source.
- `dependentFiberBundle` packages the preserved total topology, named fiber topologies, and exact
  transported atlas as a Mathlib `FiberBundle` value.
- No `FiberPrebundle`-generated topology is used and no global bundle instance is installed.
- The selected trivialization at each base point is exactly the transported principal selected chart,
  and the atlas contains precisely transported designated principal-atlas charts.
- Hostile probes reject noninducing fiber inclusions, replacement selected charts, and omission of a
  selected chart from the atlas.
- `VectorBundle`, smooth bundle, section, and descended-curvature claims remain pending.

## 2026-07-17 — forty-first mathematical stone: exact dependent vector bundle

Verified:

- `dependentModelBundleTrivialization_isLinear` proves every transported designated chart is
  fiberwise real-linear for the named selected-coordinate algebra.
- `dependentModelBundleTrivialization_coordChangeL` identifies Mathlib's ordered coordinate change
  exactly with the already derived continuous-linear adjoint transition, in the first-to-second
  direction.
- `dependentVectorBundle` derives operator-norm continuity from smooth principal transition data and
  packages the preserved total topology, named fiber topology/algebra, and exact transported atlas
  as a named Mathlib `VectorBundle` value.
- No `VectorPrebundle`-generated topology and no global topology, algebra, `FiberBundle`, or
  `VectorBundle` instance is installed.
- Hostile probes reject nonlinear designated charts, replacement or reversed coordinate changes,
  and discontinuous operator-valued changes between atlas charts.
- The smooth vector-bundle mixin, sections, and descended-curvature claims remain pending.

## 2026-07-17 — forty-second mathematical stone: smooth dependent vector-bundle mixin

Verified:

- `dependentContMDiffVectorBundle` packages Mathlib's `ContMDiffVectorBundle ∞` mixin for the same
  named fiber algebra, preserved quotient-induced topology, `FiberBundle`, and `VectorBundle`.
- Every mixin obligation is discharged by the existing smooth adjoint operator family after exact
  identification with Mathlib's ordered `coordChangeL`; no surrogate transition is introduced.
- Atlas quantification is exact because arbitrary Mathlib atlas memberships are unpacked back to the
  transported designated principal charts.
- No global instance, replacement topology, section, connection, curvature, or Yang–Mills field is
  introduced.
- Hostile probes reject omission of the mixin and nonsmooth coordinate changes between any two
  designated atlas charts.
- Sections, descended adjoint-bundle-valued forms, and curvature descent remain pending.

## 2026-07-17 — forty-third mathematical stone: dependent adjoint sections

Verified:

- `AdjointBundle.Section` is the dependent choice of an element in the actual quotient fiber over
  each base point, and `Section.totalSpace` has definitionally fixed base projection.
- `Section.IsSmooth` is Mathlib smoothness of that exact total-space map after only local
  installation of the named algebra, preserved topology, and exact smooth vector-bundle structures.
- `Section.isSmooth_iff_selectedCoordinate` derives an exact pointwise local criterion in the
  designated principal chart selected at each base point.
- `Section.zero` and `Section.zero_isSmooth` provide only the expected consistency zero section; no
  nonzero field, connection, curvature, or Yang–Mills witness is asserted.
- Hostile probes reject base-moving section realizations, smoothness disconnected from the selected
  exact coordinate, and a nonsmooth zero section.
- Adjoint-bundle-valued differential forms and curvature descent remain pending.

## 2026-07-17 — forty-fourth mathematical stone: pointwise adjoint-valued forms

Verified:

- `fiberModelContinuousLinearEquiv` packages every designated exact fiber coordinate as a continuous
  linear equivalence for the named algebra and quotient-coherent topology; its underlying map is
  proved unchanged.
- `AdjointBundle.DifferentialForm` defines a degree-`k` pointwise form at `b` as a continuous
  alternating map from `TangentSpace IB b` into the actual dependent adjoint quotient fiber over
  `b`.
- `DifferentialForm.inCoordinates` postcomposes with the exact designated coordinate, and
  `inCoordinates_apply` exposes exact quotient-coordinate evaluation.
- `projection_apply`, `zero`, `zero_apply`, and `evalTwo_same` derive base preservation, the
  pointwise zero form, and degree-two alternation without adding a field witness.
- Hostile probes reject base-moving values, replacement coordinates, nonalternating two-forms, and
  nonzero evaluations of the named zero form.
- Smooth adjoint-valued forms, covariant differentiation, tangent lifts, and curvature descent remain
  pending; no principal curvature has been claimed to descend.

## 2026-07-17 — forty-fifth mathematical stone: smooth adjoint-valued forms

Verified:

- `DifferentialForm.coordinateEvaluation` evaluates a varying-fiber form on tangent fields and uses
  the existing transported chart; on its base set, `coordinateEvaluation_eq_inCoordinates` proves
  this is exactly the quotient-derived continuous-linear coordinate.
- `DifferentialForm.IsSmooth` requires smooth coordinate evaluation for every designated principal
  atlas chart, every subset of its base set, and every locally smooth tuple of tangent fields.
- `DifferentialForm.Smooth` bundles that exact pointwise carrier with its local smoothness proof.
- `DifferentialForm.Smooth.zero` derives the smooth zero form without constructing a bundle of
  alternating maps or replacing the adjoint topology.
- Hostile probes reject replacement chart coordinates, omitted designated charts, a replacement zero
  carrier, and nonsmoothness of the named zero form.
- Covariant differentiation, tangent lifts, the horizontal-equivariant correspondence, and curvature
  descent remain pending; no curvature field witness is introduced.

## 2026-07-17 — forty-sixth mathematical stone: degree-zero form/section coherence

Verified:

- `DifferentialForm.ofSection` and `.toSection` identify dependent adjoint sections with degree-zero
  adjoint-bundle-valued forms using Mathlib's empty-index continuous alternating map.
- `toSection_ofSection` and `ofSection_toSection` prove exact carrier round trips.
- `coordinateEvaluation_ofSection` proves that degree-zero form coordinates are exactly the existing
  transported section coordinates on every designated chart domain.
- `isSmooth_ofSection_iff` proves both directions between local field-evaluation smoothness and
  Mathlib total-space smoothness of the corresponding section.
- Hostile probes reject changed round trips, smoothness disconnected in either direction, and
  replacement degree-zero coordinates.
- No nonzero section or form is constructed; tangent lifts and curvature descent remain pending.

## 2026-07-17 — forty-seventh mathematical stone: principal local tangent lifts

Verified:

- `principalBundleLocalSection` fixes group coordinate `1` in an actual designated principal chart.
- `principalBundleLocalSection_projection` proves exact base preservation on the chart domain, and
  `principalBundleLocalSection_contMDiffOn` derives smoothness from the supplied smooth principal
  trivialization inverse.
- `principalBundleLocalTangentLift` is the manifold derivative of that exact local section.
- `principalBundleProjectionDifferential_comp_localTangentLift` proves its composition with the
  actual bundle-projection differential is the identity; `.rightInverse` exposes the pointwise lift
  law.
- Hostile probes reject base-moving or nonsmooth local sections, tangent lifts disconnected from the
  projection, and nonidentity projection/lift compositions.
- Lift-independence, representative-independence, and curvature descent remain pending; no
  connection or curvature witness is constructed.

## 2026-07-17 — forty-eighth mathematical stone: horizontal lift independence

Verified:

- `PrincipalTwoForm.IsHorizontal.eq_update_of_verticalDifference` proves that changing one tangent
  argument by a vector with zero projection differential leaves a horizontal two-form unchanged.
- `.eq_of_projection_eq` derives equality for any two ordered tangent-lift pairs at the same
  total-space point when their projected base vectors agree.
- `.eq_localTangentLift` specializes this to arbitrary lifts versus the exact designated local
  tangent lifts.
- The proof uses alternating-map linearity and the intrinsic projection differential; it does not
  assume a descended form or caller-supplied independence certificate.
- Hostile probes reject value changes under vertical replacement, disagreement between equal
  projections, and disagreement with designated local lifts.
- Representative independence and curvature descent remain pending; no connection, curvature, or
  descended-form witness is constructed.

## 2026-07-17 — forty-ninth mathematical stone: right-action representative independence

Verified:

- `principalBundleProjectionDifferential_comp_rightTranslationDifferential` proves that the
  differential of actual right translation preserves projected tangent vectors.
- `PrincipalTwoForm.IsRightAdEquivariant.mk_rightTranslation` combines exact right equivariance with
  `AdjointBundle.mk_rightAction` to prove equality in the actual adjoint orbit quotient.
- `.mk_eq_of_rightTranslation_and_projection_eq` combines this with horizontality to allow arbitrary
  replacement lifts having matching projections at the translated representative.
- These are derived theorems from the existing structural predicates; no caller-supplied quotient
  equality or descended-form witness is accepted.
- Hostile probes reject altered projection differentials, changed quotient representatives, and
  dependence on right-related representatives or matching replacement lifts.
- Construction and smoothness of the descended base two-form remain pending; no curvature descent is
  claimed yet.

## 2026-07-17 — fiftieth mathematical stone: pointwise principal two-form descent

Verified:

- `AdjointBundle.fiberModelEquiv_localSection_mk` identifies the exact designated coordinate of a
  quotient point represented at the chart's local section.
- `PrincipalTwoForm.selectedBaseForm` constructs a continuous alternating degree-two map into each
  actual dependent adjoint quotient fiber using the selected local tangent lift and exact fiber
  continuous-linear equivalence.
- `selectedBaseForm_coordinate` and `_quotient` prove its unchanged model coordinate and exact
  quotient representative.
- `selectedBaseForm_quotient_eq_rightRelated` proves that horizontality and right adjoint
  equivariance make the pointwise value agree with every right-related representative and matching
  lift tuple.
- Hostile probes reject replacement coordinates, unrelated quotient representatives, and
  right-related presentation mismatches.
- Specialization to the certified principal curvature and smoothness of the descended base form
  remain pending; neither is claimed by this generic pointwise construction.

## 2026-07-17 — fifty-first mathematical stone: certified pointwise curvature descent

Verified:

- `PrincipalConnectionData.pointwiseBaseCurvature` specializes the generic pointwise descent to the
  exact `connection.curvatureForm exterior`, not a caller-selected principal form.
- `pointwiseBaseCurvature_eq` makes that definitional tie explicit.
- `_quotient` exposes the exact selected local-section/lift representative of the derived curvature.
- `_quotient_eq_rightRelated` uses the structure certificate indexed by that same curvature to prove
  agreement with every right-related presentation and matching lift tuple.
- `_evalTwo_same` proves alternation survives descent.
- Hostile probes reject unrelated principal forms, replacement quotient representatives,
  right-related certificate mismatches, and loss of alternation.
- Smoothness of the descended base curvature remains pending; no connection, exterior-derivative
  datum, or structure certificate witness is constructed.

## 2026-07-17 — fifty-second mathematical stone: smooth local lifted fields

Verified:

- `principalBundleLocalTangentLift_eq_tangentMapWithin` identifies the derivative-based exact local
  lift with Mathlib's tangent map within the open principal-chart domain.
- `principalBundleLocalTangentLift_contMDiffOn` proves that applying this lift to a smooth base
  tangent field yields a smooth tangent field along the exact local section.
- `principalBundleLocalTangentLift_totalSpace_proj` records that the lifted field remains based at
  that local section.
- Hostile probes reject replacement tangent-map values, nonsmooth lifted fields, and moved
  tangent-bundle base points.
- No ambient extension, pullback-smoothness certificate, or descended-curvature smoothness claim is
  introduced. Smoothness of principal-form evaluation along the local section remains pending.

## 2026-07-17 — fifty-third mathematical stone: smooth form evaluation along maps

Verified:

- `ManifoldDifferentialForm.IsSmooth.eval_comp_of_ambientFields` proves smooth evaluation of a
  fixed-value smooth form on fields along a smooth map when they agree with ambient smooth fields on
  a containing target set.
- `.eval_comp` supplies the exact restriction specialization.
- The proof is derived from the existing ambient-field smoothness predicate and Mathlib
  `ContMDiffOn.comp`; no new regularity certificate or extension existence assumption is hidden in a
  model record.
- Hostile probes reject loss of smoothness for explicit ambient extensions and their restrictions.
- Construction of ambient principal-chart extensions for the local lifted fields remains pending,
  so smoothness of descended curvature is still not claimed.

## 2026-07-17 — fifty-fourth mathematical stone: ambient local-lift extensions

Verified:

- `exists_principalBundleLocalTangentLift_ambientField` extends a smooth base tangent field to a
  smooth tangent field on the exact principal-chart subset
  `chart.source ∩ projection ⁻¹' s`.
- The construction uses the product-coordinate field `(v, 0)`, Mathlib's canonical product tangent
  equivalence, and the tangent map within the exact inverse principal chart.
- Its restriction at group coordinate `1` is proved equal to the derivative-based
  `principalBundleLocalTangentLift`, using tangent-map composition rather than an unrelated lift.
- Zero totalization outside the source is only dependent typing infrastructure; no smoothness is
  claimed there.
- Hostile probes reject nonexistence and universal disagreement with the exact local lift.
- The generic form-evaluation theorem can now consume these extensions. Its specialization to
  certified curvature and the final descended-curvature smoothness proof remain pending.

## 2026-07-17 — fifty-fifth mathematical stone: smooth principal-form local evaluation

Verified:

- `principalBundleLocalTangentLift_formEvaluation_contMDiffOn` proves that a smooth fixed-value
  differential form on the principal total space evaluates smoothly on exact local lifts of any
  tuple of smooth base tangent fields.
- The proof obtains one explicit ambient field per tangent argument and applies the reusable
  along-map evaluation theorem to the exact local section.
- Smoothness is retained on arbitrary `s ⊆ chart.baseSet`; no openness overclaim is made.
- A hostile probe rejects loss of smoothness for the exact principal form and exact local lifts.
- The theorem is generic and introduces no connection, curvature, or regularity certificate.
  Presentation-independent coordinate rewriting and descended-curvature smoothness remain pending.

## 2026-07-17 — fifty-sixth mathematical stone: smooth principal two-form descent

Verified:

- `PrincipalTwoForm.selectedBaseForm_inCoordinates` identifies the selected pointwise descent in
  every designated chart with principal-form evaluation at that chart's own section and lifts.
- The proof relates the internally selected `trivializationAt` section to the requested chart section
  by the actual torsor action, uses exact dependent transports, and invokes horizontality plus right
  adjoint equivariance for presentation independence.
- `selectedBaseForm_isSmooth` combines that coordinate identity with smooth exact-lift evaluation.
- `selectedBaseFormSmooth` packages the result without changing the pointwise quotient carrier.
- Hostile probes reject arbitrary-chart coordinate replacement, loss of smoothness, and carrier
  replacement during packaging.
- No smooth principal form or structural certificate is constructed. Specialization to the exact
  certified curvature remains pending.

## 2026-07-17 — fifty-seventh mathematical stone: smooth certified-curvature descent

Verified:

- `PrincipalConnectionData.pointwiseBaseCurvature_isSmooth` specializes generic smooth descent to
  the exact `connection.curvatureForm exterior` and its same-index structure certificate.
- `smoothBaseCurvature` packages the result as a smooth adjoint-bundle-valued two-form.
- `smoothBaseCurvature_toForm` and `_toForm_eq_selected` prove that packaging retains the exact
  pointwise descent of the exact derived curvature.
- Hostile probes reject loss of smoothness, replacement of the pointwise carrier, and substitution
  of an unrelated principal two-form.
- No connection, exterior-derivative datum, or structure certificate witness is constructed; this
  is a conditional descent theorem and not an existence claim.

## 2026-07-17 — fifty-eighth mathematical stone: invariant adjoint-fiber pairing

Verified:

- `AdjointBundle.fiberPairing` transports the explicit invariant Lie-algebra pairing to every actual
  dependent adjoint quotient fiber through the exact selected coordinate.
- `fiberPairingInChart_eq` proves every designated chart computes the same scalar by the exact
  adjoint coordinate transition and adjoint invariance.
- The induced pairing is symmetric, nonnegative on the diagonal, and positive definite with respect
  to the named transported fiber zero.
- Hostile probes reject chart dependence, negative quadratic values, and nonzero zero-norm values.
- No global inner-product instance or normalization is installed. Metric contraction, integration,
  coupling, and the action remain separate.

## 2026-07-17 — fifty-ninth mathematical stone: chosen Euclidean curvature contraction

Verified:

- `EuclideanMetricData` names an explicit smooth positive-definite metric on the base tangent bundle
  without installing it globally and without bundling an unrelated measure.
- `chosenOrthonormalTwoFormContraction` computes the conventional `1/2 * sum_ij` contraction using
  Mathlib's standard orthonormal basis in each metric tangent fiber and the exact invariant pairing
  on the actual adjoint quotient fiber.
- `chosenOrthonormalCurvatureDensity` is definitionally tied to
  `connection.smoothBaseCurvature exterior certificate`, and
  `chosenOrthonormalCurvatureDensity_eq_pointwiseBaseCurvature` exposes its exact pointwise carrier,
  preserving the same connection, exterior-derivative datum, and same-index structure certificate.
- The contraction and exact curvature density are proved pointwise nonnegative.
- Hostile probes reject a negative pointwise scalar; unrelated curvature, invariant-pairing, or
  metric substitutions that change the contraction; and chart dependence in the underlying exact
  quotient-fiber pairing.
- No basis-independence or general manifold Hodge-star theorem is asserted. Integration measure,
  coupling, integrability, and the action were left to the next stone; no measure is called
  Riemannian volume.

## 2026-07-17 — sixtieth mathematical stone: Euclidean action relative to a measure

Verified:

- `EuclideanActionAnalyticData` stores proof that the manifold measurable structure is Borel, an
  explicitly designated measure, a strictly positive coupling, and integrability of the exact
  chosen curvature scalar against that same measure.
- The integrability requirement is indexed by the same metric, invariant pairing, connection,
  exterior-derivative datum, and same-index curvature certificate; no arbitrary regularity or
  density witness can be substituted.
- `EuclideanActionAnalyticData.actionCoefficient` is exactly `(4 * coupling ^ 2)⁻¹`, separately
  retaining the inner `1/2` alternating-form convention, and is proved strictly positive from the
  coupling certificate.
- `euclideanYangMillsActionRelativeToMeasure` integrates the exact chosen curvature scalar against
  the designated measure and is proved nonnegative.
- Hostile probes reject a non-Borel measurable structure, nonpositive coupling, nonintegrable exact
  scalar, negative action, unrelated integrand or measure substitutions that change the value, and
  a disconnected caller-supplied action value.
- The designated measure is not described as Riemannian volume. Basis independence for the exact
  dependent curvature contraction, a general Hodge-star bridge, and metric-volume compatibility
  remain explicit debt.

## 2026-07-17 — sixty-first mathematical stone: canonical bilinear contraction

Verified:

- `Mathematics.canonicalBilinearQuadraticContraction` contracts two copies of a bilinear map against
  two canonical covariant tensors and then applies an explicit bilinear scalar pairing.
- The codomain requires only a named bilinear `LinearMap`; no codomain norm or inner-product
  instance is installed, so different pairing normalizations remain compatible.
- `canonicalBilinearQuadraticContraction_eq_sum` proves that every orthonormal basis computes the
  canonical tensor contraction as the familiar double sum.
- `orthonormalBilinearQuadraticContraction_independent` proves those double sums agree for any two
  orthonormal bases.
- Hostile probes reject disagreement with the canonical tensor value, dependence on bases even
  with different index types, and substitution of an unrelated bilinear map that changes the
  contraction.
- This is reusable general mathematics. Specialization to the dependent adjoint fiber was left to
  subsequent adapters; no Hodge-star or volume claim is made.

## 2026-07-17 — sixty-second mathematical stone: bilinear adjoint-fiber pairing

Verified:

- `AdjointBundle.selectedFiberLieAlgebraLinearEquiv` composes the exact selected quotient-fiber
  coordinate with the explicit inverse model/Lie-algebra equivalence.
- `selectedFiberLieAlgebraLinearEquiv_apply` proves that packaging retains that exact coordinate.
- `AdjointBundle.fiberPairingLinearMap` packages the invariant pairing as an iterated real linear map
  on each actual dependent adjoint fiber, using only named locally installed fiber structures.
- `fiberPairingLinearMap_apply` proves evaluation is exactly the established chart-independent
  `AdjointBundle.fiberPairing`; no replacement pairing or global inner-product instance appears.
- Hostile probes reject coordinate replacement, pairing-value replacement, and failure of
  additivity in the packaged first argument.
- This supplies the codomain-pairing prerequisite for canonical tensor contraction. The form
  adapter was left to the next reusable mathematics stone.

## 2026-07-17 — sixty-third mathematical stone: degree-two bilinear adapter

Verified:

- `Mathematics.alternatingMapFinZeroEval` evaluates the unique empty input family, and
  `alternatingMapFinOneToLinear` uses it after one exact curry.
- `alternatingMapFinTwoToBilinear` curries a `Fin 2` alternating map twice into an iterated linear
  map, with `alternatingMapFinTwoToBilinear_apply` proving exact evaluation at `![x, y]`.
- `continuousAlternatingMapFinTwoToBilinear` forgets only continuity packaging and retains the exact
  value of every continuous degree-two alternating map.
- Hostile probes reject algebraic or continuous value replacement and failure of first-argument
  additivity.
- This is reusable general mathematics. Its dependent-fiber specialization was left to the next
  stone; no Hodge-star or volume claim is made.

## 2026-07-17 — sixty-fourth mathematical stone: canonical curvature contraction

Verified:

- `EuclideanMetricData.canonicalTwoFormContraction` applies the canonical covariant tensors to the
  exact degree-two bilinear adapter and exact adjoint-fiber pairing linear map, with all metric and
  fiber structures installed locally.
- `canonicalTwoFormContraction_eq_orthonormalSum` proves every orthonormal basis, with arbitrary
  finite index type, computes the conventional `1/2 * sum_ij` quotient-fiber pairing.
- `canonicalTwoFormContraction_eq_chosen` proves the earlier standard-basis construction is exactly
  this basis-free canonical contraction.
- `canonicalCurvatureDensity` specializes only to
  `connection.smoothBaseCurvature exterior certificate`; it is proved equal to the earlier exact
  chosen curvature scalar and pointwise nonnegative.
- Hostile probes reject canonical/chosen disagreement, basis-dependent sums, negative canonical
  curvature values, and substitution of an unrelated two-form that changes the contraction.
- Basis dependence of the exact pointwise contraction is closed. No general Hodge-star theorem,
  volume form, or metric-induced measure is claimed.

## 2026-07-17 — sixty-fifth mathematical stone: canonical action presentation

Verified:

- `EuclideanActionAnalyticData.canonicalCurvatureDensity_integrable` transports the stored
  integrability requirement from the chosen contraction to the pointwise-equal canonical curvature
  scalar against the same designated measure.
- `euclideanYangMillsActionRelativeToMeasure_eq_canonical` proves the existing action value is
  exactly the integral of the canonical basis-independent scalar with the same action coefficient
  and measure.
- No analytic witness, action value, connection, curvature, pairing, metric, measure, or coupling is
  replaced by the bridge.
- Hostile probes reject nonintegrability of the canonical scalar, disagreement with the canonical
  integral formula, and substitution of an unrelated integrand that changes the weighted value.
- The measure remains designated Borel data rather than claimed Riemannian volume; no Hodge-star
  theorem is asserted.

## 2026-07-17 — sixty-sixth evidence stone: OS-I/OS-II correction record

Verified:

- Full transformed Markdown extractions of Project Euclid's legacy OS-I and OS-II PDF-download
  endpoints were initially retained as provisional search evidence.
- Primary OS-I and OS-II article scans supplied under `/projects/` are now hash-pinned with exact
  `pdftotext -layout` extractions. Both have `%PDF-` signatures, correct title/page metadata, and
  complete article content.
- OS-II printed p. 282 was visually verified to report that OS-I Lemma 8.8 is wrong and that
  sufficiency of the original `(E0)–(E4)` is open.
- OS-II printed p. 287 was visually verified to state factorial growth, `(E0′)` equation (4.1),
  `(E0″)` equation (4.2), and the corrected reconstruction theorem.
- OS-II has correcting priority. No OS, Wightman, Euclidean, or reconstruction declaration is
  introduced by source acquisition alone.

## 2026-07-17 — sixty-seventh mathematical stone: invariant-pairing normalization scaling

Verified:

- `canonicalBilinearQuadraticContraction_smul_pairing` proves that scaling any explicit codomain
  bilinear pairing scales its canonical tensor contraction by the same scalar.
- `AdjointBundle.fiberPairingLinearMap_positiveScale` specializes this to the exact quotient-coherent
  dependent-fiber pairing induced by `InvariantInnerProductData.positiveScale`.
- `EuclideanMetricData.canonicalTwoFormContraction_positiveScale` and
  `canonicalCurvatureDensity_positiveScale` propagate the same factor through the canonical
  two-form contraction and exact certified curvature scalar.
- All fiber, topology, tangent finite-dimensionality, and metric structures remain named and locally
  installed. No global normalization or inner-product instance is introduced.
- Hostile probes reject malformed scaling at the generic canonical contraction, exact dependent
  fiber pairing, and exact canonical curvature levels.

## 2026-07-17 — sixty-eighth evidence stone: Wightman axiomatic sources

Verified:

- The 2000 corrected Princeton edition of Streater–Wightman, *PCT, Spin and Statistics, and All
  That*, is hash-pinned with exact text extraction and publication/ISBN metadata. The byte source is
  a supplied third-party scan, honestly distinguished from a publisher download.
- Printed pp. 96–101 (§3-1) were visually verified: one continuous unitary Poincaré-cover
  representation, forward-cone spectrum, unique invariant vacuum, common dense invariant domain,
  tempered field matrix elements, covariance, locality, and cyclicity are separate obligations.
- Wightman's 1956 *Physical Review* paper, DOI `10.1103/PhysRev.101.860`, is hash-pinned and visually
  verified as primary vacuum-expectation-value/reconstruction evidence.
- The source map records the planned strengthening to one explicit joint translation PVM so that
  energy, momentum, vacuum projection, invariant mass, and the gap cannot be disconnected.
- No Wightman field, Hilbert space, translation representation, PVM, vacuum, existence theorem, or
  mass-gap witness is constructed.

## 2026-07-18 — sixty-ninth evidence stone: lattice regulator sources

Verified:

- Wilson's 1974 *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`, is hash-pinned with exact
  text extraction; the title and lattice-action pages were visually verified.
- Wilson's pp. 2448–2449 define Euclidean lattice variables, local gauge transformations, a periodic
  gauge action, and its formal continuum approximation while explicitly warning that the continuum
  limit is a separate renormalization problem.
- Osterwalder–Seiler's 1978 *Gauge Field Theories on a Lattice*, DOI
  `10.1016/0003-4916(78)90039-8`, is hash-pinned with exact text extraction and visually verified
  article/action/theorem pages.
- Osterwalder–Seiler Theorem 2.1 gives finite-cutoff lattice reflection positivity; Theorem 3.5 gives
  strong-coupling exponential clustering. The source map explicitly prevents either from silently
  becoming continuum OS data or the Clay physical mass gap.
- No lattice regulator, continuum limit, confinement theorem, Euclidean theory, or mass-gap witness
  is constructed by source acquisition.

## 2026-07-18 — seventieth evidence stone: OPE and ultraviolet sources

Verified:

- Wilson's 1969 *Non-Lagrangian Models of Current Algebra*, DOI `10.1103/PhysRev.179.1499`, is
  hash-pinned with exact extraction and visually verified operator-product pages. The source rejects
  primitive coincident products and keeps local-field families, coefficient singularities,
  matrix-element domains, and finite-order truncation visible.
- The independent Gross–Wilczek and Politzer 1973 asymptotic-freedom papers, DOIs
  `10.1103/PhysRevLett.30.1343` and `10.1103/PhysRevLett.30.1346`, are hash-pinned with exact
  extractions and visually verified renormalization-group/beta-function pages.
- The source map classifies asymptotic freedom only as perturbative ultraviolet consistency. Neither
  a negative leading coefficient nor deep-Euclidean control supplies a continuum construction,
  mass-shell spectrum, existence theorem, or mass gap.
- No observable algebra, OPE, running coupling, renormalization bridge, quantum theory, or mass-gap
  witness is constructed by source acquisition.

## 2026-07-18 — seventy-first stone: scalar Schwinger regularity infrastructure

Implemented and verified:

- `PositiveArity` keeps the actual positive correlation-function arity explicit and inhabited.
- `EuclideanNPointSpace`, `ScalarSchwartzTestFunction`, and
  `ScalarTemperedSchwingerDistribution` use the selected Euclidean dimension and actual Mathlib
  Schwartz/tempered-distribution carriers.
- `ScalarSchwingerDistributionFamily` separates normalized `S₀ = 1` from positive-arity tempered
  distributions.
- `FactorialGrowthSequence` records positive coefficients, one positive amplitude, one nonnegative
  real factorial exponent, and a bound indexed by the actual arity.
- `mathlibSchwartzOrderControl` is an explicit finite sum of weighted Fréchet-derivative Schwartz
  seminorms; `MathlibFixedOrderFactorialGrowthData` requires one order and one factorial sequence to
  control every positive arity of the same family.
- The naming and source map deliberately do not identify this Mathlib convention with OS-II
  `(E0′)`: comparison with OS's diagonal-sensitive test spaces and weighted multi-index norm,
  including preservation of factorial growth, remains a required bridge.
- Hostile probes reject zero actual arity, zero `S₀`, nonpositive coefficients or amplitudes,
  negative exponents, zero fixed order, an identically-zero control, and a disconnected nonzero
  distribution value under zero designated control.
- No covariance, reflection positivity, symmetry, clustering, reconstruction, Euclidean theory,
  Wightman theory, existence theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-second stone: scalar Schwinger permutation symmetry

Implemented and verified:

- `euclideanNPointPermutation` promotes every permutation of `Fin n` to a continuous real-linear
  equivalence of the exact `n`-point configuration space in the selected Euclidean dimension.
- `permuteScalarSchwartzTestFunction` is the exact continuous complex-linear Schwartz pullback, with
  its pointwise precomposition formula proved.
- `ScalarSchwingerPermutationSymmetry` states OS-I `(E3)` for every positive arity and every
  permutation of the same scalar distribution family.
- Hostile probes exhibit a genuinely nonidentity two-point transposition and reject changed values
  under the exact designated permutation; an unrelated symmetric family cannot satisfy the field.
- This stone introduces no `(E1)`, `(E2)`, `(E4)`, source-norm bridge, reconstruction, Euclidean
  theory, Wightman theory, existence theorem, or mass-gap witness.

## 2026-07-18 — seventy-third stone: scalar Schwinger proper-Euclidean covariance

Implemented and verified:

- `EuclideanProperRigidMotion` separates an orthogonal linear part, its determinant-one proof, and a
  translation, matching OS-I's proper Euclidean group rather than silently strengthening to `O(d)`.
- Identity and pure-translation motions are available without asserting any Schwinger-family
  inhabitant.
- `euclideanNPointRotation` and `euclideanNPointTranslation` act diagonally on the exact positive-
  arity configuration space.
- `pullbackScalarSchwartzTestFunctionByProperRigidMotion` is a continuous complex-linear Schwartz
  pullback with proved pointwise formula `f (R xᵢ + a)`.
- `ScalarSchwingerEuclideanCovariance` states `(E1)` for the same normalized scalar distribution
  family and exact arity.
- Hostile probes reject determinant `-1`, exhibit a genuinely nonzero translation in every supported
  dimension, verify its exact pullback wiring, and reject covariance of an unrelated value.
- No reflection positivity `(E2)`, clustering `(E4)`, source-norm bridge, reconstruction, Euclidean
  theory, Wightman theory, existence theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-fourth stone: Euclidean time-reflection infrastructure

Implemented and verified:

- `euclideanTimeCoordinate` selects the first coordinate in every supported positive dimension.
- `euclideanTimeReflection` is a linear isometry that exactly negates that coordinate and fixes all
  others; pointwise and Schwartz-pullback involutivity are proved.
- `euclideanNPointTimeReflection` acts diagonally at the exact arity, and
  `reflectScalarSchwartzTestFunction` is its continuous complex-linear Schwartz pullback.
- `strictPositiveTimeConfigurationSet` and `HasStrictPositiveTimeSupport` use strict positivity at
  every point and containment of the actual topological support.
- Hostile probes exhibit positive-time configurations, prove reflected positive-time incompatibility
  at positive arity, and explicitly show that the zero Schwartz test satisfies support vacuously.
- Full `(E2)` remains absent pending OS-I's time-ordered and diagonal-flat `_𝒮₊` source-space bridge
  and the finite sequence product/reflection operation. The following stone supplies a nonzero test;
  subtype inhabitation by zero alone remains explicitly unacceptable anti-vacuity evidence.
- No reflection positivity theorem, clustering, reconstruction, Euclidean theory, Wightman theory,
  existence theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-fifth stone: nonzero positive-time Schwartz test

Implemented and verified:

- `positiveTimeBumpCenter` places an arity-one configuration at selected Euclidean time one.
- `positiveTimeBump` has inner radius `1/4` and outer radius `1/2`; its real compactly supported
  smooth function is transported through `Complex.ofRealCLM` to `positiveTimeBumpSchwartz`.
- The bump equals one at its center and is therefore proved nonzero.
- Coordinate-distance bounds from its closed support prove every supported configuration has
  strictly positive selected time, yielding `positiveTimeBumpTest` in the exact support subtype.
- Hostile probes prove the topological support is nonempty, the packaged value is nonzero, and zero
  substitution is impossible.
- This closes nonzero-domain anti-vacuity only for the reusable all-points-positive subtype. OS-I's
  time-ordered/diagonal-flat source-space bridge, finite test-sequence product, and `(E2)` remain
  absent.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-sixth stone: ordered and coincidence-flat test candidate

Implemented and verified:

- `HasPointCoincidence` names equality of two distinctly labelled Euclidean points.
- `IsFlatAtPointCoincidences` requires every iterated real Fréchet derivative of the exact Schwartz
  function to vanish at every such configuration.
- `strictPositiveTimeOrderedConfigurationSet` requires every selected time positive and strictly
  increasing with point-label order; `HasStrictPositiveTimeOrderedSupport` uses topological support.
- `MathlibPositiveTimeOrderedFlatTestFunction` packages these two properties as a strict subspace,
  not OS-I's exact source carrier: boundary-flat source functions may have boundary points in their
  topological support and are excluded here.
- The explicit arity-one positive-time bump inhabits this candidate nontrivially; ordering and
  coincidence-flatness have no hidden higher-arity obligations at arity one.
- Hostile probes exhibit an all-positive but reversed two-point configuration, so positivity alone
  cannot discharge ordering, and project the exact all-derivative flatness condition.
- Future work must determine the strict subspace's embedding/sufficiency/density/completion relation
  to OS-I's derivative-vanishing carrier and compare Fréchet with multi-index flatness. The induced
  per-arity topology, finite-sequence direct-sum topology, and distinct positive-half-space completed
  tensor product remain separately visible debt, followed by finite sequence products and `(E2)`.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-seventh stone: finite Schwinger test sequences

Implemented and verified:

- `MathlibStrictPositiveTimeTestSequence` separates the arity-zero scalar, a finite positive-arity
  support finset, and the exact underlying Schwartz component at every positive arity.
- Every component retains strict ordered support and coincidence-flatness from the current strict
  Mathlib subspace.
- `mem_support_iff` makes the finset exactly equivalent to nonvanishing of the same component;
  arbitrary finite supersets cannot serve as disconnected summation witnesses.
- Derived theorems force every outside-support component to zero and every nonzero component into
  support.
- Both a zero sequence and a singleton sequence carrying the exact nonzero arity-one positive-time
  bump are constructed without asserting any Schwinger-family or QFT inhabitant.
- Hostile probes reject nonzero outside-support components, omitted singleton support, and
  replacement of the supported bump by an unrelated value.
- The direct-sum topology, sequence product, reflected involution, and `(E2)` remain absent.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-eighth stone: exact configuration concatenation

Implemented and verified:

- `euclideanConfigurationSplit` is a continuous real-linear equivalence from `(n+m)` points to the
  first `n` and final `m` blocks, using `Fin.castAdd m` and `Fin.natAdd n` exactly.
- `euclideanConfigurationMerge` is its inverse, with exact recovery theorems for both blocks and the
  second-block offset.
- `scalarSchwartzRawTensorKernel` is the unbundled function
  `f(x₁,…,xₙ) g(xₙ₊₁,…,xₙ₊ₘ)`, with exact split and merged evaluation theorems.
- Hostile probes prove both blocks are retained, the two explicit positive-time bumps give a
  nonzero kernel value, and zeroing the second factor cannot be ignored.
- This stone itself makes no bundled Schwartz claim. The following stone supplies the generic decay
  theorem; exact configuration pullback and continuous bilinear topology remain pending before the
  finite sequence product.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — seventy-ninth stone: generic scalar Schwartz tensor product

Implemented and verified:

- Projection-pullback derivative norms are bounded using continuous multilinear composition and the
  norm-at-most-one first/second projections.
- `max_pow_le_add_pow` splits product-space polynomial weights between the two factors.
- `scalarSchwartzTensorProduct` packages `(x,y) ↦ f(x)g(y)` as an actual Mathlib Schwartz map using
  the iterated Leibniz bound and explicit finite sums of Schwartz seminorm products.
- Exact evaluation, additivity in both factors, and scalar compatibility in both factors are proved.
- Hostile probes independently zero each factor, preserve nonzero paired evaluations, reject
  unrelated pointwise replacement, and exercise both additive laws.
- The theorem works for arbitrary real normed spaces; it does not rely on finite-dimensionality.
- This generic stone does not itself perform the Euclidean pullback; the following stone supplies
  it. Joint continuity remains pending packaging before the finite sequence product.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eightieth stone: bundled concatenated Schwinger tensor

Implemented and verified:

- `scalarSchwartzTensorProductOnConfiguration` pulls the generic bundled tensor through the exact
  continuous configuration split, producing an actual `(n+m)`-point Schwartz test.
- Its evaluation is proved definitionally equal to `scalarSchwartzRawTensorKernel`; evaluation on an
  exact merged pair is `f x * g y`.
- Additivity and scalar compatibility are proved independently in both factors after pullback.
- Hostile probes connect bundled and raw kernels, independently zero both factors, retain the
  nonzero two-bump tensor, and exercise additive/scalar laws.
- No closure under the current globally strict ordered subspace is claimed: cross-block ordering and
  coincidence conditions require additional hypotheses.
- Joint continuity and finite sequence convolution/product remain pending before `(E2)`.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-first stone: uniform natural-arity sequence components

Implemented and verified:

- `scalarZeroAritySchwartz` embeds a scalar as an actual Schwartz function on the compact zero-point
  configuration space; evaluation, zero, addition, scalar multiplication, and injectivity are proved.
- `extendedComponent` presents one exact Schwartz test at every natural arity, agreeing with the
  stored scalar at zero and the exact dependent positive component otherwise.
- `naturalSupport` combines zero precisely when the scalar is nonzero with the image of the exact
  positive support.
- `mem_naturalSupport_iff` proves exact equivalence between support membership and nonvanishing of
  the same extended component.
- `unitZeroPointTestSequence` supplies a sequence supported exactly at natural arity zero, distinct
  from the existing bump sequence supported exactly at arity one.
- Hostile probes reject omitted natural support and scalar replacement at zero arity and verify the
  exact supports `{}`, `{0}`, and `{1}` for the key examples.
- No convolution/product, direct-sum topology, reflected involution, or `(E2)` is introduced.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-second stone: per-arity Schwinger convolution

Implemented and verified:

- `castScalarSchwartzArity` transports bundled tests only along exact natural-arity equality.
- `schwingerSequenceConvolutionComponent` implements
  `(f × g)ₙ = Σ_{r=0}^n f_{n-r} × g_r` as a finite sum of actual `n`-point Schwartz tests.
- The `Fin (N+1)` index supplies `r ≤ N`; the only cast is the proved equality `N-r+r=N`.
- At arity zero, convolution is the zero-point scalar product. At arity one, both endpoint terms are
  independently exposed.
- The convolution of two singleton arity-one bump sequences at arity two is exactly the nonzero
  bundled two-bump tensor.
- Hostile probes retain zero and one formulas, the internal split, nonvanishing, and rejection of
  zero replacement.
- Finite support of the convolution family, output-sequence packaging, direct-sum topology,
  reflected involution, and `(E2)` remain pending.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-third stone: unrestricted finite Schwartz sequences

Implemented and verified:

- `ScalarFiniteSchwartzSequence` is the unrestricted finite algebra carrier with one dependent
  Schwartz component at every natural arity and exact nonzero support.
- Outside-support vanishing and nonzero-to-support membership are derived.
- `toFiniteSchwartzSequence` forgets strict positive-time ordered/flat proofs while preserving every
  exact extended component and natural support.
- Zero and scalar-unit unrestricted sequences are available; the latter is supported exactly at
  arity zero.
- Hostile probes verify exact support, outside-support rejection, preservation of the singleton bump
  at arity one, and impossibility of omitting it after forgetting.
- This separation prevents convolution output from being falsely required to preserve global
  cross-block positive-time ordering.
- Finite-support convolution packaging, direct-sum topology, reflected involution, and `(E2)` remain
  pending.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-fourth stone: finite Schwinger convolution sequence

Implemented and verified:

- `finiteSequenceSupportBound` is the supremum of exact finite support; every component above it is
  proved zero.
- `finiteSchwartzSequenceConvolutionComponent` extends the exact per-arity formula to arbitrary
  unrestricted finite sequences.
- Above the sum of input support bounds, every split has either its left or right factor zero, so the
  entire convolution component vanishes.
- `finiteSchwartzSequenceConvolutionSupport` filters nonzero components inside the proved finite
  range, and membership is exactly equivalent to nonvanishing.
- `finiteSchwartzSequenceConvolution` packages the result as an unrestricted finite sequence.
- Forgetting positive-time evidence before convolution agrees definitionally with the earlier
  positive-input component formula.
- Hostile probes retain the nonzero singleton-bump arity-two term and reject output support that
  omits it.
- Direct-sum topology/continuity, reflected involution, and `(E2)` remain pending.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-fifth stone: reverse-conjugate Schwartz involution

Implemented and verified:

- `conjugateScalarSchwartz` uses `Complex.conjCLE` as continuous real-linear postcomposition on the
  exact scalar Schwartz carrier.
- `reverseConjugateScalarSchwartz` first applies exact `Fin.revPerm` argument reversal and then
  conjugates the complex value, matching OS-I's printed `f*` convention.
- The pointwise formula, involutivity, additivity, conjugate scalar compatibility, zero behavior, and
  preservation/reflection of nonvanishing are proved.
- Hostile probes expose nonidentity two-point reversal and show that `i` times the real positive-time
  bump evaluates to `-i` after reverse-conjugation, preventing a fake identity/conjugation-free map.
- This operation remains separate from first-coordinate Euclidean time reflection `Θ`.
- Finite-sequence lifting, the combined reflected-star operation, direct-sum topology, and `(E2)`
  remain pending.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-sixth stone: finite-sequence reflected star

Implemented and verified:

- `ScalarFiniteSchwartzSequence.ext` derives sequence equality from all exact dependent components,
  with support equality forced by the nonzero-support invariant.
- `finiteSchwartzSequenceStar` lifts reverse-conjugation componentwise, preserves exact support, and
  is involutive.
- `finiteSchwartzSequenceTimeReflection` separately lifts Euclidean time reflection, preserves exact
  support, and is involutive.
- Time reflection and reverse-conjugation commute on exact components.
- `finiteSchwartzSequenceReflectedStar` applies star first and time reflection second, giving the
  source-facing `Θ f*`; its support is exact and the combined operation is involutive.
- Hostile probes retain exact components/support, reject omission of the nonzero bump after either
  star or combined reflection, and exercise every involution.
- The reflection-positivity inequality `(E2)` and direct-sum topology/continuity remain pending.
- No reflection positivity theorem, Euclidean theory, reconstruction, Wightman theory, existence
  theorem, or mass-gap witness is introduced.

## 2026-07-18 — eighty-seventh stone: algebraic strict-domain reflection form

Implemented and verified:

- `zeroAritySchwingerLinear` evaluates the actual zero-arity Schwartz representation with the
  family's normalized zero-point value.
- `schwingerDistributionAtNaturalArity` packages arity zero and every positive tempered Schwinger
  distribution as algebraic complex-linear functionals.
- `finiteSequenceSchwingerEvaluation` sums exactly over the sequence's nonzero support; the zero
  sequence evaluates to zero, the scalar sequence unit evaluates to one, and the explicit singleton
  bump evaluates through the actual positive-arity distribution.
- `IsNonnegativeComplexReal` requires both zero imaginary part and nonnegative real part.
- `mathlibStrictReflectionPositivityExpression` wires the exact source order `(Θ f*) × f`.
- `MathlibStrictScalarReflectionPositivity` quantifies that form over the current strict positive-time
  ordered/flat Mathlib domain. It is intentionally not named OS-I `(E2)` pending the source-carrier
  and induced/direct-sum/completed-tensor topology comparison.
- Hostile probes instantiate the condition at the explicit nonzero bump and reject imaginary or
  negative-real form values. No satisfying Schwinger family is constructed.
- Source-facing `(E2)`, `(E4)`, Euclidean theory, reconstruction, Wightman theory, existence, and a
  mass-gap witness remain absent.

## 2026-07-18 — eighty-eighth stone: finite-stage sequence topology

Implemented and verified:

- `ScalarFiniteSchwartzStage d s` is the dependent finite product of exact arity Schwartz spaces for
  a finite arity set `s`.
- `scalarFiniteSchwartzStageToSequence` extends by zero and filters support by actual nonvanishing,
  so a stage bound cannot become fake support.
- Every unrestricted finite sequence is recovered exactly from the stage indexed by its actual
  support; the explicit singleton bump survives this recovery.
- `scalarFiniteSchwartzFiniteStageFinalTopology` is the named supremum of the coinduced topologies
  from all stage maps and is not installed globally.
- Every stage map is continuous, and a map out of the final topology is continuous iff all of its
  finite-stage composites are continuous.
- This is not yet identified with OS-I's locally convex direct-sum topology or linear-map criterion:
  topological vector-space operations, source per-arity comparison, and completed positive-half-space
  tensor products remain pending.
- No source-facing `(E2)`, Euclidean theory, reconstruction, Wightman theory, existence theorem, or
  mass-gap witness is introduced.

## 2026-07-18 — eighty-ninth stone: named finite-sequence complex module

Implemented and verified:

- Exact-support scalar sequences are proved equivalent to Mathlib dependent finitely supported
  functions, in both directions.
- Named pointwise addition, negation, and complex scalar multiplication preserve the same dependent
  components while recomputing exact nonzero support.
- Addition support cannot escape the union of input supports but may shrink under cancellation;
  nonzero complex scalars preserve exact support.
- `scalarFiniteSchwartzSequenceAddCommGroup` and `scalarFiniteSchwartzSequenceModule` transport the
  full algebraic laws and are named definitions requiring local `letI` installation.
- Hostile probes prove exact cancellation to the existing zero sequence, empty support after
  cancellation, survival of the explicit bump under multiplication by `i`, and local module wiring.
- No global algebra or topology instance is installed, and no continuity with the finite-stage
  topology or identification with OS-I's direct sum is asserted.
- No source-facing `(E2)`, Euclidean theory, reconstruction, Wightman theory, existence theorem, or
  mass-gap witness is introduced.

## 2026-07-18 — ninetieth stone: continuous linear finite-stage generators

Implemented and verified:

- The named finite-stage final topology, additive group, and complex module are installed locally
  inside a dedicated module; no global instance is exported.
- `scalarFiniteSchwartzStageToSequenceLinearMap` proves every exact finite-stage extension is complex
  linear for the named module.
- `scalarFiniteSchwartzStageToSequenceContinuousLinearMap` bundles the already proved stage
  continuity with that exact linear map.
- Exact components and support containment are preserved by the bundled map.
- Hostile probes exercise named addition and scalar wiring, off-stage vanishing, continuity, support
  escape rejection, and recovery of the explicit nonzero bump through an actual continuous linear
  stage map.
- This establishes generating-stage compatibility only. Joint sequence addition/scalar continuity,
  a topological vector-space package, OS-I direct-sum identification, and convolution continuity
  remain pending.
- No source-facing `(E2)`, Euclidean theory, reconstruction, Wightman theory, existence theorem, or
  mass-gap witness is introduced.

## 2026-07-18 — ninety-first stone: continuous linear coordinate injections

Implemented and verified:

- `scalarSchwartzToSingletonStage` identifies one exact arity Schwartz test with its singleton
  dependent finite stage.
- That assignment is bundled as a continuous complex-linear map for the finite product topology.
- `scalarSchwartzCoordinateInjectionContinuousLinearMap` composes the singleton assignment with the
  corresponding continuous linear stage extension.
- The source component is retained exactly, every distinct component is zero, the map is injective,
  nonzero support is exactly the source singleton, and zero support is empty.
- Hostile probes instantiate the explicit positive-time bump, verify continuity against the named
  preliminary topology, and reject a nonzero value at any wrong coordinate.
- The OS-I iff criterion for linear maps, direct-sum identification, joint algebra continuity, and
  convolution continuity remain pending.
- No source-facing `(E2)`, Euclidean theory, reconstruction, Wightman theory, existence theorem, or
  mass-gap witness is introduced.

## 2026-07-18 — ninety-second stone: coordinate continuity criterion

Implemented and verified:

- Exact component extraction through arbitrary finite sequence sums is proved for the named module.
- Every finite-stage sequence is proved equal to the finite sum of all its natural coordinate
  injections.
- `continuous_linearMap_from_scalarFiniteSchwartzSequence_iff_coordinates` proves that a
  complex-linear map out of the preliminary finite-stage final topology is continuous iff every
  exact coordinate composite is continuous.
- The target may be any topological complex module with continuous addition; finite-stage
  continuity follows from the finite coordinate sum and the topology's universal property.
- Hostile probes expose arity zero, the explicit nonzero bump arity, both criterion directions, and
  reject any globally continuous map with a discontinuous coordinate composite.
- This is an exact theorem for the project's current Mathlib carrier/topology, not an identification
  with OS-I's diagonal-sensitive source spaces or printed locally convex direct sum.
- Joint sequence algebra continuity, source-space comparison, and convolution continuity remain
  pending. No source-facing `(E2)`, reconstruction, existence theorem, or mass-gap witness is
  introduced.

## 2026-07-18 — ninety-third stone: exact Schwinger translations

Implemented and verified:

- `translateScalarSchwartzTestFunction` uses the exact simultaneous pullback convention
  `f(x₁+a,…,xₙ+a)` through the existing proper-Euclidean translation machinery.
- Translation by `-a` inverts translation by `a`; translations compose by displacement addition.
- Every zero-arity test is fixed, and translation preserves and reflects vanishing at every arity.
- `translateScalarFiniteSchwartzSequence` lifts translation componentwise while preserving exact
  finite support definitionally; inverse and composition laws are proved.
- Hostile probes translate the explicit bump by its center and obtain value one at the zero
  configuration, retain its nonzero arity-one support, and reject omitted translated support.
- This is algebraic `(E4)` infrastructure only. No nonzero spatial ray, large-parameter limit,
  clustering axiom, or lattice/continuum identification is introduced.
- No source-facing `(E2)`, `(E4)`, reconstruction, existence theorem, or mass-gap witness is
  introduced.

## 2026-07-18 — ninety-fourth stone: nonzero Euclidean spatial rays

Implemented and verified:

- `EuclideanUnitSpatialDirection` packages a zero-time-component vector with norm exactly one,
  excluding a zero or unnormalized clustering direction.
- A canonical second-coordinate direction is constructed whenever spacetime dimension is at least
  two; four-dimensional Euclidean spacetime receives an explicit direction.
- One-dimensional Euclidean spacetime is proved to admit no unit spatial direction after its sole
  coordinate is selected as time.
- `euclideanSpatialRayDisplacement` has exact time component zero and norm `|λ|`; its norm tends to
  infinity as `λ → +∞`.
- Finite sequences translate along the exact ray without changing support.
- Hostile probes expose the nonzero four-dimensional ray at scale one, the dimension-one rejection,
  escape to infinity, and survival of the explicit bump's arity-one support.
- The `(E4)` factorization expression and clustering limit remain pending. No source-facing `(E2)`,
  `(E4)`, reconstruction, existence theorem, or mass-gap witness is introduced.

## 2026-07-18 — ninety-fifth stone: strict-domain clustering form

Implemented and verified:

- `mathlibStrictReflectedStarSequence` and `mathlibStrictSpatialRayTranslatedSequence` retain the
  exact reflected first cluster and ray-translated second cluster.
- `mathlibStrictScalarClusteringExpression` wires the source order
  `S((Θ f*) × T_{λa}g) - S(Θ f*) S(g)` through exact finite-sequence evaluation and convolution.
- `MathlibStrictScalarClusteringAlongDirection` requires that connected expression to tend to
  complex zero as the real ray scale tends to `+∞`, for every pair of strict test sequences.
- The predicate requires an explicitly supplied unit spatial direction, avoiding hidden vacuity in
  dimension one.
- Hostile probes use the explicit nonzero bump pair and escaping ray, preserve translated support,
  and reject a connected expression that remains constantly one.
- No satisfying Schwinger family is constructed. This strict-subdomain candidate is not named
  source-facing `(E4)` before the carrier/topology comparison.
- Source-facing `(E2)`, `(E4)`, complete Euclidean data, reconstruction, existence, and a mass-gap
  witness remain absent.

## 2026-07-18 — ninety-sixth stone: coherent strict Euclidean candidate

Implemented and verified:

- `MathlibStrictScalarEuclideanCandidate` assembles fixed-order factorial growth, proper-Euclidean
  covariance, permutation symmetry, strict-domain reflection positivity, and direction-indexed
  clustering around one normalized Schwinger family.
- Every field is indexed by that same family; clustering is indexed by one explicitly supplied unit
  spatial direction.
- Projection theorems expose positivity and clustering on every strict test sequence/pair.
- Hostile probes exercise the exact growth bound, `(E1)`, `(E3)`, the explicit nonzero bump in both
  positivity and clustering, and nonvanishing of the candidate direction.
- Dimension one cannot package a direction-indexed composite candidate, matching its proved absence
  of spatial directions rather than hiding a vacuous direction quantifier.
- No inhabitant is constructed. This is not a source-facing OS theory, `(E0′)` bridge,
  reconstruction datum, existence theorem, or mass-gap witness.

## 2026-07-18 — ninety-seventh stone: proper-orthochronous Poincaré kinematics

Implemented and verified:

- `Minkowski.ProperOrthochronousLorentzTransformation` packages an invertible real-linear map that
  preserves the mostly-minus Minkowski quadratic form, has determinant one, and sends the selected
  future time basis to a vector with positive time component.
- Identity is constructed; transformed time/spatial basis vectors retain Minkowski values `1` and
  `-1`; time reversal and determinant-minus-one substitutions are rejected.
- `Minkowski.ProperOrthochronousPoincareTransformation` adds an independent translation and acts by
  the exact affine formula `x ↦ Λx+a`; identity, pure translation, and action injectivity are proved.
- Hostile probes move the origin by the nonzero time basis and retain Minkowski value one, preventing
  an ignored translation or Euclidean-signature substitution.
- This independent Minkowski layer introduces no group closure theorem, Poincaré cover, Hilbert
  representation, field, common domain, spectrum, reconstruction, existence theorem, or mass gap.

## 2026-07-18 — ninety-eighth stone: Poincaré lift/pre-cover unitary representation interface

Implemented and verified:

- `Minkowski.ProperOrthochronousPoincareLiftData` requires a topological group projecting
  surjectively to the exact affine kinematics, respecting identity and multiplication at the action
  level, and containing a continuous injective Minkowski translation map.
- This is explicitly a weaker lift/pre-cover interface: the affine target has no topology here and
  no local-homeomorphism, covering-map, or discrete-kernel law is claimed.
- Translation lifts project to the exact pure affine translations; the nonzero time translation lift
  is proved distinct from cover identity.
- `Minkowski.StronglyContinuousUnitaryPoincareRepresentation` packages one unitary group
  homomorphism on one separable complete complex inner-product space, strongly continuous on every
  vector.
- Physical translation unitaries are derived from that same representation, obey spacetime addition,
  and are strongly continuous. No disconnected surrogate translation representation is accepted.
- Hostile probes expose projection surjectivity, exact group/action wiring, translation-map
  injectivity, nontrivial translations, unitary identity/multiplication, and translation strong
  continuity.
- No lift group, genuine topological cover, Hilbert space, or representation inhabitant is
  constructed. Vacuum, fields, common
  domain, spectrum/PVM, reconstruction, existence, and mass gap remain pending.

## 2026-07-18 — ninety-ninth stone: invariant unique vacuum line

Implemented and verified:

- `Minkowski.IsPoincareInvariantVector` uses the same strongly continuous unitary representation,
  not a disconnected symmetry action.
- `Minkowski.PoincareInvariantVacuumData` requires a unit-norm vacuum fixed by every lift-group
  element and requires every invariant vector to lie on its complex line.
- The vacuum is proved nonzero; invariance under physical translations is derived from the same
  representation's translation subgroup.
- Every normalized invariant vector is proved to differ from the selected vacuum by a unit-modulus
  complex phase.
- Hostile probes reject a zero vacuum and any invariant vector outside the selected vacuum line.
- No vacuum inhabitant is constructed. Field cyclicity, common domain, spectral vacuum projection,
  reconstruction, existence, and mass gap remain pending.

## 2026-07-18 — one-hundredth stone: dense common invariant domain

Implemented and verified:

- `Minkowski.CommonInvariantDomainData` packages one complex submodule of the same physical Hilbert
  carrier, dense in that carrier, containing the exact selected vacuum, and invariant under the same
  strongly continuous unitary representation.
- The selected vacuum is bundled as an actual nonzero domain vector.
- Every physical unitary restricts to a linear isometric equivalence of the exact common domain; its
  inverse and exact underlying action are proved, and it fixes the domain vacuum.
- Hostile probes reject the bottom submodule and any physical unitary image outside the domain while
  retaining density and the same vacuum.
- No common-domain inhabitant, field, adjoint, tempered matrix element, cyclicity theorem, spectrum,
  reconstruction, existence theorem, or mass gap is constructed.

## 2026-07-18 — one-hundred-first stone: scalar Wightman field on the common domain

Implemented and verified:

- `Minkowski.ScalarMinkowskiSchwartzTestFunction` is the actual complex Schwartz carrier on the
  independent Minkowski coordinate space; an explicit compactly supported bump has value one at the
  origin and is nonzero.
- `Minkowski.ScalarWightmanFieldOnCommonDomainData` packages one scalar field and its adjoint as
  complex-linear maps into endomorphisms of the exact previously selected common domain.
- For every ordered domain-vector pair, field and adjoint matrix elements are actual tempered
  distributions and are coherently equal to the corresponding Hilbert inner products.
- The adjoint relation uses the conjugated Schwartz test and the same field/domain data.
- Hostile probes retain the nonzero test, exact domain outputs, coherent bump matrix elements, and
  reject a disconnected replacement scalar.
- No field datum inhabitant, covariance, locality, cyclicity, spectrum, reconstruction, existence
  theorem, or mass gap is constructed.

## 2026-07-18 — one-hundred-second stone: scalar Wightman covariance

Implemented and verified:

- `Minkowski.pullbackScalarMinkowskiSchwartzTestFunction` constructs the exact source convention
  `f(Λ⁻¹(x-a))` from a continuous linear Lorentz equivalence and translation pullback.
- Identity and pure-translation formulas are proved; affine pullback preserves and reflects
  vanishing.
- `Minkowski.ScalarWightmanFieldCovarianceData` requires both field and adjoint to transform by
  conjugation with the exact same restricted physical unitary, projected affine transformation,
  common domain, and field datum.
- Hostile probes translate the explicit bump to value one at the translation point, retain its
  nonvanishing, and derive translation covariance through the same lift-group translation map.
- No covariance inhabitant, locality, cyclicity, spectrum, reconstruction, existence theorem, or
  mass gap is constructed.

## 2026-07-18 — one-hundred-third stone: scalar Wightman vacuum cyclicity

Implemented and verified:

- `Minkowski.ScalarWightmanFieldLetter` distinguishes exact field and adjoint insertions with their
  Minkowski Schwartz tests.
- `scalarWightmanFieldWordOnVacuum` applies finite words on the exact common domain, starting from
  the same selected domain vacuum; every word remains in that domain.
- `scalarWightmanFieldPolynomialVacuumSubmodule` is the complex Hilbert-space span of all such word
  vectors, and it contains the selected nonzero vacuum through the empty word.
- `ScalarWightmanVacuumCyclicity` requires the topological closure of that exact submodule to be the
  whole physical Hilbert carrier.
- Hostile probes expose empty, field, adjoint, and explicit-bump singleton words, reject a bottom
  span, and reject any Hilbert vector outside the closure under cyclicity.
- No cyclic field datum inhabitant, locality, spectrum, reconstruction, existence theorem, or mass
  gap is constructed.

## 2026-07-18 — one-hundred-fourth stone: scalar Wightman locality

Implemented and verified:

- `spacelikeSeparatedPointPairSet` uses the exact mostly-minus quadratic form and is proved open.
- `HaveSpacelikeSeparatedTopologicalSupports` quantifies over the actual topological supports of two
  Minkowski Schwartz tests and is proved symmetric.
- Continuity, product neighborhoods, and finite-dimensional smooth bump existence produce two
  nonzero spacelike-separated tests in every spacetime dimension at least two.
- `oneDimensional_spacelikeSeparatedPointPairSet_eq_empty` exposes the lower-dimensional boundary:
  with no spatial coordinate, dimension one has no spacelike point pair.
- `ScalarWightmanLocalityData` requires scalar bosonic commutation for field-field, field-adjoint,
  adjoint-field, and adjoint-adjoint pairs on the exact common domain.
- Hostile probes expose nonzero test pairs in dimensions two and four, all four commutators, and
  rejection of a disconnected replacement product.
- No local field datum inhabitant, spectrum, reconstruction, existence theorem, or mass gap is
  constructed.

## 2026-07-18 — one-hundred-fifth stone: physical joint translation spectrum

Implemented and verified:

- Streater–Wightman printed p. 92 was visually verified as the exact SNAG/PVM source: one
  momentum-space PVM, intersection multiplication, strong disjoint countable additivity,
  normalization, and `U(a)=∫exp(i p·a)dE(p)`.
- `ProjectionValuedMeasureData` packages self-adjoint idempotents, exact empty/universal values,
  measurable intersection multiplication, and strong countable additivity.
- `JointTranslationSpectralData` supplies finite diagonal measures exactly coherent with that PVM;
  a genuinely integrable mostly-minus momentum character reproduces the exact physical translation
  unitary, and the full Poincaré representation transports the PVM by the projected Lorentz action,
  preventing a disconnected energy surrogate or nonintegrable-zero shortcut.
- `ForwardConeJointTranslationSpectrumData` kills the projection outside the closed future cone.
- `HasPhysicalJointSpectralMassGap` makes the zero-momentum projection exactly the selected
  normalized vacuum line, excludes every nonzero future momentum below `Δ²`, requires `Δ > 0`, and
  requires a nonzero bounded positive-energy excitation band above `Δ`.
- The normalized Hamiltonian spectral view is the energy-coordinate pushforward of the same PVM;
  its exact `(0, Δ)` projection vanishes, its bounded excitation band is nonzero, and the latter also
  yields a finite invariant-mass scale.
- The finite excitation guard rejects a vacuum-only/infinite-gap spectrum and implements the Clay
  statement's `m < ∞` anti-vacuity requirement.
- Hostile probes expose exact PVM laws, strong sums, diagonal coherence, character integrability,
  negative-time rejection, vacuum projection, Hamiltonian and invariant subgap rejection, finite
  excitation, empty/full/vacuum-only families, an unrelated representation, and a nonpositive
  threshold.
- No PVM, spectrum, threshold, quantum theory, existence theorem, or mass gap witness is
  constructed.

## 2026-07-18 — one-hundred-sixth stone: integrated scalar Wightman axiom surface

Implemented and verified:

- `ScalarWightmanAxiomSurfaceData` wires covariance, cyclicity, scalar bosonic locality, and
  forward-cone joint spectrum to one exact field/common-domain/vacuum/representation chain.
- `ScalarWightmanAxiomSurfaceData.HasPhysicalMassGap` specializes the optional physical gap
  predicate to that surface's exact vacuum and PVM rather than adding a gap to the Wightman axioms.
- Hostile probes expose every exact component, the same-representation SNAG formula, positivity and
  Hamiltonian consequences of an optional gap, and rejection of a nonpositive optional threshold.
- Gauge-invariant observable interpretation and Euclidean reconstruction coherence remain explicit
  downstream obligations.
- No scalar Wightman surface, PVM, threshold, quantum theory, existence theorem, or mass-gap witness
  is constructed.

## 2026-07-18 — one-hundred-seventh stone: finite physical mass-gap supremum

Implemented and verified:

- `IsClayHamiltonianGapThreshold` is source-facing: `Δ > 0`, exact zero-momentum vacuum-line
  projection, and no same-PVM Hamiltonian spectrum in `(0, Δ)`; it does not include the stronger
  invariant-mass or bounded-excitation guards.
- `physicalGapThresholdSet` is exactly the set of those source-facing Hamiltonian thresholds.
- `physicalMassGapValue` is the real supremum of that exact threshold set, matching Clay p. 6 §4.
- Any one stronger physical joint gap makes the source-facing set nonempty; its separately required
  nonzero bounded-energy band uniformly bounds every source-facing threshold.
- Therefore any stronger physical joint gap yields `HasFinitePositivePhysicalMassGap`: the set is
  nonempty and bounded above and its exact supremum is positive.
- Hostile probes lock the mass definition to `sSup` and prove that a vacuum-only spectrum admits all
  positive Hamiltonian intervals, making the source-facing threshold set unbounded rather than
  artificially empty.
- No admissible threshold, spectrum, quantum theory, Yang–Mills existence theorem, or mass-gap
  witness is constructed.

## 2026-07-18 — one-hundred-eighth stone: algebraic smeared Wightman correlators

Implemented and verified:

- `scalarWightmanVacuumWordExpectation` pairs the exact selected vacuum with an exact finite
  field/adjoint word acting on the exact common-domain vacuum.
- `scalarWightmanVacuumExpectation` specializes to ordered field-only tests with the list head as
  the leftmost/outermost operator.
- Arity zero is exactly one by vacuum normalization; singleton values equal the exact coherent
  tempered matrix element; pair values lock `Φ(f) Φ(g) Ω` order.
- Hostile probes reject an identically-zero family and a swapped pair when ordered matrix elements
  differ, and route the explicit nonzero Minkowski bump through the exact singleton value.
- Joint `n`-point temperedness, tube analyticity, Euclidean continuation, and reconstruction remain
  explicit downstream obligations.
- No independent jointly distributional correlator datum, field inhabitant, quantum theory,
  existence theorem, or mass-gap witness is constructed.

## 2026-07-18 — one-hundred-ninth stone: finite-configuration Schwartz pure tensors

Implemented and verified:

- `Mathematics.finiteConfigurationSplit` and its inverse split exact `Fin (n+m)` coordinate blocks
  without selecting Euclidean or Minkowski semantics.
- `scalarSchwartzTensorProductOnFiniteConfiguration` packages the exact concatenated product as an
  actual full-configuration Schwartz test.
- `scalarZeroConfigurationSchwartz` and `scalarOneConfigurationSchwartz` provide exact unit and
  one-point stages.
- `scalarSchwartzPureTensor` recursively packages every finite family of one-point Schwartz tests;
  its evaluation is proved equal to the exact coordinatewise finite product.
- Hostile probes lock block offsets, split/merge inversion, unit arity, coordinate order, and reject
  an unrelated replacement value.
- This is signature-neutral reusable mathematics and constructs no Euclidean or Minkowski physical
  datum.

## 2026-07-18 — one-hundred-tenth stone: jointly tempered Wightman correlator interface

Implemented and verified:

- `ScalarMinkowskiNPointSchwartzTestFunction` is the actual full-product Schwartz carrier
  `𝓢(Fin n → Spacetime d, ℂ)` at every arity.
- `ScalarWightmanJointTemperedCorrelatorData.nPointDistribution` requires one actual Mathlib
  tempered distribution on that carrier for every `n`.
- `pureTensor_coherent` ties every distribution to the exact ordered algebraic field-word vacuum
  expectation on every finite pure Schwartz tensor.
- Zero arity evaluates the exact scalar unit to one; arity one recovers the coherent tempered matrix
  element; arity two locks `Φ(f) Φ(g) Ω` order.
- Hostile probes reject an identically-zero family and a disconnected distribution value.
- Tube analyticity, boundary-value semantics, Euclidean continuation, and reconstruction remain
  explicit downstream obligations.
- No jointly tempered correlator datum, field inhabitant, quantum theory, existence theorem, or
  mass-gap witness is constructed.

## 2026-07-18 — one-hundred-eleventh stone: Wightman backward-tube geometry

Implemented and verified:

- `ComplexifiedSpacetime` remains a complexification of the Minkowski coordinate carrier, not an
  identification with Euclidean spacetime.
- `openForwardMomentumCone` uses strict positive time and strict positive mostly-minus invariant
  square and is proved open.
- `wightmanBackwardTube` preserves Streater–Wightman's exact `ξ - iη`, `η ∈ V₊°` sign and is proved
  open at every finite relative-coordinate arity.
- An explicit negative-imaginary unit-time point proves nonemptiness in all dimensions 1–4,
  including dimension one.
- Hostile probes reject zero at positive arity and the reversed positive-imaginary sign.
- No holomorphic function, polynomial bound, boundary value, continuation, reconstruction,
  correlator inhabitant, or physical theory is constructed.

## 2026-07-18 — one-hundred-twelfth stone: Wightman tube boundary-value interface

Implemented and verified:

- `wightmanForwardDirectionSet` is the open domain of all coordinatewise strict future imaginary
  directions.
- Positive standard directions remain in that domain at every scale and genuinely tend to zero;
  the boundary filter is proved `NeBot`, and at positive arity the standard ray consists of nonzero
  strict directions. Arity zero retains its expected singleton direction carrier.
- `wightmanTubeApproachPoint` sends every real relative configuration and admissible direction to
  the exact negative-imaginary backward tube.
- `WightmanTubeBoundaryValueData` requires a genuinely holomorphic function, actual tempered
  approximants, integrability of every tube-function/Schwartz pairing, exact integral coherence,
  and convergence to the selected boundary distribution as all direction tuples jointly tend to
  zero.
- Hostile probes reject a disconnected regularized value and expose every analytic and convergence
  field.
- Relative-coordinate correlator coherence, polynomial bounds, extended-tube continuation,
  reconstruction, and every analytic inhabitant remain pending.

## 2026-07-18 — one-hundred-thirteenth stone: Wightman tube polynomial growth

Implemented and verified:

- `IsPolynomiallyBoundedOnWightmanTube` requires one radial bound `C(1+‖ξ‖)^N`, `C ≥ 0`, uniformly
  while the strict imaginary direction ranges over any chosen compact subset.
- `PolynomiallyBoundedWightmanTubeBoundaryValueData` extends the exact same holomorphic tube
  function and weak distributional boundary data with that growth requirement.
- Every singleton strict direction, including the explicit unit-time direction, receives a concrete
  polynomial bound.
- Hostile probes expose compact-direction uniformity and prove that the certified bound cannot be
  undersized anywhere on its covered compact direction set.
- The radial form is an explicit project normal form for the same finite-dimensional growth class
  as Streater–Wightman's arbitrary polynomial `P_K`; both comparison directions remain pending and
  no definitional identification is claimed.
- No polynomially bounded analytic datum, boundary value, correlator inhabitant, reconstruction, or
  physical theory is constructed.

## 2026-07-18 — one-hundred-fourteenth stone: consecutive-difference/anchor coordinates

Implemented and verified:

- `Mathematics.consecutiveDifferenceAnchorLinearEquiv` identifies an `(n+1)`-point configuration
  with exact differences `xᵢ-xᵢ₊₁` and the final anchor `xₙ`.
- Reverse-inductive reconstruction is proved to be its exact inverse, then promoted by finite
  dimensionality to a continuous linear equivalence.
- `relativeAnchorSchwartzLift` pulls a relative Schwartz test times an anchor Schwartz test back to
  one actual full-configuration Schwartz test with exact product evaluation.
- Hostile probes lock difference signs, final-anchor choice, reconstruction, common-translation
  invariance of differences, anchor translation, and reject an unrelated lifted value.
- This is signature-neutral reusable mathematics and makes no physical translation-invariance or
  reconstruction claim.

## 2026-07-18 — one-hundred-fifteenth stone: relative analytic Wightman correlators

Implemented and verified:

- `ScalarWightmanRelativeAnalyticCorrelatorData` packages one relative tempered distribution at
  every difference arity for the exact existing full correlator family.
- A selected anchor Schwartz test has exact coordinate-Lebesgue integral one, preventing an empty
  normalization domain; it is proved nonzero by hostile probe.
- `full_relative_coherent` requires the full `(n+1)`-point distribution on the exact
  consecutive-difference/anchor lift to equal the relative distribution for every normalized
  anchor, not merely the selected witness.
- Normalized-anchor independence is derived from that exact common relative value.
- `analyticBoundary` uses the exact relative distribution as the polynomially bounded
  all-direction weak tube boundary at every arity.
- Hostile probes reject a disconnected relative value and expose the full-to-relative-to-analytic
  chain.
- Coordinate Haar/Lebesgue volume is not called Riemannian volume. No anchor, relative distribution,
  analytic datum, correlator inhabitant, reconstruction, or physical theory is constructed.

## 2026-07-18 — one-hundred-sixteenth stone: reverse Wick-rotation geometry

Implemented and verified:

- `Reconstruction.reverseWickRotateEuclideanConfiguration` explicitly reverses Euclidean point
  labels and maps only the distinguished time coordinate by `τ ↦ -iτ`; spatial coordinates remain
  real.
- `reverseWickRotatedRelativeCoordinates` forms exact consecutive differences after that reversal.
- Strictly increasing Euclidean times become strictly positive reversed time differences, and every
  resulting relative coordinate is proved to lie in the exact Wightman backward tube.
- Explicit standard strict Euclidean configurations make the bridge nonvacuous in dimensions one
  and four.
- Hostile probes lock time/spatial formulas and relative imaginary sign, and prove concretely that
  omitting reversal rejects the explicit strict two-point configuration from the backward tube.
- This is geometry only: no Euclidean/Minkowski correlator equality, analytic continuation theorem,
  OS reconstruction, theory inhabitant, or mass-gap witness is constructed.

## 2026-07-18 — one-hundred-seventeenth stone: strict ordered Wick continuation

Implemented and verified:

- `MathlibStrictOrderedScalarWickContinuationData` connects one exact Euclidean Schwinger family to
  one exact relative analytic Wightman chain.
- At every positive arity and every current strict positive-time ordered/flat test, the reverse-Wick
  analytic integrand is required genuinely integrable.
- The Euclidean tempered-distribution value is exactly that coordinate-Lebesgue/Haar integral of
  the same polynomially bounded Wightman tube function.
- Kernel-visible support lemmas prove every nonzero test value maps into the holomorphy tube and the
  integrand vanishes outside its preimage.
- OS-I `(5.2)` initially uses compactly supported tests in the noncoincident region; requiring
  absolute integrability for every potentially noncompact strict Schwartz test is an explicit
  strengthening. Reversal is justified by the source's analytic permutation symmetry before
  `(5.1)`, not attributed to `(5.1)` itself.
- The explicit nonzero arity-one positive-time bump exercises the continuation interface.
- Hostile probes reject a disconnected continuation value and prevent Mathlib's
  nonintegrable-zero convention from satisfying coherence silently.
- The current carrier is stronger than OS-I's printed derivative-vanishing ordered space. No
  source-carrier density/topology/completion comparison, full distribution equality, Hilbert
  reconstruction, continuation inhabitant, theory, or mass-gap witness is constructed.

## 2026-07-18 — one-hundred-eighteenth stone: finite periodic lattice gauge action

Implemented and verified:

- `Lattice.FinitePeriodicLattice` encodes a nonempty successor extent on every dimension-indexed
  periodic axis; one-site periodicity and distinct-direction shift commutation are proved.
- `GaugeField` stores group elements on positive oriented bonds, while `gaugeTransform` uses exact
  base/forward-endpoint multiplication.
- `plaquetteHolonomy` uses the ordered four-link product and is proved to transform by base-point
  conjugation.
- `PlaquettePotentialData` avoids a fake canonical matrix trace by requiring an explicit
  nonnegative, identity-normalized, conjugation- and inversion-invariant class potential; a
  nontriviality witness blocks the identically-zero density.
- Plaquette direction reversal is proved to invert holonomy, and the potential is therefore
  orientation-independent.
- `LatticeCouplingData` requires a strictly positive coefficient. The finite Wilson-type action is
  unconditionally gauge invariant and nonnegative; the identity field has zero action.
- Dimension two has a genuine plaquette direction pair, while dimension one has none and its
  plaquette action is identically zero.
- No compactness/Haar structure, Gibbs measure, lattice reflection positivity, continuum limit,
  confinement, lattice-to-OS bridge, theory, or Clay mass gap is constructed.

## 2026-07-18 — one-hundred-nineteenth stone: finite Wilson-loop observables

Implemented and verified:

- `Lattice.SignedDirection` and `stepEndpoint` describe exact forward/backward periodic traversal;
  backward link values use the inverse positive link at the preceding vertex.
- `pathEndpoint` and `pathHolonomy` preserve ordered path composition, and holonomy is proved to
  transform only at the initial/final endpoints.
- `GaugeInvariantClassObservable` requires a nonconstant conjugation-class function without
  imposing a fake canonical representation trace. This does not yet prove that every induced
  function of gauge fields is nonconstant.
- Every closed-loop observable is proved locally gauge invariant.
- The explicit nonempty four-step plaquette path is closed and its path holonomy is exactly the
  independently defined plaquette holonomy, preventing reliance only on the trivial empty loop.
- No Gibbs expectation, area law, confinement result, reflection positivity, continuum observable
  interpretation, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-twentieth stone: finite Gibbs acceptance interface

Implemented and verified:

- `latticeBoltzmannWeight` is the `ENNReal` exponential density of the exact finite Wilson-type
  action and is proved strictly positive at every configuration, with identity value one.
- `latticePartitionFunction` is the exact `lintegral` against a supplied finite-cutoff reference.
- `normalizedLatticeGibbsMeasure` is the exact inverse-partition scaling of `withDensity`.
- `FiniteLatticeGibbsMeasureData` requires reference probability normalization, measurability, and
  exact local gauge invariance on the same action/reference chain. Partition positivity/finiteness,
  Gibbs probability, and Gibbs invariance are now derived from those fields.
- `FiniteLatticeObservable` requires measurability and a uniform norm bound; actual Bochner
  integrability under the Gibbs probability is proved before `finiteLatticeExpectation` is defined.
- Hostile probes reject zero density, zero reference/Gibbs measures, zero/infinite partition
  functions, and nonintegrable-observable shortcuts.
- The generic interface itself constructs no Gibbs datum, expectation value, lattice positivity,
  continuum theory, or mass gap.

## 2026-07-18 — one-hundred-twenty-first stone: exact finite product Haar reference

Implemented and verified:

- `normalizedCompactHaarMeasure` probability-normalizes Mathlib's chosen Haar measure using compact
  finiteness and nonzeroness while retaining the exact Haar property.
- Compact Haar uniqueness proves right invariance from normalized left invariance; inversion
  invariance is then proved on the same measure.
- `finiteGaugeFieldProductHaarMeasure` is definitionally `Measure.pi` over the finite positive-link
  type. Its total mass and every coordinate marginal are proved exactly.
- `linkGaugeMap_measurePreserving` and `gaugeTransform_measurePreserving_productHaar` derive local
  gauge invariance coordinatewise from the same left/right Haar measure.
- `FiniteProductHaarGibbsMeasureData` fixes the generic reference definitionally to this product and
  asks only for measurability of the exact Boltzmann density.
- Everywhere positivity and the action bound `weight ≤ 1` derive positive finite partition
  function; `withDensity` normalization and measure-preserving density invariance derive Gibbs
  probability and gauge invariance rather than accepting disconnected fields.
- Hostile probes expose an explicit positive link, exact Haar marginal, zero-measure exclusions,
  exact specialized reference, unrelated-reference rejection, and all derived Gibbs laws.
- No concrete compact-simple gauge-group certificate, measurable potential datum, Gibbs datum,
  evaluated expectation, reflection positivity, continuum limit, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-twenty-second stone: support-local Wilson-loop expectations

Implemented and verified:

- `orientedStepPositiveLink` identifies the exact positive link read by forward or backward signed
  traversal; `pathLinkSupport` recursively records the finite support of a based path.
- `pathHolonomy_eq_of_eq_on_pathLinkSupport` proves arbitrary changes outside that support cannot
  alter holonomy.
- Signed-link and finite-path holonomy measurability are proved from exact product evaluations and
  measurable group operations.
- `BoundedMeasurableGaugeInvariantClassObservable` strengthens the algebraic nonconstant class
  function with source-facing boundedness and measurability evidence.
- `finiteWilsonLoopObservable` is a genuine `FiniteLatticeObservable`, remains support-local, and is
  gauge invariant on exactly closed paths.
- `finiteProductHaarWilsonLoopExpectation` requires the same specialized Gibbs datum and an explicit
  closure proof; integrability is proved before taking the Bochner integral.
- Hostile probes expose forward/backward singleton support, nonempty plaquette support, outside-
  support insensitivity, actual measurability/integrability, and a concrete two-site open path.
- No bounded class-observable datum, potential-measurability datum, Gibbs datum, evaluated
  expectation, area law, reflection-positivity datum, continuum interpretation, theory, or mass gap
  is constructed.

## 2026-07-18 — one-hundred-twenty-third stone: finite lattice time reflection and positivity checker

Implemented and verified:

- `FiniteLatticeTimeReflectionGeometry` selects a time coordinate and an even periodic extent with
  two separated reflection planes.
- Vertex reflection `t ↦ -t` is involutive; forward time shifts reflect to backward shifts while
  spatial shifts commute with reflection.
- `timeReflectGaugeField` reads time-oriented links by inverse reflected-endpoint links and spatial
  links at reflected bases. It is measurable, involutive, and exactly covariant with reflected local
  gauge transformations.
- Strict positive-time vertices and links lie between the two finite-periodic reflection planes;
  six-site probes construct actual positive time and spatial links and show reflection is nonidentity.
- `FiniteSupportedGaugeInvariantLatticeObservable` records a designated sufficient syntactic
  support, bounded measurability, and local gauge invariance; no semantic minimality is claimed.
- `finiteLatticeReflectionSquareObservable` is proved integrable before
  `finiteLatticeReflectionPairing` takes the same specialized Gibbs expectation.
- `FiniteLatticeReflectionPositivityData` requires reflection invariance and real nonnegative
  pairings for all designated positive-supported tests, plus a test that genuinely changes when one
  listed strict-positive link alone is changed, blocking fake support on constants.
- This checker is definitionally separate from continuum OS `(E2)` and requires a future explicit
  continuum bridge.
- No reflection-positivity datum, transfer matrix, Hamiltonian, continuum limit, theory, or mass gap
  is constructed.

## 2026-07-18 — one-hundred-twenty-fourth stone: lattice scaling trajectories

Implemented and verified:

- `FiniteLatticeScalingTrajectoryData` indexes an exact periodic lattice, positive spacing,
  plaquette potential, action coefficient, bare gauge coupling and product-Haar Gibbs datum at every
  natural cutoff.
- The bare gauge coupling is kept distinct from the action coefficient and tied by an explicit
  positive injective normalization convention.
- Spacing and bare coupling must tend to zero, while sites per axis and physical linear extent tend to
  infinity; fixed-cutoff, bounded-volume and constant-positive-coupling probes derive contradictions.
- `scalingTrajectoryExpectation` uses each stage's exact same-chain Gibbs measure.
- `LatticeToContinuumObservableExpectationBridgeData` takes an independently supplied target
  carrier/functional and requires genuine expectation convergence rather than definitional
  identification.
- Exact unit approximants and an actual one-link-dependent nontrivial approximant block empty or
  constant-only bridges; uniqueness of limits blocks unrelated target values.
- The interface records Wilson's warning that `a → 0` is difficult and OS's statement that general
  infinite volume was open; OS's explicit two-dimensional scaling is model evidence only.
- No trajectory, continuum target, measure/field convergence, renormalization theorem, OS/Wightman
  identification, continuum theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-twenty-fifth stone: weak bilocal local-observable products

Implemented and verified:

- `TemperedLocalObservableFamilyData` indexes labeled local smeared operators on one exact common
  invariant domain and coherent tempered matrix elements for every ordered domain-vector pair.
- The unit label is exactly the identity operator smeared by `minkowskiSchwartzIntegral`; a normalized
  test proves it acts identically rather than vanishing through normalization.
- A distinct label and nonzero operator witness reject empty, singleton/unit-only and zero families.
- `WeakTemperedBilocalObservableProductData` assigns an actual full two-configuration tempered
  distribution to every ordered label/vector tuple.
- Pure-tensor coherence fixes exact `A(f)` after `B(g)` operator order, matching Wilson's weak
  matrix-element formulation; a nonzero product witness rejects the zero distribution family.
- Hostile probes expose the exact unit, local matrix-element coherence, operator order, nonzero full
  distribution and rejection of a candidate disagreeing on one pure tensor.
- This prerequisite still does not interpret labels as gauge-invariant curvature polynomials or
  impose covariance/locality family-wide.

## 2026-07-18 — one-hundred-twenty-sixth stone: generic weak finite-order OPE checker

Implemented and verified:

- `WeakBilocalDiagonalProbeData` packages full bilocal Schwartz tests with integral one, one compact
  first-anchor region, relative support bounded by a fixed positive constant times `r`, support
  shrinking to the diagonal as `r → 0+`, and a fixed dimension/order polynomial seminorm envelope.
- Derived/probe theorems reject eventually zero tests, empty anchor compacts and support uniformly
  separated from the diagonal; linear scale control prevents arbitrary slow reparameterizations
  from making order powers meaningless, while seminorm control blocks arbitrarily amplified
  zero-integral additions.
- Reusable `BilocalDifferenceFirstAnchor` mathematics fixes `(x,y) ↦ (x-y,x)` and its Schwartz lift,
  rejecting the previously available final-anchor convention for Wilson's `C(x-y) O(x)` formula.
- `TemperedRelativeAnchorContractionData` is a nondegenerate bilinear contraction of relative
  coefficient and local-field tempered distributions, fixed exactly on relative/first-anchor pure
  tests.
- `WeakOperatorProductExpansionData` supplies relative tempered coefficients, finite monotone output
  truncations, and exact full-product remainders tied to the same ordered bilocal distributions and
  local-field matrix elements.
- Every order-`N` remainder is little-`o(r^N)` against every normalized compact-anchor probe and
  every ordered domain-vector matrix element.
- Every accepted OPE carries a designated normalized probe, so universal probe asymptotics cannot
  pass through an empty probe type.
- A nonzero zeroth-order coefficient is tied to a nonzero same-label local matrix element and hence
  a nonzero contracted term. Every nonzero coefficient eventually enters a truncation; hostile
  probes reject zero contractions, unused metadata and unrelated remainders.
- Natural powers are an explicit finite-order convention while generic tempered coefficients can
  retain Wilson's fractional/logarithmic singular behavior.
- No probe, contraction, OPE datum, curvature-polynomial interpretation, prescribed
  asymptotic-freedom singularity, stress tensor, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-twenty-seventh stone: covariant local-observable family surface

Implemented and verified:

- The local-family nontrivial witness now requires both nonzero action and action genuinely different
  from the exact unit field, blocking duplicate labels with identical operators.
- `CovariantLocalObservableFamilyData` adds an involutive label adjoint fixing the unit and an exact
  conjugated-test common-domain adjoint relation.
- Every label transforms with the same Poincaré lift projection, restricted domain unitary and exact
  inverse-affine scalar test pullback already used by the scalar Wightman field.
- Every ordered label pair commutes on the same domain for spacelike-separated closed topological
  test supports.
- Hostile probes force covariance on the nontrivial label, two-way adjoint closure, the same exact
  adjoint matrix-element chain and all-label locality; dimensions at least two exercise locality on
  explicit nonzero separated tests.
- No local-observable family datum, curvature-polynomial/gauge interpretation, family cyclicity,
  prescribed OPE singularity, stress tensor, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-twenty-eighth stone: one-dimensional boundary facts

Implemented and verified:

- Every continuous real alternating degree-two map on exact one-dimensional spacetime is proved
  zero by the `Fin 2` linear-dependence/finrank obstruction.
- `OneDimensionalKinematicBoundaryData` packages the absence of a spatial clustering direction,
  spacelike point pairs and nonzero separated tests, while retaining a nonempty Wightman backward
  tube.
- Production lattice theorems now prove there are no ordered plaquette directions and every
  dimension-one Wilson-type plaquette action vanishes for every field/potential/coupling.
- `OneDimensionalLatticeBoundaryData` packages those exact facts without a model witness.
- An explicit one-site forward path is closed and has exact holonomy `u`; conditional on `u ≠ 1`, a
  hostile probe shows zero local plaquette action does not erase nonidentity global holonomy around
  that periodic loop; no winding or homotopy statement is made.
- A direct index probe rejects identifying dimension one with the four-dimensional Clay endpoint.
- These are derived boundary facts only: no one-dimensional quantum theory, lower-to-four
  coercion, existence theorem, or mass gap is constructed.

## 2026-07-18 — one-hundred-twenty-ninth stone: local stress-energy tensor interface

Implemented and verified:

- `minkowskiSchwartzCoordinateDerivative` supplies exact Schwartz directional derivatives along the
  canonical spacetime basis.
- Explicit inverse-Lorentz matrix coefficients fix a project contravariant rank-two component
  convention matching `U(g)T(f)U(g)⁻¹` and the inverse-affine test pullback.
- `LocalStressEnergyTensorData` selects every `T^{μν}` as a label in the same tempered local-
  observable family/common-domain/Poincaré chain.
- Components are symmetric at label/operator level, Hermitian on conjugated tests, local relative to
  every label in the same family, transform by the exact rank-two Lorentz sum, and satisfy weak
  distributional conservation.
- Each component inherits the same family's coherent tempered matrix elements.
- The `T^{00}` energy-density label must differ from the unit and act both nontrivially and
  differently from the unit on an exact test/domain vector.
- Hostile probes independently expose the coordinate derivative, inverse Lorentz entries,
  inverse-affine pullback, locality, symmetry, adjointness, tensor covariance, conservation, tempered
  coherence, and rejection of zero/unit energy-density surrogates.
- The standard gauge-theory symmetry/conservation semantics are pinned to
  Blaschke–Gieres–Reboud–Schweda 2016; Streater–Wightman supplies quantum component covariance,
  locality, common-domain, and adjoint semantics.
- The rank-two convention is an explicit formalization decision beyond Clay's printed existence
  request. No tensor datum, trace/trace-anomaly semantics, renormalization theorem, theory, or mass
  gap is constructed.

## 2026-07-18 — one-hundred-thirtieth stone: stress-energy translation Ward bridge

Implemented and verified:

- `StressTensorChargeCutoffData` makes the formal spatial charge integral honest through exact
  spacetime Schwartz products.
- Integral-one temporal profiles have shrinking support and converge on every Schwartz test to the
  time-zero delta distribution, excluding derivative-contaminated mollifiers.
- Real nonnegative spatial profiles are bounded by one, equal one on expanding norm balls, and have
  support controlled by twice the plateau radius.
- `LocalStressEnergyTranslationWardData` supplies common-domain Hermitian momentum generators with
  integrable diagonal first moments equal to those of the exact same physical joint PVM.
- The exact same generators differentiate the exact same physical translation unitaries with
  independently probed `+i` time and `-i` spatial mostly-minus signs.
- Controlled strong limits of the same stress tensor's `T^{0ν}` components equal those generators on
  every common-domain vector.
- Every label in the same local-observable family obeys the corresponding infinitesimal translation
  Ward identity, with the sign fixed by the inverse-affine test pullback.
- A nonzero time generator and zero-regulator hostile probes block trivial/disconnected surrogates.
- Blaschke–Gieres–Reboud–Schweda equation `(2.2)` sources the classical charge/generator relation;
  the regulator, same-PVM, common-domain and all-family quantum formulation is explicitly classified
  as a project strengthening informed by the pinned Wightman/SNAG chain.
- No cutoff sequence, generator, Ward datum, tensor, trace anomaly, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-first stone: basic curvature-squared interpretation

Implemented and verified:

- `BasicCurvatureObservableTag` deliberately contains only the normalized unit and curvature squared.
- `basicClassicalCurvatureObservable` makes `F²` definitionally equal to the basis-free canonical
  density of the exact metric, invariant pairing, connection, exterior derivative, curvature
  certificate, and descent chain.
- `CurvatureSquaredLocalObservableInterpretationData` places both tags in one exact tempered local-
  observable family/common quantum domain.
- A designated classical base point prevents empty-base vacuity, and every classical tangent finrank
  must equal the exact quantum spacetime dimension.
- The selected quantum unit is the family's normalized unit; the `F²` label is distinct and acts both
  nontrivially and differently from the unit on one exact test/domain vector.
- Hostile probes expose the exact classical density, designated-point dimension equation, normalized
  unit, and rejection of zero/duplicate-unit `F²` interpretations.
- In accordance with Clay footnote 1, no global injective classical-polynomial-to-quantum-field map is
  claimed. “Gauge-invariant” remains the intended source interpretation through curvature descent
  and invariant pairing; gauge transformations of connections are not yet formalized here.
- Arbitrary curvature polynomials, covariant derivatives, operator mixing, quantization, a theory,
  and a mass gap remain unconstructed.

## 2026-07-18 — one-hundred-thirty-second stone: curvature-derivative tensor carrier

Implemented and verified:

- `AdjointBundle.fiberIsTopologicalAddGroup` and `fiberContinuousSMul` prove that the exact
  quotient-derived dependent-fiber topology is compatible with its transported addition, negation,
  and real scalar multiplication.
- The proofs use the exact selected quotient coordinate as a continuous linear equivalence and
  introduce only named locally installed structures, not global fiber instances.
- `AdjointBundle.CurvatureDerivativeTensor n` has `n` continuous multilinear derivative slots and
  retains two continuous alternating curvature slots valued in the exact dependent adjoint fiber.
- `toCurvatureDerivativeTensorZero` embeds any exact adjoint-valued two-form in the unique
  zero-derivative-slot carrier.
- `PrincipalConnectionData.curvatureDerivativeTensorZero` specializes that embedding definitionally
  to the same smoothly descended curvature indexed by the exact connection, exterior derivative,
  and structural certificate.
- Hostile probes expose joint operation continuity, coordinate coherence, both derivative- and
  curvature-slot continuity, repeated-curvature-slot vanishing, exact zero-order evaluation,
  empty-argument uniqueness, and rejection of an unrelated zero-order curvature anchor.
- No positive-order tensor, recursive tower law, Bianchi theorem, polynomial grammar, quantum
  interpretation, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-third stone: same-connection adjoint-section derivative

Implemented and verified:

- `AdjointBundle.CovariantDerivative` specializes Mathlib's bundled covariant-derivative carrier to
  the exact dependent adjoint bundle with all topology/module/fiber-bundle structures installed
  locally.
- `adjointLocalSectionCoordinate`, `adjointLocalOrdinaryDerivative`, and
  `adjointLocalConnectionBracketTerm` keep the fixed-chart ordinary derivative and exact principal-
  connection correction separately visible.
- `adjointLocalCovariantDerivativeExpression` is definitionally their plus-sign sum
  `dσ(X) + [A(X),σ]`, matching the project's right-`Ad(g⁻¹)` associated-bundle convention.
- `PrincipalConnectionAdjointCovariantDerivativeData` requires Mathlib additivity/Leibniz laws and
  the exact local formula for every smooth adjoint section, designated principal chart, in-chart
  base point, and tangent vector.
- The source locator correctly distinguishes Freed's numbered Bianchi equation `(1.16)` from the
  unnumbered `d_Θ = d + ad(Θ)` definition immediately following it.
- Hostile probes expose the unfolded plus sign, block omission of a nonzero bracket correction,
  reject substitution of a connection with a different local expression, and reject an unrelated
  coordinate derivative value.
- This is an uninhabited degree-zero section-derivative interface. No adjoint-valued-form derivative,
  positive curvature-tensor order, recursive tower, Bianchi theorem, polynomial interpretation,
  theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-fourth stone: smooth adjoint derivative output

Implemented and verified:

- `AdjointBundle.CovariantDerivative.IsSmooth` specializes Mathlib's
  `ContMDiffCovariantDerivative` at `C∞` to the exact named dependent adjoint vector bundle.
- `SmoothPrincipalConnectionAdjointCovariantDerivativeData` strengthens the exact same-connection
  `d + ad(A)` datum with that standard regularity requirement.
- `smooth_output` derives an exact `C∞` total-space section of the derivative bundle from every
  exact smooth adjoint section, including the `∞ + 1 = ∞` input regularity reconciliation.
- The smooth wrapper retains the identical principal connection, derivative carrier, and local
  coordinate formula rather than supplying a disconnected smooth operator.
- A hostile probe rejects packaging a nonsmooth derivative as smooth data while preserving the exact
  underlying same-connection datum.
- This regularity is required acceptance data and is not derived from the local formula alone. No
  derivative inhabitant, adjoint-valued-form extension, positive curvature-tensor order, Bianchi
  theorem, polynomial interpretation, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-fifth stone: proper complex Lorentz kinematics

Implemented and verified:

- `complexMinkowskiBilinearForm` is the exact complex-bilinear, non-Hermitian extension of the
  mostly-minus form.
- `ProperComplexLorentzTransformation` requires a continuous complex-linear automorphism preserving
  that form and having determinant one.
- Identity, composition and inverse are constructed and proved to retain both laws, yielding a named
  group without assuming a transformation-group topology.
- `actConfiguration` gives the exact simultaneous action on every finite relative configuration,
  with multiplication, inversion and fixed-transformation continuity.
- Four-dimensional complex negation is constructed with determinant `(-1)^4 = 1` and proved
  nonidentity, blocking an identity-only surrogate.
- Hostile probes reject determinant-minus-one and form-nonpreserving automorphisms.
- Streater–Wightman supplies the four-dimensional source. Dimensions one through three are explicit
  project consistency infrastructure rather than a verbatim source quantifier.
- “Proper” currently records determinant one only. No group topology, connectedness theorem,
  complex Lie/analytic structure, real-Lorentz embedding, continuation datum, theory, or mass gap is
  constructed.

## 2026-07-18 — one-hundred-thirty-sixth stone: extended-tube orbit geometry

Implemented and verified:

- `wightmanExtendedTube` is definitionally the union of all simultaneous proper-complex-Lorentz
  images of the exact ordinary backward tube.
- Membership has an exact transformation/source-point witness rather than an unrelated enlarged set.
- Each orbit image equals an inverse-action preimage, so fixed-action continuity proves every image
  open and the full orbit open.
- Identity gives ordinary-tube inclusion and nonemptiness; group multiplication proves exact orbit
  invariance.
- Invertibility keeps zero outside the extended tube at every positive arity.
- Four-dimensional complex negation maps the standard tube point into the extended orbit but outside
  the original backward tube, proving strict enlargement and blocking a fixed-tube surrogate.
- The source is four-dimensional; dimensions one through three remain project consistency
  infrastructure.
- This is domain geometry only. No transformation-group analytic structure, continuation datum,
  correlator datum, theory, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-seventh stone: connected extended-tube continuation interface

Implemented and verified:

- `PolynomiallyBoundedWightmanExtendedTubeContinuationData` requires one ambient function
  holomorphic on the exact extended tube, equal to the exact polynomially bounded ordinary-tube
  function on its original domain, and invariant under proper complex Lorentz transformations.
- Function semantics make the candidate single-valued; restriction plus invariance derive exact
  values at every orbit presentation and presentation independence.
- The explicit four-dimensional point outside the ordinary tube is forced to have the exact
  standard ordinary-source value.
- `ScalarWightmanRelativeExtendedAnalyticCorrelatorData` requires this continuation at every arity
  for exactly `relative.analyticBoundary n`, tying it to the same relative tempered distribution,
  full correlator, field, domain, vacuum and physical representation.
- Hostile probes reject disconnected extension values and unrelated relative boundaries, and expose
  all-arity complex-Lorentz invariance and orbit-source values.
- This packages the scalar conclusion of Streater–Wightman Theorem 2-11 as uninhabited acceptance
  data. It does not derive continuation from ordinary covariance or formalize the source path lemma.
- No transformation-group analytic structure, continuation/correlator datum, theory, or mass gap is
  constructed.

## 2026-07-18 — one-hundred-thirty-eighth stone: perturbative running-coupling normal form

Implemented and verified:

- `PureYangMillsAsymptoticFreedomData` is indexed by an exact compact-simple gauge-group certificate
  and carries an explicit spacetime dimension forced to four by a named equality field.
- The chosen convention is the dimensionless logarithmic scale `t = log(μ/μ₀)` with
  `g′(t)=β(g(t))`.
- Positivity and the exact flow equation are required only on a strict open ultraviolet tail, so no
  two-sided derivative at the threshold or infrared behavior is imposed.
- The same coupling tends to zero at `+∞`; `β(0)=0`; and the small-positive-coupling normal form is
  `β(g)/g³ → -b₀` with `b₀>0`, deriving eventual beta negativity.
- Hostile probes reject lower-dimensional reuse, zero/constant running couplings, eventually
  nonnegative beta functions, and a flow derivative disconnected from the same beta function.
- The exact group certificate currently only indexes the universal sign normal form. The numerical
  adjoint-Casimir/group-dependent coefficient and its invariant-pairing/coupling normalization remain
  explicit debt; no claim is made that this is the full one-loop coefficient.
- No OPE coefficient matching, perturbative series/remainder, infrared or mass-shell statement,
  quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-18 — one-hundred-thirty-ninth stone: supplied weak OPE regular variation

Implemented and verified:

- `normalizedRelativeSchwartzDilationCLM` defines `r⁻ᵈ f(·/r)` exactly at nonzero scale and is
  totalized by zero at the excluded scale; all source-facing limits use `r → 0+`.
- `rescaledOPECoefficient` combines the exact normalized test dilation, `t=-log r`, a signed real
  radial degree, and a real power of the same four-dimensional running coupling.
- `SuppliedWeakOPERegularVariationData` requires every nonzero coefficient of one exact weak OPE to
  converge in Mathlib's pointwise/weak tempered-distribution topology to a nonzero leading
  distribution. Signed degrees permit regular or vanishing coefficients.
- At least one actual nonzero coefficient has a nonzero coupling exponent, blocking a wholly
  disconnected running-coupling decoration.
- Hostile probes expose exact evaluation, inverse-coordinate scaling, scale-zero totalization,
  positive-scale noncollapse, all-coefficient limits, nonzero leaders, four-dimensional scope,
  a signed-degree constructor surface with no nonnegativity premise, negative-degree visibility,
  limit uniqueness, and rejection of all-zero coupling exponents.
- This is explicitly supplied acceptance data, not a consequence of Gross–Wilczek, Politzer, or
  Wilson for an arbitrary local family. It does not calculate group-normalized beta/OPE
  coefficients, anomalous dimensions, operator mixing, scheme dependence, perturbative remainders,
  or identify the labels with curvature-polynomial observables. Clay's prescribed-singularity
  obligation therefore remains open.
- No OPE datum, regular-variation datum, theory, existence theorem, or mass gap is constructed.

## 2026-07-18 — one-hundred-fortieth stone: OS ordered Fréchet candidate

Implemented and verified:

- `IsOSPositiveTimeOrderedDerivativeVanishing` requires every iterated real Fréchet derivative,
  including order zero, to vanish outside strict positive time order.
- `osPositiveTimeOrderedDerivativeSubmodule` proves exact closure under addition and arbitrary
  complex scalar multiplication. `OSPositiveTimeOrderedDerivativeCarrier` is algebraically
  identified with that submodule, installs exactly the topology induced from the ambient Mathlib
  Schwartz carrier, and packages an injective topological forgetful map.
- Every earlier strict topological-support ordered/flat test includes with exactly the same
  underlying Schwartz function; the explicit positive-time bump gives a nonzero arity-one element.
- Coincidence flatness is derived because a coincident configuration cannot be strictly ordered.
- Hostile probes lock the derivative-only constructor surface and complex-linear closure, reject a
  nonzero outside jet,
  preserve the strict inclusion, expose the induced topology, and block zero-only collapse.
- OS-I printed p. 86 was newly visually checked for the multi-index spaces, induced topology, and
  completed-tensor distinction. The Lean carrier is deliberately classified only as a
  project-dimension Fréchet candidate for `S₊`, not the exact source space.
- Exact four-dimensional multi-index equivalence, closedness, proper enlargement beyond strict
  support, finite direct-sum and completed-tensor comparisons, source-facing `(E2)`, and all OS-II
  reconstruction obligations remain open. OS-II's correction of Lemma 8.8 is explicitly recorded.
- No OS sequence, reflection-positive datum, reconstruction, theory, existence theorem, or mass gap
  is constructed.

## 2026-07-18 — one-hundred-forty-first stone: coordinate-basis OS jets

Implemented and verified:

- A reusable theorem, built over Mathlib's `Module.Basis.ext_multilinear`, proves that every
  finite-arity continuous multilinear map is determined by its values on basis tuples, including
  arity zero; a nonzero map therefore has a nonzero basis-tuple evaluation.
- `euclideanNPointCoordinateBasis` is the exact Kronecker basis indexed jointly by point label and
  Euclidean spacetime coordinate.
- `IsOSPositiveTimeOrderedCoordinateJetVanishing` requires every derivative to vanish on every
  ordered tuple of those exact directions outside strict positive time order.
- `osPositiveTimeOrderedFrechet_iff_coordinateJets` proves exact internal equivalence with full
  Fréchet-map vanishing, and `OSPositiveTimeOrderedCoordinateJetCarrier.equivFrechetCarrier`
  preserves the same Schwartz test in both presentations.
- Hostile probes calculate the point/coordinate basis values, detect any nonzero derivative by an
  actual coordinate tuple, lock the carrier identification, and retain the explicit nonzero test.
- This still is not OS-I's printed multi-index equivalence. Exact four-dimensional coordinate
  flattening and the relation between ordered repeated directions, derivative symmetry/multiplicity,
  and `D^α` remain open, as do closedness and every reconstruction obligation.
- No OS sequence, reflection-positive datum, reconstruction, theory, existence theorem, or mass gap
  is constructed.

## 2026-07-19 — one-hundred-forty-second stone: comprehensive audit bibliography

Implemented and verified:

- `docs/AUDIT_BIBLIOGRAPHY.md` now inventories current sources of record and candidate authoritative
  sources selected for acquisition/page audit across every currently planned remaining workstream.
- Thirty-six DOI records were queried directly through the Crossref works API and matched against
  every identity field Crossref supplies; sources without DOIs retain canonical institutional URLs,
  arXiv identifiers or ISBNs rather than invented identifiers. The machine-readable metadata
  snapshot and offline/optional-online verifier are checked in.
- The inventory separates current sources of record, required additions, and conditional sources
  that become relevant only if optional topology, moduli, gauge-fixing or perturbative-convergence
  layers are introduced.
- A coverage matrix maps Bianchi, Hodge/action, OS reconstruction, the genuine Poincaré cover,
  joint spectral measures, extended tubes, operator mixing, beta normalization, trace anomaly,
  two-dimensional consistency and final Clay integration to bounded source chains.
- Online verification corrected plausible but wrong DOI variants for Freed, Ambrose, Driver and
  Gross–King–Sengupta and rejected a nonresolving DOI previously associated with Hall–Wightman.
- The Blaschke–Gieres–Reboud–Schweda source record now includes its verified Nuclear Physics B DOI.
- Bibliography inclusion is explicitly not canonicalization: every new load-bearing source still
  requires an artifact/identity record, page-level inspection and a declaration-level source-map
  row before use.
- No source in the inventory is represented as proving four-dimensional existence or a mass gap.

## 2026-07-19 — one-hundred-forty-third stone: closed OS Fréchet candidate

Implemented and verified:

- Reusable `SchwartzMap.iteratedDirectionalEvaluationCLM` packages any finite ordered real
  directional jet at a point as a continuous complex-linear functional on exact complex Schwartz
  space, and proves exact agreement with `iteratedFDeriv`.
- Every such jet-vanishing kernel is closed. Hostile mathematics probes lock exact evaluation and
  kernel membership and reject a nonzero selected jet.
- `isClosed_osPositiveTimeOrderedDerivativeSubmodule` uses the proved coordinate-jet equivalence to
  identify the dimension-generic candidate with the intersection of all continuous coordinate-jet
  kernels outside strict positive time order.
- `OSPositiveTimeOrderedDerivativeCarrier.closedEmbedding_toSchwartz` upgrades the existing induced
  topological embedding to a closed embedding.
- Hostile limit probes prove every ambient Schwartz limit of accepted tests retains the exact
  derivative-vanishing law and show that one nonzero exterior jet blocks such convergence.
- This proves closedness only for the internal dimension-generic Fréchet candidate. Exact
  four-dimensional coordinate flattening, repeated-direction symmetry and multiplicity, and
  comparison with OS-I's printed `D^α` space remain open; the theorem is not mislabeled as that
  source-space identification.
- No `(E2)` datum, OS-II reconstruction, quantum theory, existence theorem, or mass gap is
  constructed.

## 2026-07-19 — one-hundred-forty-fourth stone: canonical four-dimensional multi-indices

Implemented and verified:

- `fourDimensionalPointCoordinateEquiv` flattens the exact dependent point/coordinate label to
  `Fin (4n)` in point-major order, with the proved arithmetic law `(i, μ) ↦ μ + 4i`.
- `FourDimensionalMultiIndex` is a natural-valued function on that exact flattened coordinate type;
  `fourDimensionalMultiIndexOrder` is its finite sum.
- `fourDimensionalMultiIndexOccurrenceEquiv` identifies the `αᵢ` finite occurrences of every
  coordinate `i` with exactly `|α|` derivative slots. The repeated-coordinate and basis-direction
  maps are proved to return the exact designated coordinate at every occurrence.
- `fourDimensionalMultiIndexDerivative` evaluates the iterated Fréchet derivative on that canonical
  repeated basis tuple, and `IsOSPositiveTimeOrderedMultiIndexVanishing` records its exterior
  vanishing.
- `frechet_implies_fourDimensionalMultiIndexVanishing` proves the established Fréchet candidate
  implies every such canonical four-dimensional multi-index condition.
- Hostile probes lock point-major flattening, every multiplicity occurrence, the exact iterated-
  derivative value, zero-arity evaluation, zero total order, the exact one-way carrier bridge, and
  rejection by any nonzero exterior multi-index jet.
- This is only a partial comparison with OS-I printed p. 86. Permutation symmetry/order
  independence, the converse from arbitrary coordinate tuples, and identification of the canonical
  repeated-basis derivative with the source's recursively interpreted `D^α` remain open.
- No exact OS source-space identity, `(E2)` datum, reconstruction, quantum theory, existence theorem,
  or mass gap is constructed.

## 2026-07-19 — one-hundred-forty-fifth stone: enumerated four-dimensional multi-indices

Implemented and verified:

- `FourDimensionalMultiIndexEnumeration α k` is an exact equivalence from all dependent coordinate
  occurrences `(i, r < αᵢ)` to `Fin k`; its existence prevents a disconnected slot count.
- Every arbitrary ordered coordinate tuple induces `fourDimensionalCoordinateTupleMultiIndex` by
  exact fiber cardinalities and `fourDimensionalCoordinateTupleEnumeration` through
  `Equiv.sigmaFiberEquiv`.
- `fourDimensionalCoordinateTupleEnumeration_recovers` proves the induced enumerated coordinate at
  every slot is exactly the original tuple entry, retaining order and repetitions.
- `IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing` quantifies over every occurrence
  enumeration. It implies the earlier canonical condition.
- `osPositiveTimeOrderedCoordinateJets_iff_enumeratedMultiIndex` and
  `osPositiveTimeOrderedFrechet_iff_enumeratedMultiIndex` prove exact internal equivalence with all
  arbitrary ordered coordinate tuples in four dimensions.
- Hostile probes lock fiber multiplicities, entrywise tuple recovery, exact candidate equivalence,
  retention of the canonical ordering, and rejection by any nonzero arbitrary exterior coordinate
  jet, including rejection of a disconnected carrier surrogate.
- This combinatorial all-enumeration equivalence does not prove higher-derivative permutation
  symmetry or identify one canonical ordering with OS-I's recursively interpreted `D^α`. Those
  analytic and source-syntax comparisons remain open.
- No exact OS source-space identity, `(E2)` datum, reconstruction, quantum theory, existence theorem,
  or mass gap is constructed.

## 2026-07-19 — one-hundred-forty-sixth stone: multi-index permutation independence

Implemented and verified:

- Reusable `SchwartzMap.lineDerivOp_commute` derives exact commutation of two Schwartz directional
  derivatives from Mathlib's symmetric-second-derivative theorem.
- `SchwartzMap.iteratedLineDerivOp_eq_foldr` identifies the recursive operator with the exact fold of
  its finite direction list. Pairwise commutation and `List.Perm.foldr_eq` then prove
  `iteratedLineDerivOp_comp_perm` for every slot permutation.
- `SchwartzMap.iteratedFDeriv_comp_perm` transfers that exact equality to every iterated Fréchet
  value at the designated point. Hostile probes retain the same function, point and tuple and show
  nonzero jets survive permutation.
- Any two four-dimensional multi-index occurrence enumerations are proved related by an explicit
  slot permutation and give the same `fourDimensionalEnumeratedMultiIndexDerivative`.
- Every enumeration's slot count is derived from its actual equivalence and its derivative is proved
  equal to `fourDimensionalMultiIndexDerivative` in the canonical occurrence ordering.
- `osPositiveTimeOrderedCanonicalMultiIndex_iff_enumeratedMultiIndex` and
  `osPositiveTimeOrderedFrechet_iff_canonicalMultiIndex` complete the internal equivalence between
  canonical multi-index, all-enumeration, coordinate-jet and Fréchet candidate predicates.
- Hostile probes lock the exact slot permutation, enumeration independence, canonical value,
  predicate equivalences, and rejection by a nonzero canonical exterior jet.
- The remaining source comparison is narrower but still substantive: the canonical repeated-basis
  derivative has not yet been identified with OS-I printed p. 86's recursively interpreted `D^α`.
- No exact OS source-space identity, `(E2)` datum, reconstruction, quantum theory, existence theorem,
  or mass gap is constructed.

## 2026-07-19 — one-hundred-forty-seventh stone: exact OS-I positive-arity source spaces

Implemented and verified:

- `fourDimensionalOSMultiIndexPartialDerivative` names the canonical permutation-independent
  repeated-coordinate Fréchet evaluation as the formal interpretation of OS-I printed p. 86's
  four-dimensional `D^α` notation.
- Its exact expansion retains order `|α|`, the point-major coordinate basis and every multiplicity;
  a theorem identifies it with every exact occurrence enumeration.
- `IsOSPositiveTimeOrderedFourDimensionalSourceTest` is indexed by `PositiveArity` and gives the
  exact positive-arity source membership law: every interpreted `D^α` vanishes outside strict
  positive time order. OS-I's separately declared scalar zero-point component remains separate.
- `osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet` proves exact equivalence with the
  established coordinate-free presentation on the same Schwartz function.
- `isClosed_osPositiveTimeOrderedFourDimensionalSourceTest` transports the proved kernel-
  intersection closedness to the exact source-syntax carrier.
- `OSPositiveTimeOrderedFourDimensionalSourceSpace` packages each positive-arity subtype with the
  induced ambient Schwartz topology, an exact equivalence to the Fréchet carrier, and a closed
  embedding.
- The explicit positive-time bump supplies a nonzero arity-one source-space element.
- Hostile probes lock the exact and enumerated positive-arity `D^α` values, source/Fréchet
  membership identity, closed topology, rejection by a nonzero exterior source derivative, and
  nonzero content.
- This does not yet construct the finite-sequence OS source domain: the relation to the earlier
  strict-support subspace, locally convex direct sum, distinct completed positive-half-space tensor
  product, source-facing `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-forty-eighth stone: exact algebraic OS source sequences

Implemented and verified:

- `OSPositiveTimeOrderedFourDimensionalTestSequence` keeps the source's scalar `f₀ ∈ ℂ` separate
  from exact positive-arity `OSPositiveTimeOrderedFourDimensionalSourceSpace` components.
- Its positive support finset is equivalent to nonvanishing of the same underlying Schwartz
  component, preventing disconnected finite-support witnesses.
- Zero source components and the all-zero source sequence are explicit.
- `MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence` maps the earlier strict
  topological-support carrier componentwise while preserving its scalar, exact support and every
  underlying Schwartz function definitionally; no properness claim is made.
- `unitZeroPointFourDimensionalOSSourceSequence` proves scalar-only data remains expressible without
  inventing an arity-zero source-space component.
- `singletonPositiveTimeBumpFourDimensionalOSSourceSequence` has exact support `{1}` and retains the
  explicit nonzero arity-one bump.
- Hostile probes lock the constructor surface, omitted-component zero law, the designated all-zero
  sequence, exact source membership, the strict-carrier componentwise map, scalar separation,
  singleton support and
  nonzero content.
- This is algebraic only. The exact source-sequence direct-sum topology, product, involution,
  completed positive-half-space tensor product, `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-forty-ninth stone: exact-source finite-stage final topology

Implemented and verified:

- `OSPositiveTimeOrderedFourDimensionalStage s` is the product of the separate scalar `f₀` and the
  exact source spaces at every positive arity in finite stage `s`.
- Stage components extend by the exact zero source test outside `s`; stage output support filters by
  actual nonvanishing and is proved contained in `s`.
- `osPositiveTimeOrderedFourDimensionalSequenceToSupportStage` restricts any exact source sequence
  to its actual support, and `osPositiveTimeOrderedFourDimensionalStage_recover` proves exact
  recovery including the scalar.
- `osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology` is the named supremum of all stage-
  map coinduced topologies. Every stage map is continuous and the exact all-stage universal property
  for maps out is proved.
- Hostile probes lock selected and absent components, support containment, exact recovery, scalar
  retention by the empty positive stage, every stage's continuity and the universal property.
- This topology is not yet identified with OS-I's locally convex direct sum. Compatible complex-
  module/topological-vector-space operations and local convexity remain open, as do the strict-
  carrier density/completion relation, completed positive-half-space tensor product, source product,
  involution, `(E2)`, OS-II growth and reconstruction.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fiftieth stone: exact source-space complex algebra

Implemented and verified:

- `OSPositiveTimeOrderedFourDimensionalSourceSpace.equivSubmodule` identifies every positive-arity
  source-syntax carrier with the exact complex derivative-vanishing Schwartz submodule while
  preserving the underlying function definitionally.
- Named additive commutative group and complex module structures are transported through that
  equivalence under the repository's controlled-instance policy.
- Zero, addition, negation and complex scalar multiplication are proved to be exactly the ambient
  Schwartz operations.
- Hostile probes lock the exact submodule equivalence and all underlying operations and retain the
  explicit nonzero source test.
- No continuity, topological-vector-space structure, local convexity, source-sequence module,
  direct-sum identification, `(E2)`, OS-II growth or reconstruction is asserted.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-first stone: exact source-sequence complex algebra

Implemented and verified:

- `OSPositiveTimeOrderedFourDimensionalSourceDFinsupp` models finitely supported dependent positive-
  arity source tests, and sequence coordinates are its product with the separate scalar `f₀`.
- Exact-support source sequences are proved equivalent to those coordinates; support membership is
  tied to source-space zero through exact underlying Schwartz equality.
- Named additive commutative group and complex module structures are transported to source
  sequences under controlled local source-space instances.
- Algebraic zero is the designated all-zero source sequence. Addition and complex scalar
  multiplication are exact on both the scalar and every positive-arity Schwartz component.
- Hostile probes lock coordinate preservation, designated zero, exact addition/scalar action and
  retention of the nonzero singleton source sequence.
- No continuity, topological-vector-space structure, local convexity, direct-sum identification,
  source product/involution, `(E2)`, OS-II growth or reconstruction is asserted.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-second stone: continuous linear source stages

Implemented and verified:

- The exact per-arity source-space algebra, source-sequence algebra and finite-stage final topology
  are installed only as local named instances.
- `osPositiveTimeOrderedFourDimensionalStageToSequenceLinearMap` proves every generating finite-
  stage extension complex-linear with exact scalar and underlying Schwartz component laws.
- `osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap` packages the same map as
  continuous into the named exact-source final topology.
- Bundling retains the exact stage map and support bound.
- Hostile probes lock the stage map, named addition/scalar action, support, actual continuity and
  recovery of the nonzero singleton from its support stage.
- This proves compatibility of generating maps only. Joint global addition/scalar continuity,
  topological-vector-space structure, local convexity, direct-sum identification, source product/
  involution, `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-third stone: source-space topological algebra

Implemented and verified:

- The exact positive-arity source topology remains the induced ambient Schwartz topology while its
  named additive-group and complex-module structures are installed locally.
- Named `ContinuousAdd`, `ContinuousNeg`, `IsTopologicalAddGroup` and `ContinuousSMul ℂ` structures
  are constructed by reducing every operation to its exact ambient Schwartz operation.
- Hostile probes install the named aggregate topological additive-group structure, expose joint
  addition continuity, negation continuity, joint complex scalar continuity and retain the explicit
  nonzero source test.
- Structures remain named rather than global. No source-sequence global continuity, local convexity,
  direct-sum identification, `(E2)`, OS-II growth or reconstruction is asserted.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-fourth stone: final-topology quotient compatibility

Implemented and verified:

- The disjoint union of all exact finite source stages maps continuously and surjectively onto exact
  source sequences, and the named finite-stage final topology is proved to be exactly its quotient
  topology.
- The lifted scalar action is continuous stagewise. Since `ℂ` is locally compact, quotient-product
  lifting proves joint complex scalar multiplication continuous on exact source sequences; named
  `ContinuousSMul ℂ` and continuous negation structures are packaged.
- Addition of stages indexed by `s` and `t` is constructed continuously in the union stage `s ∪ t`
  and proved to factor exactly to named sequence addition. Consequently addition by any fixed source
  sequence is continuous on either side.
- Joint addition is not inferred from separate continuity. A conditional theorem isolates the exact
  remaining hypothesis that the product of the total-stage quotient map with itself is quotient;
  no general false quotient-product principle is assumed.
- Hostile probes lock quotient recovery, named scalar and negation continuity, the nonzero singleton,
  exact union-stage addition, separate addition continuity, and the conditional joint-addition gate.
- `ContinuousAdd`, topological-vector-space structure, local convexity, direct-sum identification,
  source product/involution, `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-fifth stone: source-space local convexity

Implemented and verified:

- The transported exact complex source-space module canonically restricts to a real module, and the
  exact forgetful map is packaged as `toSchwartzRealLinearMap`.
- The map preserves the same underlying Schwartz function and exact real scalar action and is proved
  inducing for the already-defined source topology.
- Named `LocallyConvexSpace ℝ` structure is transported from ambient Schwartz space to every exact
  positive-arity source space.
- Hostile probes lock exact real-linearity, the inducing topology, actual convex neighborhoods at
  zero, and retention of the explicit nonzero source test.
- This is per-arity local convexity only. Sequence local convexity, joint sequence addition,
  direct-sum identification, completion/tensor topology, `(E2)`, OS-II growth and reconstruction
  remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-sixth stone: finite-stage local convexity

Implemented and verified:

- Every exact finite source stage inherits named `IsTopologicalAddGroup`, `ContinuousSMul ℂ`, and
  `LocallyConvexSpace ℝ` structures from the separate scalar and finite dependent product of exact
  positive-arity source spaces.
- Hostile probes install each aggregate and expose joint stage addition, joint complex scalar
  continuity, actual convex zero-neighborhood refinements, and the nonzero independent scalar even
  at the empty positive-arity stage.
- These are finite-product structures only. They do not establish joint sequence addition, sequence
  local convexity, direct-sum identification, completion/tensor topology, `(E2)`, OS-II growth or
  reconstruction.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-seventh stone: locally convex final source topology

Implemented and verified:

- `IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology` requires joint addition and
  complex scalar continuity, real local convexity, and continuity of every exact finite-stage map.
- The `sInf` of all such topologies is constructed as a separately named locally convex final topology.
  Mathlib lattice theorems prove it self-admissible, so its defining family is not vacuous.
- Named `ContinuousAdd`, `ContinuousSMul ℂ`, `ContinuousNeg`, `IsTopologicalAddGroup`, and
  `LocallyConvexSpace ℝ` structures are packaged, and every exact stage map is bundled as the same
  continuous complex-linear extension.
- The raw finite-stage final topology is proved below the locally convex final topology in Mathlib's
  reversed topology order. Equality is proved equivalent to full raw admissibility and is not
  asserted.
- Hostile probes lock self-admissibility, genuine joint operations, convex zero neighborhoods,
  exact nonzero-stage recovery, the one-way raw comparison, and the exact equality gate.
- Hausdorff separation, identification with OS-I's printed locally convex direct sum, raw equality,
  strict-carrier density/completion, completed tensor topology, `(E2)`, OS-II growth and
  reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-fifty-eighth stone: Schwartz Hausdorff infrastructure

Implemented and verified:

- `SchwartzMap.exists_schwartzSeminorm_ne_zero` proves the standard zeroth Schwartz seminorm
  detects every nonzero map by its pointwise norm control.
- The standard seminorm family therefore separates points; named `T1Space` and `T2Space` structures
  are derived from `WithSeminorms` and the existing topological additive-group structure.
- Structures remain named rather than global to avoid future Mathlib instance conflicts.
- Hostile probes require seminorm detection of every nonzero map, closed exact singletons, and
  disjoint open neighborhoods for every unequal pair.
- This is reusable general mathematics. It supplies no OS direct-sum identification, `(E2)`, OS-II
  growth, reconstruction, quantum theory, existence theorem, or mass gap.

## 2026-07-19 — one-hundred-fifty-ninth stone: Hausdorff locally convex source topology

Implemented and verified:

- Hausdorffness of ambient Schwartz space transports through the exact closed embedding to every
  positive-arity source space.
- `OSPositiveTimeOrderedFourDimensionalAllCoordinates` keeps the separate scalar and every exact
  positive-arity source coordinate; the sequence coordinate map is complex-linear and injective.
- The topology induced by that map is proved an admissible locally convex final topology, so
  universal minimality makes the map continuous from the constructed locally convex final topology.
- A continuous injection into the Hausdorff scalar/product source space proves the locally convex
  final source topology itself Hausdorff; the exact coordinate map is also bundled continuously
  linear.
- Hostile probes lock exact coordinates, injectivity, auxiliary admissibility, continuity, retention
  of the nonzero singleton coordinate, and disjoint open separation of every unequal pair.
- Raw-topology equality, identification with OS-I's printed locally convex direct sum, strict-carrier
  density/completion, completed tensor topology, `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixtieth stone: locally convex finite-stage universal property

Implemented and verified:

- For any real-locally-convex topological complex module `Y`, a complex-linear map from exact source
  sequences to `Y` is continuous for the locally convex final topology if and only if its composite
  with every exact finite-stage extension is continuous.
- The reverse implication uses the topology induced by the linear map, proves it admissible, and
  invokes exact universal minimality rather than assuming a generic direct-sum theorem.
- Every all-stage-continuous algebraic linear map packages as the same continuous-linear map, and
  two continuity proofs cannot produce disconnected packages.
- Hostile probes recover the independently constructed all-coordinate CLM, retain its nonzero
  singleton value, require all finite stages, and enforce package uniqueness.
- OS-I p. 87 states the analogous criterion using each natural coordinate injection. Exact
  equivalence between those individual injections and the finite-stage criterion—and hence the
  printed direct-sum identification—remains open, alongside strict-carrier density/completion,
  completed tensor topology, `(E2)`, OS-II growth and reconstruction.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-first stone: source-facing locally convex direct sum

Implemented and verified:

- The exact sequence-coordinate equivalence is upgraded to a complex-linear equivalence. OS-I's
  separate scalar natural injection and every positive-arity source natural injection are defined.
- Scalar and source injections factor through the empty and singleton finite stages respectively
  and are proved continuous into the Hausdorff locally convex final topology.
- Every exact finite-stage extension is proved equal to the scalar injection plus the finite sum of
  its selected positive-arity injections, including dependent-coordinate casts and the exact zero
  branch outside the stage.
- A complex-linear map into any real-locally-convex topological complex module is continuous exactly
  when its scalar-injection composite and every positive-arity-injection composite are continuous.
  This is the coordinatewise universal property printed by OS-I p. 87.
- The Hausdorff locally convex final topology is consequently designated the source-facing locally
  convex direct-sum topology. The raw topological final topology remains a separately named
  auxiliary topology; equality is neither asserted nor needed for the source-facing selection.
- Hostile probes lock the scalar/component split, exact finite-stage recomposition, genuine
  injection continuity, the coordinatewise criterion, the nonzero source injection, and exact
  topology selection.
- Strict-carrier density/completion, the distinct completed positive-half-space tensor topology,
  source product/involution, `(E2)`, OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-second stone: direct-sum named structures and injections

Implemented and verified:

- The source-facing direct-sum topology now exposes named `ContinuousAdd`, `ContinuousSMul ℂ`,
  `IsTopologicalAddGroup`, `LocallyConvexSpace ℝ`, and `T2Space` structures under its own name.
- The separate scalar and every positive-arity natural injection are bundled as exact continuous
  complex-linear maps into that topology.
- Application theorems prove the CLM bundles retain the exact algebraic injections.
- Hostile probes install the named aggregates, expose genuine joint operations, require local
  convexity and Hausdorffness, retain the scalar coordinate, and retain the explicit nonzero source
  test through its bundled injection.
- This supplies canonical source-facing topology plumbing only. Strict-carrier density/completion,
  the distinct completed positive-half-space tensor topology, source product/involution, `(E2)`,
  OS-II growth and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-third stone: completed projective tensor interface

Implemented and verified:

- `CompletedComplexProjectiveTensorProductData` isolates missing general mathematics as a typed
  interface rather than an arbitrary proposition or project axiom.
- Both factors must be Hausdorff real-locally-convex topological complex modules. A candidate
  carrier must be complete for an additive-compatible uniformity, receive a jointly continuous
  bilinear pure-tensor map, have dense pure-tensor span, and preserve every pair of nonzero factors.
- Every jointly continuous bilinear map into a same-universe additive-uniform complete Hausdorff
  locally convex target must extend continuously linearly with exact agreement on pure tensors;
  uniqueness is derived from dense pure span and target Hausdorffness.
- Derived theorems prove zero-factor laws and nontriviality from explicit nonzero factors.
- Hostile probes reject one-factor collapse, zero pure tensors, nondense disconnected complements,
  nonexact lifts, nonunique extensions, and proper self-projections.
- No interface inhabitant is constructed. The OS positive-half-line quotient, spatial factor,
  iterated source-specific completion, and bridges remain open and separate from the direct sum.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-fourth stone: continuous Schwartz point evaluation

Implemented and verified:

- `SchwartzMap.pointEvaluationLinearMap` evaluates an arbitrary real Schwartz map at one exact
  point, and the zeroth standard Schwartz seminorm proves it continuous.
- Point evaluation is bundled as a continuous real-linear map with exact application.
- Every point-evaluation kernel is closed for Hausdorff values, every nonzero Schwartz map is
  detected by some evaluation, and equality of all evaluations determines the exact map.
- Hostile probes lock exact values, closed kernels, nonzero detection, and full pointwise
  determination.
- This is reusable infrastructure for the closed negative-half-line support submodule and quotient
  `𝒮(ℝ₊)`; no quotient, completed tensor carrier, `(E2)`, reconstruction, theory, or mass gap is
  constructed here.

## 2026-07-19 — one-hundred-sixty-fifth stone: OS positive-half-line Schwartz quotient

Implemented and verified:

- `osNegativeHalfLineSchwartzSubmodule` consists exactly of complex Schwartz functions vanishing at
  every positive real point; membership is equivalent to topological support in `(-∞,0]`.
- Continuous point evaluations express it as an intersection of closed kernels, proving closedness.
- `OSPositiveHalfLineSchwartzSpace` is the actual quotient `𝒮(ℝ)/𝒮(ℝ₋)` with Mathlib's quotient
  topology. Its canonical map is complex-linear, continuous, surjective, a quotient map, and is
  bundled continuously linearly.
- The open linear quotient map transports named topological additive-group, jointly continuous
  complex scalar, and real local-convexity structures; closedness supplies named regular/Hausdorff
  structures.
- A compactly supported smooth bump centered at `1` has topological support in `[0,∞)`, exact value
  one, and gives a nonzero quotient class.
- Hostile probes lock support semantics, closedness, quotient topology/surjectivity, exact zero
  classes, CLM packaging, joint operations, convex zero neighborhoods, nonzero retention, and
  Hausdorff separation from zero.
- Quotient completeness, OS-I's seminorm presentation, spatial/tensor factors, `(E2)`, OS-II growth
  and reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-sixth stone: positive-half-space scalar-functional candidate

Implemented and verified:

- `OSFourDimensionalSpatialSpace` uses exactly `Fin four.spatialDimension` and has real finrank
  three, recording the spatial provenance even though the underlying Euclidean type is definitionally
  the same as three-dimensional spacetime. Its complex Schwartz factor has an
  explicit compactly supported nonzero spatial bump.
- `OSPositiveHalfSpaceScalarFunctionalTensorCandidate` records OS-I's scalar-valued extension
  consequence for the exact factors while leaving the candidate carrier supplied and uninhabited.
  Scalar-valued extensions do not characterize `𝒮(ℝ₊) ⊗̂ 𝒮(ℝ³)` or its topology. The stronger
  arbitrary-target projective interface is not inherited and remains separately source-blocked.
- Any supplied candidate is additive-uniform complete, Hausdorff and locally convex, with jointly
  continuous noncollapsing pure tensors, dense pure span, and exact scalar-functional extension;
  scalar extension uniqueness within that candidate is derived from density.
- Hostile probes lock the four-dimensional spatial index, two-factor noncollapse, joint continuity,
  dense pure span, exact scalar extension values, and scalar extension uniqueness.
- No completed tensor topology or carrier is constructed or characterized. Half-line completeness,
  the printed seminorm presentation, nuclearity, strict-carrier comparison, `(E2)`, OS-II growth and
  reconstruction remain open.
- No `(E2)` datum, reconstruction, quantum theory, existence theorem, or mass gap is constructed.

## 2026-07-19 — one-hundred-sixty-seventh stone: iterated scalar-functional candidates

Implemented and verified:

- `osPositiveHalfSpaceScalarFunctionalTensorFactorCount` makes the indexing explicit: index `n`
  denotes `n + 1` intended factors, so index zero is the one-factor candidate and never the scalar
  OS-sequence component.
- `OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate` anchors `T 0` to that candidate and
  records fixed-left-associated scalar-functional successor candidate data for every natural index.
- Every supplied successor has jointly continuous noncollapsing pure tensors, dense pure span, and
  exact scalar-functional extension. Extension uniqueness is derived from density at each index.
- The explicit one-factor bump is recursively tensorized and proved nonzero at every finite positive
  factor count. Hostile probes also lock the one-factor anchor, successor continuity and density,
  scalar lift values and uniqueness, two-factor recursion, and two-factor noncollapse.
- The stronger arbitrary-target projective interface is not inherited. These data do not
  characterize completed tensor topology or nuclearity; no associator, permutation equivalence,
  product-Schwartz identification, actual completed carrier, or OS test-space bridge is asserted.
- Half-line completeness, the printed seminorm presentation, nuclearity, strict-carrier comparison,
  actual completed tensor powers, `(E2)`, OS-II growth and reconstruction remain open. No theory,
  existence theorem, or mass gap is built.

## 2026-07-19 — one-hundred-sixty-eighth stone: degree-zero covariant exterior derivative

Implemented and verified:

- `covariantExteriorDerivativeZero` canonically packages the existing same-connection intrinsic
  derivative of the exact section corresponding to a degree-zero adjoint-valued form as a degree-one
  adjoint-valued form; it introduces no new derivative field.
- Evaluation at the unique `Fin 1` slot is definitionally the original covariant derivative, and a
  degree-zero form built from a section differentiates that exact section.
- Agreement at every tangent evaluation uniquely determines the packaged one-form. A hostile probe
  rejects any output with even one mismatching evaluation.
- For every smooth input and designated in-chart point, exact fiber coordinates reduce to the
  existing same-connection expression `dσ(X) + [A(X),σ]`; probes expose both the ordinary derivative
  and bracket correction tied to that connection.
- This is only pointwise degree zero to degree one. Smoothness in the project's adjoint-form
  predicate, a positive-degree covariant exterior derivative, graded bracket wedge, Bianchi, and
  positive curvature-tensor orders remain open. No derivative inhabitant or theory is constructed.

## 2026-07-19 — one-hundred-sixty-ninth stone: smooth degree-zero covariant exterior derivative

Implemented and verified:

- `SmoothPrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero`
  packages the exact pointwise degree-one output together with a derived proof of the project's
  adjoint-valued differential-form smoothness predicate.
- No new regularity field is supplied. The proof uses the already required `C∞` derivative-bundle
  section, applies that smooth family of continuous linear maps to each locally smooth tangent
  field, and reads the result in the exact designated dependent-fiber trivialization.
- Forgetting smoothness is definitionally the preceding same-connection pointwise packaging, and
  evaluation remains definitionally the original intrinsic covariant derivative.
- Hostile probes lock the exact pointwise carrier, smoothness of that same carrier, unique-slot
  evaluation, rejection of an unrelated smooth output, and the same local `d + ad(A)` expression.
- Positive-degree covariant exterior differentiation, graded bracket wedge, Bianchi, and positive
  curvature-tensor orders remain open. No derivative inhabitant or theory is constructed.

## 2026-07-19 — one-hundred-seventieth stone: continuous graded Lie-bracket wedge

Implemented and verified:

- `ContinuousAlternatingMap.lieBracketWedgeOneMany` constructs `[α ∧ β]` from a continuous
  one-form and continuous `n`-form using Mathlib's algebraic alternatization and the exact sum
  `∑ᵢ (-1)ⁱ[α(vᵢ),β(v₀,…,v̂ᵢ,…,vₙ)]`.
- Continuity is proved directly term by term from joint bracket continuity, coordinate evaluation,
  omitted-slot continuity, finite sums, and integer scalar action; no new normed-space assumption is
  imposed.
- At degree one the construction is proved exactly equal to the existing two-term bracket wedge,
  retaining its curvature normalization. Zero laws and a pointwise manifold lift are derived.
- Hostile probes lock every term/sign, degree-one coherence, the exact three terms for a one-form
  wedged with a two-form, alternation, zero laws, and same-base manifold evaluation.
- Smooth closure of the graded operation, a positive-degree covariant exterior derivative, Bianchi,
  and positive curvature-tensor orders remain open. No connection or theory is constructed.

## 2026-07-19 — one-hundred-seventy-first stone: smooth graded Lie-bracket wedge

Implemented and verified:

- `ManifoldDifferentialForm.IsSmooth.lieBracketWedgeOneMany` proves that a smooth one-form wedged
  by the exact graded bracket with a smooth `n`-form is a smooth `(n+1)`-form.
- Each omitted-slot term uses the corresponding smooth tangent fields, the existing smooth bracket
  in exact normed value coordinates, integer sign conversion, and a finite smooth sum.
- `SmoothManifoldDifferentialForm.lieBracketWedgeOneMany` bundles that proof without changing the
  pointwise carrier. At degree one its carrier is proved exactly equal to the earlier smooth
  two-form bracket wedge.
- Hostile probes lock smoothness of the exact carrier, degree-one smooth coherence, rejection of an
  unrelated smooth output, the smooth one-with-two endpoint, and the zero-one-form carrier.
- A positive-degree exterior/covariant derivative, graded Leibniz laws, Jacobi cancellation,
  Bianchi, and positive curvature-tensor orders remain open. No connection or theory is constructed.

## 2026-07-19 — one-hundred-seventy-second stone: cubic graded Jacobi cancellation

Implemented and verified:

- `ContinuousAlternatingMap.lieBracketWedgeOneMany_self_self` proves
  `[α ∧ [α ∧ α]] = 0` for every continuous Lie-algebra-valued one-form.
- Evaluation expands the exact three omitted-slot terms and both inner bracket orders. Skew symmetry
  converts each pair to twice one nested bracket, and the cyclic Lie Jacobi identity cancels the
  resulting sum with the repository's fixed self-wedge normalization.
- Pointwise manifold and smoothly bundled corollaries retain the exact zero three-form carrier; the
  smooth corollary is assembled only from the already derived smooth inner and outer wedges.
- Hostile probes reject nonzero pointwise and smooth cubic self-brackets and lock manifold
  coherence.
- A positive-degree exterior/covariant derivative, graded Leibniz laws, Bianchi, and positive
  curvature-tensor orders remain open. No connection or theory is constructed.

## 2026-07-19 — one-hundred-seventy-third stone: graded bracket bilinearity laws

Implemented and verified:

- `add_lieBracketWedgeOneMany` and `lieBracketWedgeOneMany_add` derive additivity in the one-form
  and `n`-form arguments from the exact alternating-sum definition.
- `smul_lieBracketWedgeOneMany` and `lieBracketWedgeOneMany_smul` derive real-scalarity in both
  arguments, including the required commutation between integer signs and real scalar action.
- Hostile probes lock both additivity laws and both real-scalarity laws simultaneously; the earlier
  zero laws remain exact consequences.
- These are algebraic prerequisites for future curvature and Leibniz expansions. No exterior or
  covariant derivative, Bianchi identity, connection, or theory is constructed.

## 2026-07-19 — one-hundred-seventy-fourth stone: positive-degree Cartan certificates

Implemented and verified:

- `positiveDegreeCartanExpressionCoordinates` mirrors Mathlib's general positive-degree Cartan
  formula with the exact `Fin (n+2)` derivative sum, triangular `Fin (n+1)`/`Ici` bracket sum,
  nested omitted slots, integer signs, and leading subtraction.
- Normed-space specialization is definitionally the pinned Mathlib expression, and
  `extDerivWithin_eq_positiveDegreeCartanExpression` derives exact compatibility from Mathlib's
  theorem under its differentiability and unique-differentiability hypotheses.
- `SmoothManifoldPositiveDegreeExteriorDerivativeCertificate` packages a supplied smooth
  `(n+2)`-form satisfying that formula for one smooth `(n+1)`-form. Certificates agree on every
  admissible smooth field tuple, and every zero form has a concrete zero certificate.
- `SmoothManifoldTwoFormExteriorDerivativeCertificate` is the exact `2 → 3` specialization needed
  to type a future ordinary derivative of curvature.
- Hostile probes lock all indices/signs, Mathlib compatibility, certificate formula and agreement,
  the `2 → 3` endpoint, malformed-formula rejection, and the zero output.
- This does not construct a canonical manifold exterior derivative or prove chart independence,
  `d²`, graded Leibniz, covariant differentiation, or Bianchi. No connection or theory is built.

## 2026-07-19 — one-hundred-seventy-fifth stone: one-form/positive-degree Cartan coherence

Implemented and verified:

- `positiveDegreeCartanExpressionCoordinates_zero_eq_oneForm` proves the positive-degree triangular
  formula at `n = 0` is exactly the earlier ordered one-form Cartan expression.
- The proof explicitly recovers both omitted one-slot tuples, both field coordinates, the singleton
  triangular bracket sum, and the earlier `twoVectorArguments` ordering.
- `toPositiveDegreeZero` and `toOneForm` convert certificates in both directions while retaining
  definitionally the same smooth degree-two derivative carrier.
- Hostile probes lock the expression bridge, each conversion, carrier preservation through both
  round trips, and rejection of unrelated forward or reverse derivative outputs.
- This is coherence between supplied APIs, not certificate existence, full structure equality,
  chart independence, `d²`, graded Leibniz, covariant differentiation, or Bianchi.

## 2026-07-19 — one-hundred-seventy-sixth stone: local-model Cartan nilpotence

Implemented and verified:

- `extDerivWithin_positiveDegreeCartanExpression_zero` combines the exact positive-degree Cartan
  bridge with Mathlib's `extDerivWithin_extDerivWithin_apply` theorem.
- Differentiability of the first derivative is derived from the same input form's second-order
  regularity and exact set hypotheses; it is not accepted as a disconnected witness.
- `extDeriv_positiveDegreeCartanExpression_zero` supplies the global specialization, while
  `secondExteriorDerivativeCartanExpression_zero` locks the Bianchi-relevant `1 → 2 → 3` endpoint.
- Hostile probes reject a nonzero second-derivative Cartan value and any unrelated nonzero output.
- This proves normed-space local-model mathematics only. It does not provide an arbitrary-manifold
  exterior derivative, chart-independent `d²`, covariant `D²`, graded Leibniz, or Bianchi.

## 2026-07-19 — one-hundred-seventy-seventh stone: exact Lie-bracket differential calculus

Implemented and verified:

- `groupLieAlgebraCoordinateBracketCLM_apply` proves that the existing bounded bilinear coordinate
  map is exactly the transported Mathlib tangent Lie bracket.
- `groupLieAlgebraCoordinateBracket_hasFDerivAt` derives the bracketed function's derivative from
  the two exact input derivatives using Mathlib's bilinear calculus; no separate differentiability
  witness or auxiliary bracket is accepted.
- `groupLieAlgebraCoordinateBracket_fderiv_apply` evaluates the exact two-term product rule in an
  arbitrary source direction, and `groupLieAlgebraCoordinateSelfBracket_fderiv_apply` specializes
  it to the same function in both slots.
- Hostile probes reject an unrelated continuous bilinear bracket map and any derivative value that
  differs from the canonical two-term result.
- This is finite-dimensional normed-coordinate infrastructure. The exterior derivative of the
  bracket wedge, graded Leibniz, manifold/covariant transport, and Bianchi remain unproved.

## 2026-07-19 — one-hundred-seventy-eighth stone: continuous bilinear coordinate wedge

Implemented and verified:

- `continuousBilinearWedgeOneMany` constructs the exact signed omitted-slot wedge of a continuous
  one-form and `n`-form through any curried continuous bilinear map.
- Its full alternating-sum evaluation and degree-one first-minus-second formula are proved.
- Additivity and real scalar multiplication are proved in both form arguments, preparing the
  operation for Mathlib's bounded-bilinear differential calculus.
- `groupLieAlgebraCoordinateBracket_wedge_coherence` proves that canonical coordinate
  postcomposition carries the intrinsic graded Lie-bracket wedge to this operation using the exact
  previously constructed group bracket map.
- Hostile probes lock signs, degree-one ordering, the exact degree-two three-term expansion, both
  linearity surfaces, and intrinsic/coordinate coherence while rejecting malformed sums and coherence failures.
- This does not yet differentiate the wedge or prove graded Leibniz, manifold/covariant transport,
  or Bianchi.

## 2026-07-19 — one-hundred-seventy-ninth stone: self-wedge coefficient calculus

Implemented and verified:

- `continuousAlternatingMapEvaluation` packages evaluation on any fixed tuple as a continuous
  linear map, with continuity derived from the alternating-map operator-norm bound.
- `continuousBilinearSelfWedgeOne_hasFDerivAt_apply` derives the fixed two-vector self-wedge
  coefficient derivative solely from the exact one-form-valued `HasFDerivAt` witness.
- `continuousBilinearSelfWedgeOne_fderiv_apply` exposes all four terms: two forward-order product
  terms minus the corresponding two reverse-order terms.
- No separate differentiability witness for the wedge coefficient is accepted; it is derived through
  continuous evaluation and Mathlib's bounded-bilinear calculus.
- Hostile probes lock exact evaluation, the same-input derivative, all four slots, and rejection of
  missing, swapped, sign-changed, or otherwise malformed derivative outputs.
- This is coefficient-level local-model calculus. Exterior alternation, the self-wedge graded
  Leibniz identity, manifold/covariant transport, and Bianchi remain unproved.

## 2026-07-19 — one-hundred-eightieth stone: self-wedge exterior alternation

Implemented and verified:

- `continuousBilinearSelfWedgeExteriorAlternationAt` names the exact three-slot signed alternation
  of the previously derived self-wedge coefficient derivatives.
- `continuousBilinearSelfWedgeOne_fderiv_tuple` removes the earlier `Fin.cases` presentation and
  supplies the exact four-term derivative for every arbitrary `Fin 2` tuple.
- `continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two` expands all twelve terms, applies
  skew symmetry in the six derivative-first terms, and proves the exact identity
  `-2 • (A ∧_B dA)`.
- `groupLieAlgebraCoordinateBracketCLM_skew` derives skewness from the same transported Mathlib
  tangent bracket, and the group-coordinate specialization uses no auxiliary bracket.
- Hostile probes lock tuple recovery, the minus-two sign and normalization, canonical group skew,
  and reject every conflicting alternation value.
- The left side is intentionally a raw exterior alternation. Differentiability of the whole
  self-wedge form-valued function, its identification with Mathlib `extDeriv`, manifold/covariant
  transport, and Bianchi remain unproved.

## 2026-07-19 — one-hundred-eighty-first stone: full local self-wedge exterior derivative

Implemented and verified:

- `norm_continuousBilinearWedgeOneMany_one_le` proves the explicit operator-norm estimate
  `2 ‖B‖ ‖α‖ ‖β‖` from the two-term wedge formula.
- `continuousBilinearWedgeOneCLM` packages the exact degree-one wedge as a curried continuous
  bilinear map without changing its carrier.
- `continuousBilinearSelfWedgeOne_hasFDerivAt` applies Mathlib's bounded-bilinear calculus to derive
  whole-form self-wedge differentiability from the same one-form-valued derivative witness.
- `extDeriv_continuousBilinearSelfWedgeOne` identifies the raw coefficient alternation with Mathlib
  `extDeriv` and proves `d(A ∧_B A) = -2 • (A ∧_B dA)` exactly.
- The canonical finite-dimensional group-coordinate bracket receives the same exact theorem.
- Hostile probes lock the norm bound, bundled carrier, derived differentiability, minus-two identity,
  canonical specialization, and rejection of malformed exterior derivatives.
- This closes the required self-wedge graded Leibniz identity only in normed local coordinates.
  Arbitrary-manifold transport, positive-degree covariant differentiation, and Bianchi remain open.

## 2026-07-19 — one-hundred-eighty-second stone: normed-coordinate Bianchi

Implemented and verified:

- `groupLieAlgebraCoordinateCurvature` defines `F_A = dA + 1/2[A ∧ A]` from one exact
  group-coordinate one-form and the canonical transported tangent bracket.
- `groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo` defines the degree-two expression
  `D_Aω = dω + [A ∧ ω]` using the same connection and bracket.
- `groupLieAlgebraCoordinateSelfWedge_cubic` derives exact cubic Jacobi cancellation in those
  coordinates rather than assuming a zero field.
- `groupLieAlgebraCoordinate_bianchi` derives `D_A F_A = 0` from second-order regularity of the
  same one-form, Mathlib `d² = 0`, the exact self-wedge exterior derivative, and Jacobi.
- No curvature, covariant derivative, or Bianchi witness is accepted independently.
- Hostile probes lock both defining formulas, cubic cancellation, the derived zero, and reject
  unrelated curvature and nonzero Bianchi outputs.
- This is a finite-dimensional normed-coordinate theorem. Transport to the project's exact
  principal connection, descended adjoint-bundle curvature, arbitrary-manifold positive-degree
  covariant exterior derivative, and source-facing Bianchi theorem remain open.

## 2026-07-19 — one-hundred-eighty-third stone: within-set coordinate Bianchi

Implemented and verified:

- `continuousBilinearSelfWedgeOne_fderivWithin_tuple` derives every fixed coefficient derivative
  from one `DifferentiableWithinAt` input on one exact set.
- `continuousBilinearSelfWedgeOne_differentiableWithinAt` derives whole-wedge regularity without a
  second witness, and `extDerivWithin_continuousBilinearSelfWedgeOne` proves the exact minus-two
  within-set Leibniz identity.
- `groupLieAlgebraCoordinateCurvatureWithin` and
  `groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin` retain the same set, connection,
  and canonical bracket; both recover the global definitions exactly on `univ`.
- `groupLieAlgebraCoordinate_bianchiWithin` derives zero from one `ContDiffWithinAt` connection,
  explicit smoothness order, `UniqueDiffOn`, membership, and closure-of-interior hypotheses.
- Hostile probes reject malformed within-set derivatives, unrelated same-set curvature, and nonzero
  Bianchi outputs while locking exact `univ` recovery.
- This removes the locality-shape blocker for chart transport. The chart-local pullback carrier,
  exterior-derivative naturality, exact principal-curvature coordinate equality, and source-facing
  principal/adjoint Bianchi theorems remain open.

## 2026-07-19 — one-hundred-eighty-fourth stone: normed coordinates for manifold forms

Implemented and verified:

- Raw unrestricted `mfderiv` transport and canonical explicit-source `mfderivWithin` transport are
  separate carriers; the raw carrier is documented as meaningful only under full differentiability.
- `inExtChartAt` uses the canonical within-set carrier on `Set.range I`, matching Mathlib's
  corner-aware inverse-chart pullback rather than differentiating the unrestricted totalization.
- Exact evaluation and chart-center point recovery retain the same within-range derivative.
- `inExtChartAt_tangentMap_isInvertible` proves this transport invertible at every chart-target
  point; a hostile nontrivial-model probe rejects silent zero transport at the chart center.
- Addition and real scalar multiplication commute exactly with within-set coordinate pullback.
- Canonical tangent/model coordinates carry the intrinsic graded Lie-bracket wedge to the exact
  continuous-bilinear coordinate wedge, both generally within a source and in inverse charts.
- At this stone, chart-target regularity, `extDerivWithin` naturality, principal connection
  specialization, exact curvature equality, and transported Bianchi remained open.

## 2026-07-19 — one-hundred-eighty-fifth stone: exact principal curvature coordinates

Implemented and verified:

- The exact principal connection form, its connection-indexed exterior-derivative certificate, and
  the curvature derived from both now have named within-set normed-coordinate carriers.
- Separate inverse extended-chart carriers reuse the corner-aware within-range tangent transport.
- `curvatureCoordinatePullbackWithin_eq` proves Freed's exact equation after arbitrary same-map,
  same-source coordinate pullback using the canonical transported group bracket.
- `curvatureCoordinatesInExtChartAt_eq` proves the inverse-chart specialization without replacing
  the exact connection, derivative certificate, or derived curvature.
- The original degree-one bracket wedge is proved coherent with the graded one-with-one formula,
  preserving the exact `1/2` normalization through coordinate transport.
- Hostile probes reject unrelated curvature and derivative carriers and lock both general within-set
  and inverse-chart equations.
- At this stone the derivative term remained only the coordinate pullback of the manifold
  certificate; chart regularity, derivative naturality, coordinate-curvature identification, and
  transported Bianchi remained open.

## 2026-07-19 — one-hundred-eighty-sixth stone: conditional exact-curvature Bianchi bridge

Implemented and verified:

- `PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn` states the exact missing equality
  between the pulled-back connection-indexed derivative certificate and `extDerivWithin` of the
  exact coordinate connection.
- Tangent transport and exterior calculus retain separate sets. In an inverse chart these are exactly
  `Set.range IP` and `(extChartAt IP p).target`, respectively.
- Under naturality, the exact derived principal-curvature carrier agrees on the calculus set with
  `groupLieAlgebraCoordinateCurvatureWithin`.
- The existing same-connection coordinate Bianchi theorem then derives a zero covariant expression
  for the exact curvature carrier under explicit `ContDiffWithinAt`, smoothness-order,
  `UniqueDiffOn`, membership, and closure-of-interior hypotheses.
- Inverse-chart specializations preserve the actual chart target in every hypothesis and conclusion.
- Hostile probes reject mismatched derivative values and nonzero Bianchi outputs while locking the
  exact two-set naturality shape.
- Naturality and chart regularity are hypotheses, not constructed evidence. A canonical manifold
  positive-degree derivative and descended adjoint-bundle Bianchi theorem remain open.

## 2026-07-19 — one-hundred-eighty-seventh stone: dimension-two nondegeneracy

Implemented and verified:

- `twoDimensionalAreaForm` is an explicit continuous `dx⁰ ∧ dx¹`; it evaluates to one on the
  ordered standard basis and is therefore nonzero.
- Dimension two has an explicit normalized spatial direction, nonzero spacelike-separated Schwartz
  tests, a nonempty backward tube, and an ordered time/spatial plaquette plane.
- A concrete `2 × 2` periodic one-link gauge field realizes every prescribed group element as the
  holonomy of one selected elementary plaquette.
- Every admissible nontrivial plaquette potential therefore yields a concrete selected plaquette
  with strictly positive local action density.
- Hostile probes reject zero area, malformed holonomy, identity replacement of a nonidentity link,
  extension of the dimension-one curvature degeneracy, and substitution of dimension two for four.
- These are kinematic and finite-cutoff witnesses only. No two-dimensional continuum Yang–Mills,
  OS/Wightman theory, continuum bridge, or mass gap is constructed.

## 2026-07-19 — one-hundred-eighty-eighth stone: Wightman/observable coherence

Implemented and verified:

- `ScalarWightmanFieldLocalObservableCoherenceData` identifies the exact scalar Wightman field with
  the same-domain local family's existing nontrivial label.
- The Wightman adjoint is identified with the operator at that label's exact involutive adjoint.
- Pointwise operator equalities propagate to the already-tempered field and adjoint matrix-element
  distributions.
- Involutivity and unit-label preservation prove the selected adjoint label is also nonunit.
- The family's existing anti-vacuity witness transfers to the Wightman field, proving one action is
  nonzero and differs from the smeared unit.
- Hostile probes reject disconnected field and adjoint operators. No field, family, coherence datum,
  theory, or mass gap is constructed.

## 2026-07-19 — one-hundred-eighty-ninth stone: three-dimensional continuum core

Implemented and verified:

- `ThreeDimensionalCurrentStrengthContinuumCoreAcceptanceData` is hard-wired to coordinate
  Euclidean `ℝ³`, its two-dimensional spatial slice, and coordinate Lebesgue action measure; at
  this stone the supplied metric had not yet been fixed to the canonical flat metric.
- Its physical compact-simple gauge group is distinct in role and type parameter from the Poincaré
  lift group.
- One exact classical connection/curvature/action chain is joined to an exact `F²` interpretation in
  the same quantum local-observable family.
- One strict scalar Euclidean candidate is connected by exact strict Wick continuation to full and
  relative correlators of the exact Wightman field.
- The Wightman field is coherently the family's existing nontrivial label; the family is covariant,
  adjoint-closed, and local on the same common domain.
- A positive physical gap is required on the integrated Wightman surface's exact joint translation
  PVM and derives finite-positive supremum semantics from that same spectrum.
- Hostile projections lock dimension, compact-simple semantics, strict Wick coherence, nonzero
  Wightman and `F²` operators, exact classical coordinate measure, same-spectrum gap semantics, and
  reject disconnected spectra/families.
- No inhabitant is constructed. The record imports no lattice module, four-dimensional OS spatial
  `ℝ³` tensor surface, or four-dimensional running-coupling interface. Corrected source-facing OS
  reconstruction and a genuine Poincaré covering remain required before the `d=3` contract is
  complete.

## 2026-07-19 — one-hundred-ninetieth stone: three-dimensional stress/translation closure

Implemented and verified:

- The three-dimensional current-strength core now requires a symmetric, Hermitian, covariant,
  local, weakly conserved stress tensor inside its exact observable family.
- `LocalStressEnergyTranslationWardData` is indexed by that exact tensor and by
  `wightmanSurface.spectrum`; regulated stress charges, translation derivatives, momentum moments,
  and all-family Ward identities therefore use the same domain, representation, family, and PVM as
  the physical gap.
- The bridge requires a nonzero physical time-translation generator on one common-domain vector.
- Hostile projections expose the exact stress-family carrier, same-spectrum Ward bridge, and
  nonzero time generator. No tensor, cutoff sequence, generator, theory, or gap is constructed.

## 2026-07-19 — one-hundred-ninety-first stone: canonical Euclidean coordinate metric

Implemented and verified:

- `canonicalEuclideanSpacetimeMetricData` packages Mathlib's standard vector-space Riemannian metric
  on every supported coordinate spacetime, downgrading its `C^ω` regularity to the required `C^∞`.
- Its tangent-fiber pairing is definitionally the ordinary real inner product, self-pairing is the
  squared coordinate norm, and nonzero vectors have positive self-pairing.
- Hostile probes evaluate standard basis vectors and reject any unrelated metric whose pairing
  differs from the canonical inner product.
- The three-dimensional core no longer accepts an arbitrary Riemannian metric parameter: its action
  and exact `F²` interpretation are indexed by the canonical flat metric on coordinate `ℝ³`.
- The designated action measure remains exactly coordinate Lebesgue measure. A general theorem
  identifying Mathlib's metric-induced Riemannian volume with this measure remains open.

## 2026-07-19 — one-hundred-ninety-second stone: four-dimensional continuum core

Implemented and verified:

- `FourDimensionalCurrentStrengthContinuumCoreAcceptanceData` is an uninhabited integration surface
  hard-wired to canonical-flat coordinate `ℝ⁴` and coordinate Lebesgue action measure.
- It joins one compact-simple gauge/classical curvature/action chain to one strict Euclidean family,
  one exact Wightman/correlator chain, and strict ordered Wick coherence.
- The same covariant local family contains the nontrivial Wightman field, exact `F²` interpretation,
  and local stress tensor; stress charges, Ward identities and the physical gap use the exact same
  representation, domain and joint translation PVM.
- Unlike the lower-dimensional core, it requires the preliminary four-dimensional pure-gauge
  running-coupling/beta normal form indexed by the exact compact-simple gauge certificate.
- Hostile projections distinguish all three lower dimensions, expose canonical metric/measure,
  reject disconnected spectra/families, and require nonconstant running coupling, nonzero Wightman
  and `F²` actions, nonzero time generator, and finite-positive same-PVM gap semantics.
- No inhabitant is constructed. Corrected OS reconstruction, genuine Poincaré covering,
  source-faithful curvature-polynomial/OPE mixing, group-normalized coefficients and perturbative
  remainders, trace anomaly, and the final universal Clay proposition remain open.

## 2026-07-19 — one-hundred-ninety-third stone: four-dimensional weak OPE integration

Implemented and verified:

- The four-dimensional core now carries exact weak bilocal products and a weak all-orders OPE on its
  same coherently connected local-observable family.
- Decidable equality of the exact label carrier is stored locally for finite truncations and is not
  installed on an unrelated or global label type.
- `SuppliedWeakOPERegularVariationData` ties every nonzero coefficient's preliminary scaling to the
  exact core running coupling and exact weak OPE.
- The existing OPE anti-vacuity theorem derives an actual nonzero contracted zeroth-order term in
  the same family; hostile projections lock products, OPE, scaling, and that term.
- This remains supplied weak regular variation, not source-faithful perturbative Yang–Mills OPE
  coefficients. Group normalization, operator mixing, scheme dependence, calculated remainders and
  trace anomaly remain open; no theory or OPE inhabitant is constructed.

## 2026-07-19 — one-hundred-ninety-fourth stone: interpreted curvature-squared OPE coherence

Implemented and verified:

- `CurvatureSquaredOPECoherenceData` ties the exact interpreted curvature-squared label to both
  ordered inputs of one exact weak OPE in the same observable family.
- A selected output label must occur already at zeroth truncation order, its exact relative
  coefficient must be nonzero, and one exact output local-field matrix element must be nonzero.
- Contraction nondegeneracy derives a nonzero exact `F² × F²` term; monotonicity keeps the output in
  every later truncation.
- Hostile probes reject zero coefficients, zero output matrix elements, and unrelated input labels.
- The four-dimensional core now requires this bridge and exposes the exact nonzero contracted term.
  No coefficient calculation, operator-mixing matrix, group normalization, remainder calculation,
  trace anomaly, theory, or mass-gap witness is constructed.

## 2026-07-19 — one-hundred-ninety-fifth stone: interpreted OPE running dependence

Implemented and verified:

- The four-dimensional core now requires the selected nonzero interpreted `F² × F²` coefficient's
  coupling exponent to be nonzero for the exact same running coupling.
- The generic regular-variation theorem then derives that this exact coefficient has a nonzero
  leading tempered distribution.
- Hostile projections expose both same-coefficient running dependence and the nonzero leading
  distribution, preventing the generic OPE's running witness from living only on an unrelated label.
- The exponent and leading distribution remain supplied data. No anomalous dimension calculation,
  group normalization, operator mixing, perturbative coefficient or remainder is derived.

## 2026-07-19 — one-hundred-ninety-sixth stone: exact-source algebraic `(E2)`

Implemented and verified:

- Every finite sequence over the exact four-dimensional derivative-vanishing OS source spaces now
  maps to the unrestricted finite Schwartz algebra with exact scalar, support, and positive
  components.
- `OSSourceFourDimensionalReflectionPositivity` evaluates the exact Schwinger family on the actual
  unrestricted reflected-star convolution `(Θ f*) × f` and requires a nonnegative complex real.
- The concrete arity-one source bump survives the forgetful map, preventing scalar-only collapse.
- The strict-to-source inclusion forgets back to the exact same unrestricted sequence, so source
  positivity implies the earlier strict-subdomain predicate. No converse or properness is claimed.
- This closes exact algebraic source-carrier `(E2)`. Completed positive-half-space tensors,
  nuclearity, strict-carrier density, OS-II growth, reconstruction, and existence remain separate
  obligations rather than prerequisites for this positivity predicate.

## 2026-07-19 — one-hundred-ninety-seventh stone: exact-source `(E4)` clustering

Implemented and verified:

- `OSSourceFourDimensionalClustering` quantifies over every pair of exact derivative-vanishing
  source sequences and every normalized nonzero four-dimensional spatial direction.
- Its expression is exactly `S((Θ f*) × T_{λa}g) - S(Θ f*)S(g)` in the unrestricted finite
  Schwartz algebra and tends to complex zero as `λ → +∞`.
- Four dimensions have an explicit canonical direction, every direction is nonzero, and the
  positive-arity source bump survives, blocking empty-direction, zero-ray, and scalar-only vacuity.
- Exact componentwise restriction proves source `(E4)` implies every earlier strict-direction
  predicate; no converse is claimed.
- No clustering family, OS-II growth, reconstruction, theory, or mass-gap witness is constructed.

## 2026-07-19 — one-hundred-ninety-eighth stone: exact-source Euclidean current-strength package

Implemented and verified:

- `OSSourceFourDimensionalEuclideanCurrentStrengthData` now assembles ambient-extension OS-II
  growth and exact same-family source-carrier `(E1)`–`(E4)` obligations.
- Positivity reaches every exact derivative-vanishing source sequence; clustering reaches every
  source pair and every normalized nonzero spatial direction.
- Its ambient growth restricts canonically to carrier-exact OS-II `(E0′)` on the coincidence-flat
  family; source clustering already quantifies over every normalized direction.
- The four-dimensional continuum core now requires this exact-source package; its strict Wick
  bridge remains independently indexed by the same ambient Schwinger family.
- The package remains `CurrentStrength` because it retains extra full-Schwartz tempered extensions
  and has no corrected reconstruction bridge; no theory or mass-gap witness is constructed.

## 2026-07-19 — one-hundred-ninety-ninth stone: Clay endpoint dimension separation

Implemented and verified:

- `IsFourDimensionalClayEndpoint` accepts exactly the four-dimensional checker index.
- Every supported lower dimension `1`–`3` is rejected explicitly.
- Exact finite-rank arguments prove that no lower-dimensional real Euclidean spacetime is linearly
  equivalent to four-dimensional spacetime; in particular the 3D and 4D core bases cannot be
  substituted through a linear coordinate identification.
- Hostile probes cover all lower indices, four's exclusion from the lower union, and the `ℝ¹`,
  `ℝ²`, and exact 3D-core carrier obstructions.
- These are supporting index and real-linear coordinate-carrier separation facts, not yet
  witness-level separation for the still-absent final acceptance proposition and not nonexistence
  claims for lower-dimensional theories.

## 2026-07-19 — two-hundredth stone: carrier-exact OS-II linear growth

Implemented and verified:

- `fourDimensionalConfigurationSquaredNorm` uses the exact flattened coordinate sum
  `∑ᵢ∑μ(xᵢ^μ)²`, not the outer Pi supremum norm, and `osIIPrintedWeightedDerivativeTerm` formalizes
  equation (2.1)'s corresponding `(1+x²)^(p/2)‖D^αf(x)‖` term.
- `OSIIPrintedSchwartzControlData` characterizes the displayed supremum by every-term upper bounds
  and its least-upper-bound universal property; uniqueness and zero-test control are derived.
- Any strictly positive displayed term blocks a fake zero control.
- The coincidence-flat condition is packaged as an exact complex Schwartz submodule.
  `OSIICoincidenceFlatSchwingerFamily` has linear functionals only on those source carriers.
- `OSIICarrierExactLinearGrowthData` imposes equation (4.1) with one positive order and one positive
  factorial-growth sequence, without requiring a full-Schwartz extension.
- A separate `OSIIAmbientExtensionLinearGrowthData` retains extra full-Schwartz tempered extensions
  and restricts canonically to carrier-exact data; no converse extension is claimed.
- The control and growth data remain uninhabited, are not identified with the different Mathlib
  seminorm sum, and construct no family, reconstruction, theory, or mass gap.

## 2026-07-19 — two-hundred-first stone: four-dimensional Euclidean `(E0′)` integration

Implemented and verified:

- The exact-source Euclidean current-strength package now requires ambient-extension OS-II growth
  on the same Schwinger family as covariance, positivity, symmetry, and clustering.
- Its growth restricts canonically to carrier-exact `(E0′)` on the exact coincidence-flat family.
- The four-dimensional continuum core now requires this integrated `(E0′)`–`(E4)` package and no
  longer stores an arbitrary selected clustering direction or duplicate strict Euclidean candidate.
- Source `(E4)` already quantifies over every normalized nonzero direction; at this stone the Wick
  bridge was still separately limited to its strict ordered domain.
- Extra ambient tempered extensions and the absence of corrected reconstruction keep both records
  qualified as `CurrentStrength`; no family, theory, or mass-gap witness is constructed.

## 2026-07-19 — two-hundred-second stone: exact-source Wick coherence

Implemented and verified:

- `OSSourceOrderedScalarWickContinuationData` requires integrability and exact smeared equality for
  every derivative-vanishing positive-time ordered four-dimensional source test.
- The Euclidean distribution and relative Wightman analytic boundary are the exact existing
  families; no disconnected continuation value is stored.
- Nonzero source values are proved to lie in strict positive time order and reverse-Wick-rotate into
  the exact backward tube; the integrand vanishes outside its preimage.
- Strict ordered/flat tests include without changing their Schwartz function, so exact-source
  continuation derives the old strict bridge in the valid direction.
- The four-dimensional core now requires exact-source Wick coherence and derives its strict view.
  This is coherence between supplied data, not corrected reconstruction, uniqueness, a Hilbert-space
  construction, theory existence, or a mass-gap witness.

## 2026-07-19 — two-hundred-third stone: corrected-output Wightman `(R0′)`

Implemented and verified:

- The full Wightman Schwartz weight now uses the exact flattened positive coordinate sum over all
  `4n` coordinates, distinct from both the outer Pi norm and the Minkowski quadratic form.
- `OSIIWightmanPrintedSchwartzControlData` uniquely characterizes the printed control by its
  least-upper-bound property and rejects zero controls when an exact term is positive.
- `OSIIWightmanLinearGrowthCoefficientData` requires positive `ωₙ` and the exact source bound
  `ωₙ ≤ α β^(n²)` without adding unprinted sign hypotheses on `α, β`.
- `OSIIWightmanLinearGrowthData` imposes equation (4.3) with one common positive order on the exact
  existing full Wightman distributions, not a disconnected functional family.
- The four-dimensional core now requires this same-correlator `(R0′)` surface. No reconstruction
  output, uniqueness theorem, theory, or mass-gap witness is constructed.

## 2026-07-19 — two-hundred-fourth stone: same-field OS-II correlator uniqueness

Implemented and verified:

- `SameFieldOSIIOutputCorrelatorUniquenessData` bundles selected `(R0′)`, relative analytic, and
  exact-source Wick data for one full correlator family.
- Any alternative full correlator extension on the exact same field/Hilbert realization that also
  has `(R0′)` and exact-source Wick coherence must have equal distributions at every arity.
- Derived uniqueness reaches every full Schwartz test value, preventing zero-arity-only or
  disconnected-functional uniqueness.
- The four-dimensional core now requires this narrow same-field obligation.
- This is not corrected reconstruction acceptance or Wightman-theory uniqueness. Heterogeneous
  unitary-equivalence semantics and reconstruction remain open; no output, theory, or mass-gap
  witness is constructed.

## 2026-07-19 — two-hundred-fifth stone: genuine topological Poincaré cover requirement

Implemented and verified:

- The proper-orthochronous Lorentz carrier now has the topology induced by its exact pointwise linear
  action, and the affine Poincaré target has the product coordinate topology retaining both that
  action and the exact translation.
- Both coordinate maps are injective topological embeddings; changing the translation cannot be
  hidden by proof fields.
- `ProperOrthochronousPoincareCoverData` extends the existing surjective lift and requires its exact
  projection to satisfy Mathlib's `IsCoveringMap`.
- Continuity, local-homeomorphism, openness, quotient-map behavior, and discrete nonempty fibers are
  derived. Physical translation lifts remain exact.
- The four-dimensional core requires this cover and an equality tying its inherited lift to the
  exact lift indexing the physical representation.
- No concrete inhomogeneous `SL(2,ℂ)` carrier, affine-target group law, two-sheet/kernel theorem,
  universal-cover result, cover inhabitant, theory, or mass gap is constructed.

## 2026-07-19 — two-hundred-sixth stone: exact two-sheet covering semantics

Implemented and verified:

- `ProperOrthochronousPoincareDoubleCoverData` strengthens the genuine covering projection by
  requiring every exact affine target fiber to be equivalent to `Fin 2`.
- Every target consequently has two explicitly distinct lift points, and every fiber is finite as
  well as discrete and nonempty.
- Physical translation lifts and the same covering-map projection are retained unchanged.
- The four-dimensional core now requires this two-sheeted cover and ties its inherited lift exactly
  to the lift indexing the physical representation.
- The abstract sheets are not identified with matrix signs. No concrete inhomogeneous `SL(2,ℂ)`,
  affine semidirect-product group law, `{±1}` kernel theorem, universal cover, inhabitant, theory, or
  mass gap is constructed.

## 2026-07-19 — two-hundred-seventh stone: affine-target topological-group contract

Implemented and verified:

- `ProperOrthochronousPoincareTargetGroupData` requires a named group law on the exact affine target
  whose identity is the existing affine identity and whose multiplication acts by exact source-order
  composition.
- Affine transformations are proved equal when all their actions agree, so this multiplication is
  uniquely determined by the action law rather than being disconnected algebra.
- The named law must be a topological group for the canonical Lorentz-action/translation topology.
- For every exact double cover, the action-level projection laws derive a bundled group
  homomorphism into this named target law.
- The four-dimensional core now requires this target law alongside the exact double cover.
- The law remains supplied acceptance data: future-cone closure, its concrete construction, the
  inhomogeneous `SL(2,ℂ)` semidirect product, `{±1}` kernel identification, theory, and mass gap are
  not constructed.

## 2026-07-19 — two-hundred-eighth stone: heterogeneous Wightman unitary equivalence

Implemented and verified:

- `ScalarWightmanRealizationUnitaryEquivalence` provides project-level transport between explicitly
  equivalent lift-group carriers and Hilbert carriers. A source-facing
  `ScalarWightmanFixedLiftUnitaryEquivalence` additionally forces lift transport to be the identity,
  matching Streater–Wightman's fixed Poincaré group.
- Exact affine projections and physical translations agree under generic lift transport. In the
  source-facing specialization, the same exact group element acts on both realizations, while one
  Hilbert unitary intertwines the Poincaré representations and normalized vacua.
- One domain isometry is required to be the restriction of that Hilbert unitary and transports the
  vacuum, scalar field, and adjoint field exactly.
- Vacuum-in-domain coherence and Hilbert-level field intertwining are derived. Induction then proves
  transport of every finite field/adjoint word and equality of every associated algebraic vacuum
  expectation, including every ordered field-only smeared correlator.
- `CorrectedOSIIReconstructionAcceptanceData` now requires every universe-relative heterogeneous
  Hilbert realization over the same exact lift, with corrected `(R0′)`, relative analyticity, and
  exact-source Wick coherence for the same Euclidean family, to be related by fixed-lift unitary
  equivalence and to have the same full tempered distributions at every arity.
- The four-dimensional core uses this exact acceptance record with its selected Euclidean family,
  Wightman axiom surface, and full correlators, replacing same-field-only uniqueness as its core
  obligation.
- These are uninhabited acceptance conditions. They do not construct an output or equivalence,
  prove the OS reconstruction theorem, construct a theory, or prove a mass gap.

## 2026-07-19 — two-hundred-ninth stone: adjoint-Casimir one-loop normalization

Implemented and verified:

- `AdjointCasimirNormalizationData` chooses a finite nonempty basis of the exact tangent Lie algebra,
  requires it to be orthonormal for the same invariant pairing used by the classical action, and
  defines its structure coefficients from the exact Mathlib tangent bracket.
- Gross–Wilczek's displayed identity `∑_{b,c} C_{abc} C_{dbc} = C₂(G) δ_{ad}` is imposed with a
  strictly positive adjoint Casimir. A genuinely nonzero structure coefficient is derived, excluding
  an abelian or zero-bracket surrogate.
- `GroupNormalizedOneLoopBetaData` fixes the same preliminary running coupling's leading coefficient
  to `11 C₂(G)/(3·16π²)` and derives the denominator-cleared identity.
- `ClassicalRunningCouplingReferenceData` chooses an explicit ultraviolet logarithmic scale and
  equates the outer classical-action coupling with that same running coupling there. A replacement
  scalar satisfying the same bridge is proved equal, blocking a disconnected action coupling.
- The four-dimensional core requires both certificates using its exact compact-simple group,
  invariant pairing, classical action, and running coupling.
- The basis, Casimir identity, and coefficient/reference equalities remain supplied acceptance data.
  No basis construction, connection-level field-rescaling theorem, `O(g⁵)` calculation, scheme
  choice, OPE coefficient, theory, or gap is constructed.

## 2026-07-19 — two-hundred-tenth stone: scalar curvature-power observables

Implemented and verified:

- `ScalarCurvaturePowerTag` contains exactly the finite intrinsic fragment `1`, `F²`, `(F²)²`; its
  classical carrier is the corresponding exact function of the already descended,
  basis-independent canonical curvature density.
- `ScalarCurvaturePowerLocalObservableInterpretationData` exposes that classical carrier and requires
  exact equality with the canonical fragment. Its unit and `F²` labels are the existing labels in
  the same quantum local family.
- Separate `CurvatureQuarticAntiCollapseData` requires `(F²)²` to have a new label and one exact
  test/vector on which its operator is nonzero and differs from both unit and `F²`. The 4D core
  adopts this as a transparent project strengthening, not as a consequence of Clay's footnote.
- No active connection-gauge-invariance theorem, all-power map, independent invariant contractions,
  mixed curvature polynomials, covariant derivatives, renormalized products/mixing, interpretation
  witness, theory, or gap is constructed.

## 2026-07-19 — two-hundred-eleventh stone: literal complex-sign cover kernel

Implemented and verified:

- `complexSignSubgroup` is the literal subgroup `{1,-1}` of complex units, not an abstract `Fin 2`
  index; its negative sign is proved distinct from its identity.
- `properOrthochronousPoincareProjectionKernel` is the group-theoretic kernel of the exact bundled
  double-cover projection under the accepted named affine-target law.
- `projectionKernelEquivIdentityFiber` identifies that kernel with the exact identity fiber, so the
  existing `Fin 2` fiber theorem derives kernel cardinality two.
- Reusable order-two group infrastructure then derives a multiplicative equivalence with literal
  complex signs. Normality of the homomorphism kernel plus its unique nonidentity element derives
  centrality; these are theorems, not redundant supplied acceptance fields.
- The negative sign derives a central nonidentity lift of the exact affine identity. Multiplying any
  selected lift by it produces a distinct lift over the same target, and every lift over that target
  is proved equal to exactly one of these two relative choices.
- The four-dimensional core obtains these results automatically from the exact cover already
  indexing its physical representation.
- This project packaging is motivated jointly by Streater–Wightman printed p. 12's exact `A=±B`
  theorem and p. 14's inhomogeneous law. It does not construct `SL(2,ℂ)`, identify the accepted lift
  with a matrix semidirect product, produce canonical global/matrix sheet labels, construct a theory,
  or prove a gap.

## 2026-07-19 — two-hundred-twelfth stone: scalar cover-kernel triviality

Implemented and verified:

- Exact scalar covariance proves that every identity-projecting lift commutes on the common domain
  with both the field and its exact adjoint; identity affine pullback fixes the same Schwartz test.
- Vacuum invariance and induction prove that the same restricted unitary fixes every finite
  field/adjoint word on the selected vacuum.
- The Wightman cyclicity equality supplies density of that exact polynomial-vacuum span. Equality of
  continuous linear maps on the dense generating span then proves the full Hilbert unitary is the
  identity.
- For any scalar realization definitionally indexed by the exact double cover, the derived negative
  sign therefore acts trivially.
- `ScalarWightmanAxiomChainData` bundles the dependent representation/vacuum/domain/field/surface
  chain and transports this theorem across a propositional equality of lift records. The
  four-dimensional core now derives trivial negative-sign action on its exact existing physical
  representation through `poincareDoubleCover_toLift_eq`.
- This is a theorem from an already supplied scalar Wightman surface, not a representation or theory
  construction, and it does not apply to spinorial fields.

## 2026-07-19 — two-hundred-thirteenth stone: scalar affine-Poincaré descent

Implemented and verified:

- Kernel triviality proves that any two lifts of the same affine transformation have the exact same
  scalar Hilbert unitary.
- `selectedAffinePoincareLift` chooses one lift only internally; projection coherence proves the
  resulting `descendedAffineUnitary` agrees with every original lift and is choice-independent.
- `descendedAffineUnitaryHom` is a genuine homomorphism for the accepted named affine-target law.
- The selected-lift domain restriction is proved coherent with every original `D.domainUnitary`.
  Scalar field and adjoint covariance therefore descend to direct affine statements with no lift
  choice present. Every explicitly designated scalar label in a covariant local-observable family
  sharing that exact domain inherits the same direct affine covariance.
- Strong continuity descends from the cover representation through the exact cover projection's
  quotient-map universal property.
- The dependent 4D scalar chain is transported to the exact double-cover index and yields an affine
  homomorphism and pointwise strong-continuity theorem on the core's existing Hilbert space.
  Cast-eliminating coherence theorems recover every original `U.unitary g` over its projection and,
  on pure translations, the exact `U.translationUnitary a` tied to the joint PVM, stress tensor, and
  mass-gap predicate. Further lift-equality theorems define the descended domain action directly on
  the original uncast `D.domain` and prove affine covariance of the original scalar field and every
  label in the core's explicitly designated scalar-observable sector.
- No cover, representation, field, scalar theory, spinorial realization, or mass gap is constructed.

## 2026-07-19 — two-hundred-fourteenth stone: scalar/tensor covariance separation

Implemented and verified:

- `CovariantLocalObservableFamilyData` now carries an explicit adjoint-closed `scalarLabel` sector.
  Its scalar pullback law requires membership in that sector; unit and distinguished Wightman labels
  are explicit members.
- Arbitrary observable labels are no longer silently assigned scalar Lorentz covariance.
  `ScalarStressCovarianceSeparationData` explicitly excludes every stress-component label from the
  scalar sector, so those labels obey only their rank-two mixing interface.
- Cover-to-affine descent carries the scalar-membership premise throughout, including the exact 4D
  lift-equality bridge. The interpreted `F²` labels in the 3D/4D cores and `(F²)²` in the 4D core are
  explicitly required to belong to the scalar sector. Both cores require explicit scalar/stress
  disjointness.
- Hostile probes expose the sector anchors, adjoint closure, membership-sensitive covariance, and
  scalar membership of interpreted curvature observables. No tensor representation, theory, or
  observable inhabitant is constructed.

## 2026-07-19 — two-hundred-fifteenth stone: finite covariant observable multiplets

Implemented and verified:

- `FiniteLiftCovariantObservableMultipletData` packages nonempty finite component indices inside the
  existing observable family, one genuine complex-linear lift-group representation, pointwise strong
  continuity, trivial component mixing on physical translation lifts, and exact covariance on the
  same common domain and inverse-affine test pullback.
- A mandatory nonzero/non-unit component rejects empty, zero, and unit-only multiplets. Identity and
  composition of mixing are derived from the bundled representation rather than accepted as
  unrelated coefficient laws.
- `FiniteLorentzCovariantObservableMultipletData` separately requires mixing to depend only on the
  projected Lorentz transformation. The base interface deliberately retains possible nontrivial
  cover-kernel action for spinorial multiplets.
- The existing distinguished nontrivial scalar label derives an exact one-component Lorentz
  multiplet with trivial mixing; no new operator or field witness is introduced.
- `FiniteLiftCovariantObservableCoverData` covers any explicit label subset by an arbitrary family
  of finite lift-covariant multiplets. It does not silently factor possible spinorial central action
  through the affine Lorentz projection.
- `LocalObservableCovarianceCoverageData` gives the 3D/4D bosonic observable cores an exhaustive
  scalar/stress/residual classification. Scalar labels use the scalar law, exact stress components
  use only their rank-two law, and residual labels use the finite projected-Lorentz cover. Thus no
  original bosonic-family label lacks covariance and no stress label receives an unrelated duplicate
  representation. Spinorial fields require a separate future graded-locality surface.
- Hostile probes expose nonemptiness, representation identity/composition/continuity, translation
  blindness, same-chain covariance, anti-vacuity, tensorial factorization, scalar recovery, exact
  predicate-indexed coverage, residual exclusions, and exhaustive original-label classification.

## 2026-07-19 — two-hundred-sixteenth stone: completion-audit baseline

Implemented and verified:

- `docs/COMPLETION_AUDIT.md` restates the governing objective as eighteen concrete completion
  criteria and maps every objective family to inspected files, declarations, probes, source records,
  commands, statuses, and unresolved evidence.
- Separate dimension and bridge matrices prevent broad green statuses from standing in for missing
  dimension contracts or coherence theorems.
- Every standard verifier is documented with both its observed baseline result and its coverage
  limit. The audit explicitly records that source hashes do not verify interpretation and builds do
  not verify physical adequacy.
- The living audit is now anchored to fully validated implementation commit `a5d8563` on branch
  `cathedral`: 3,766 build jobs, 7,780 kernel-audited declarations, 603 Lean files, a then-clean
  working tree, and no configured remote. Later audit-metadata commits do not change that validated
  implementation snapshot; final closure must re-anchor once more. The final proposition, witness-level separation, final
  audit closure, push, and PR remain absent.
- The stale claim that non-scalar/non-stress labels lacked finite-dimensional covariance was
  corrected to match the committed exhaustive residual multiplet coverage.
- The audit concludes **not complete** and is a living baseline, not a completion certificate.

## 2026-07-19 — two-hundred-seventeenth stone: multiplet adjoint coherence

Implemented and verified:

- `FiniteLiftCovariantObservableMultipletAdjointPartnerData` relates two existing finite multiplets
  by an exact component-index equivalence, the same family's involutive adjoint labels, and
  coefficientwise complex-conjugate mixing.
- Reverse label coherence is derived from the existing adjoint involution rather than stored as a
  second independent relation.
- Every residual multiplet in `LocalObservableCovarianceCoverageData` now has an exact adjoint
  partner inside the same residual cover. Component-level residual membership prevents that partner
  from importing scalar or stress labels.
- `ScalarStressCovarianceSeparationData` now additionally fixes every Hermitian stress-component
  label under the same global family adjoint, connecting the prior componentwise Hermiticity law to
  the family-level adjoint interface.
- Hostile probes expose exact partner labels, reverse coherence, conjugate coefficients, in-cover
  partner existence, and stress-label fixed points. No partner, multiplet, field, or theory is
  constructed.

## 2026-07-19 — two-hundred-eighteenth stone: derived chart connection regularity

Implemented and verified:

- `PrincipalConnectionData.connectionCoordinatesInExtChartAt_contDiffOn` derives target-wide `C∞`
  regularity of the exact corner-aware inverse-chart connection one-form from the connection's
  existing intrinsic evaluation smoothness when the principal total-space model is finite
  dimensional.
- The proof pulls constant coordinate vectors back to smooth manifold vector fields using Mathlib's
  `VectorField.mpullback`, identifies their exact `mfderivWithin ... (Set.range IP)` transport by
  inverse-chart derivative identities, and reconstructs one-form-valued smoothness from all fixed
  vector evaluations.
- Pointwise `ContDiffWithinAt` is derived at every actual chart-target member; no coordinate
  regularity witness or unrestricted `mfderiv` carrier is substituted.
- `curvatureCoordinatesInExtChartAt_coordinateBianchi_of_finiteDimensional` consumes this theorem,
  removing the supplied regularity and smoothness-order premises from the exact-curvature chart
  Bianchi bridge. Mathlib derives `UniqueDiffOn` and closure-of-interior membership for the extended
  chart target, leaving only exterior naturality and actual target membership explicit.
- Dedicated probes expose target-wide/pointwise regularity and the reduced-hypothesis Bianchi
  theorem. Exterior naturality and descended adjoint-bundle Bianchi remain open.

## 2026-07-19 — two-hundred-nineteenth stone: exterior naturality reduced to Cartan transport

Implemented and verified:

- `PrincipalConnectionExteriorDerivativeData.exterior_coordinatesInExtChartAt_eq_cartan_constantFields`
  derives the coordinate pullback of the certified derivative from the existing manifold Cartan
  certificate on smooth inverse-chart pullbacks of arbitrary constant coordinate vectors.
- `PrincipalConnectionData.extDerivWithin_connectionCoordinates_eq_coordinateCartan_constantFields`
  independently derives Mathlib's `extDerivWithin` side from the exact smooth coordinate connection,
  constant-field differentiability, and chart-target unique differentiability.
- `PrincipalConnectionCoordinateCartanNaturalityInExtChartAt` names the sole remaining equality
  between those intrinsic and coordinate Cartan expressions. It keeps the chart source, model range,
  and actual chart target distinct.
- Degree-two extensionality proves both directions: the exact Cartan equality implies full
  alternating-map exterior naturality, and full naturality recovers that equality. Thus the named
  residual condition is an exact equivalent, not a weaker proxy or stronger unrelated requirement.
- Hostile probes expose both derived sides, the exact residual shape, the equivalence theorem, and
  rejection of a mismatched Cartan value.

## 2026-07-19 — two-hundred-twentieth stone: derived exterior naturality and coordinate Bianchi

Implemented and verified:

- `ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt` proves reusable
  inverse-extended-chart Cartan naturality for every differentiable fixed-value coordinate one-form.
- Its derivative terms use `mfderivWithin_comp`, exact inverse-chart tangent cancellation, and
  pointwise equality on the chart source while preserving `Set.range I` as the tangent-transport
  source. Its bracket term uses Mathlib's `mpullback_mlieBracketWithin`; constant coordinate fields
  have zero bracket.
- Intrinsic connection smoothness discharges the generic theorem's differentiability premise and
  derives `PrincipalConnectionData.coordinateCartanNaturalityInExtChartAt`.
- Every connection-indexed derivative certificate now has derived
  `PrincipalConnectionExteriorDerivativeData.isNaturalInExtChartAt`; naturality is no longer an
  acceptance premise in finite-dimensional principal total-space models.
- `curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional` derives the exact
  same-connection coordinate Bianchi identity at every chart-target point with no naturality,
  regularity, smoothness-order, unique-differentiability, closure, or Bianchi witness.
- Generic and principal hostile probes reject mismatched Cartan transport and nonzero Bianchi
  outputs. Arbitrary-map/two-set naturality, a global arbitrary-manifold positive-degree operator,
  and descended adjoint-bundle Bianchi remain open.

Not yet achieved:

- No concrete inhabitant of the gauge-group certificate has been constructed. Mathlib's algebraic
  `SU(n)` API does not supply the complete manifold/compactness/connectedness/tangent-simplicity
  chain, so positive consistency infrastructure remains open.
- No concrete smooth gauge-bundle-map witness, principal-connection/curvature witness, constructed
  curvature-exterior certificate, canonical arbitrary-manifold exterior operator, complete gauge-
  covariance result, symmetry-group construction, quantum-theory witness, existence theorem, or
  satisfying mass-gap declaration exists. Finite-dimensional curvature structure and conditional
  intrinsic descended Bianchi are now derived, but construct no geometric or quantum witness.
- Bosonic observable labels now have exhaustive scalar/stress/residual covariance classification;
  residual labels are covered by finite projected-Lorentz multiplets with component-level exclusion
  of scalar/stress labels and exact in-cover adjoint/conjugate-representation partners. Spinorial
  graded locality remains a separate open interface.
- A preliminary `FourDimensionalCurrentStrengthUniversalAcceptance` now has the correct outer
  quantifier over every caller-supplied exact compact-simple gauge certificate and existentially
  packages all construction-specific classical and quantum carriers into one same-core witness.
  It is intentionally uninhabited and explicitly not final. Wrapper probes preserve the core's
  nonzero Wightman-field witness and nonzero same-PVM physical time generator, so the packaged
  `Nonempty` cannot be mistaken for a trivial quantum chain. A conditional projection theorem now
  shows that inhabiting the preliminary universal proposition would give every exact input a witness
  with a positive finite same-spectrum gap and explicit nonzero/non-unit field; the theorem does not
  inhabit that premise. Existing source-strength debts must
  close before a full Clay acceptance proposition can replace it.
- No standalone Git remote is configured in this checkout. The tested candidate
  `git@github.com:elmismisimoxhunca/lean-yangmills-adaly.git` does not exist, and the available SSH
  credential was scoped to the retired repository. No push or PR is evidenced locally; remote
  publication remains blocked/unverified rather than globally disproved.
- Clay, Hall, Aharony–Seiberg–Tachikawa, and Freed artifacts are pinned. Clay equation (1) now
  anchors the action formula, invariant quadratic form, and chosen orthonormal curvature
  contraction and relative-to-designated-measure action. Generic bilinear contraction is now proved
  basis-independent, the exact dependent adjoint-fiber pairing is packaged bilinearly, and the
  generic degree-two adapter is applied to the exact curvature. The resulting pointwise contraction
  is basis-independent and the existing action is proved to integrate it, but a general Hodge-star
  bridge and metric-volume compatibility remain pending. OS-I, correcting OS-II, Wightman 1956,
  and Streater–Wightman source artifacts are now acquired and verified. Scalar tempered Schwinger
  families, the exact printed OS-II control, carrier-exact `(E0′)`, and source-carrier `(E1)`–`(E4)`
  are implemented as uninhabited requirements. Corrected same-lift reconstruction acceptance now
  quantifies over universe-relative alternative Hilbert realizations, but no output, equivalence, or
  reconstruction theorem is constructed; ambient family/exact-source Wick coherence is not silently
  identified with an exhibited reconstructed output. Wilson and Osterwalder–Seiler
  lattice sources are likewise pinned; finite periodic bonds, plaquette holonomy, local gauge
  transformations, Wilson-type action, normalized product Haar, conditional Gibbs data,
  support-local loop expectations, finite-cutoff reflection-positivity checker, and scaling/
  expectation-limit interfaces are explicit. No Gibbs, positivity, scaling, or continuum-bridge
  inhabitant is constructed, and measure/field/OS continuum identification remains unimplemented.
  Wilson's OPE paper and the Gross–Wilczek/Politzer asymptotic-freedom papers are pinned. Generic
  weak OPE data, the basic exact `F²` interpretation bridge, and supplied group-normalized one-loop
  beta coefficient are implemented, but arbitrary curvature-polynomial/covariant-derivative
  interpretation, operator mixing, calculated OPE coefficients, scheme dependence, and perturbative
  remainder semantics remain unimplemented. The physical joint translation-PVM
  and invariant-mass-gap predicates are now anchored to the visually verified SNAG discussion, and
  the same PVM supplies the Hamiltonian interval view; any satisfying spectral datum and the final
  acceptance integration remain absent.

### Smooth-descent/principal-Bianchi bridge

`YangMills.Geometry.PrincipalCurvatureSmoothDescentBianchiBridge` now joins two exact branches of
the same indexed curvature. In every designated bundle chart, the coordinate of the constructed
smooth adjoint-bundle-valued curvature is the principal curvature evaluated at that chart's local
section and exact tangent lifts; throughout the inverse extended chart centered at that section,
the same principal representative satisfies the already-derived coordinate Bianchi identity.
Hostile probes reject both a mismatched descended coordinate and a nonzero representative Bianchi
output. This result-specific bridge was deliberately weaker than intrinsic descended Bianchi; the
later positive-degree construction now supplies the adjoint-valued `D_A F` three-form and derives
its conditional intrinsic zero without changing this earlier representative theorem.

### Principal-connection gauge pullback

`YangMills.Geometry.PrincipalConnectionGaugePullback` now constructs the pullback of a smooth
principal connection by the exact tangent map of an existing smooth gauge automorphism. Gauge
equivariance differentiates to preserve fundamental vertical generators and commute with fixed
right translations, deriving vertical normalization and right-adjoint equivariance of the result.
Smoothness is derived by transporting local test vector fields through the gauge diffeomorphism and
its smooth inverse. Identity and multiplication laws expose the contravariant pullback order,
equivalently a right gauge action convention. Hostile probes reject changed vertical generators and
malformed composition. `YangMills.Geometry.PrincipalCurvatureGaugePullbackFormula` now generalizes
smooth gauge pullback to every fixed form degree, proves exact Lie-bracket-wedge pullback
naturality, and constructs the curvature formula from the exact pulled derivative carrier. That
assembled formula is proved equal to the pullback of the original same-index curvature, including
an exact tangent-evaluation theorem. Reusable diffeomorphism infrastructure now derives tangent-map
invertibility, exact pushed/pulled tangent fields, image-set smoothness and unique-differentiability,
within-set chain rules, and Lie-bracket transport. It proves full Cartan-expression naturality and
constructs the pulled exterior certificate under the explicit `CompleteSpace EP` premise required
by Mathlib's public bracket theorem. Finite-dimensional total-space models derive that premise.
`YangMills.Geometry.PrincipalConnectionGaugeExteriorDerivative` therefore constructs exact
transformed exterior data and proves canonical principal curvature pullback naturality, with hostile
mismatch probes. `YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint` canonically selects the
unique associated group function from torsor data, proves its pointwise action, uniqueness, and
right-action conjugation laws, and differentiates gauge projection preservation. The exact original
curvature structure certificate then removes the vertical difference between gauge-transported and
fixed-right-translated tangents, deriving the evaluated local law with `Ad(g_ϕ(p)⁻¹)`. Hostile probes
reject the opposite adjoint factor whenever the two evaluated factors are explicitly distinguishable.
`YangMills.Geometry.SmoothGaugeAssociatedFunction` identifies the unique selected function with the
second coordinate of each transformed canonical local section. Every chart point is reconstructed
from that section and its second coordinate, so the conjugation law expresses `g_ϕ` as a smooth
chart formula. Exact chart-source regularity and atlas coverage derive global `C∞` smoothness; no
regularity of `Classical.choose` is assumed.
`YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation` defines left Maurer–Cartan
trivialization and its exact pullback along `g_ϕ`. The derivative of the variable principal right
action is proved to split into fixed right translation plus the fundamental vector generated by
`g_ϕ⁻¹dg_ϕ`; connection right-equivariance and vertical normalization then derive the evaluated
affine formula with the exact inverse adjoint factor and plus sign. Hostile probes reject omission,
sign reversal, and the non-inverted adjoint factor when distinguishable.
`YangMills.Geometry.SmoothAssociatedMaurerCartanPullback` proves smoothness of the exact
inverse-adjoint transform of every supplied smooth connection. The affine identity then identifies
the unchanged associated Maurer–Cartan carrier with the difference of that smooth form and the
smooth gauge-pulled connection, deriving an exact smooth-form bundle without an extra regularity
field. `YangMills.Geometry.PrincipalCurvatureGaugeStructure` derives the canonical transformed
curvature structure certificate from the exact original certificate: gauge projection preservation
transports horizontality, while differentiated commutation with right translation transports
right-adjoint equivariance. Pointwise descent is identified by the selected-section
`Ad(g_ϕ⁻¹)` coefficient and, equivalently, by inverse-shifting the principal representative while
retaining the original coefficient. `YangMills.Geometry.AdjointBundleGaugeAction` constructs the
covariant quotient action `[p,X] ↦ [ϕ(p),X]`, proves base preservation and exact group/inverse laws,
and restricts it to the actual dependent fibers. The transformed pointwise curvature and every
evaluation of the exact smooth descended package equal the inverse induced fiber action on the
original value. This is covariance, not equality with the original adjoint-valued curvature.
`YangMills.Geometry.AdjointBundleGaugeContinuousLinear` proves the selected coordinate formula is
exactly the forward `Ad(g_ϕ)` operator and packages the unchanged action on every fixed dependent
fiber as a continuous real-linear equivalence. Its inverse carrier is definitionally the inverse
gauge action, and identity/composition laws hold at the bundled level.
`YangMills.Geometry.AdjointBundleGaugeHomeomorph` descends continuity through the defining quotient
map and packages the covariant quotient action with inverse gauge carrier as a homeomorphism.
Transport through the exact quotient/dependent carrier homeomorphism yields a base-preserving
homeomorphism for the named dependent-total-space topology; each fixed-fiber restriction is exactly
the established continuous-linear equivalence.
`YangMills.Geometry.AdjointBundleGaugeDiffeomorph` derives the arbitrary model-trivialization
formula `(b,X) ↦ (b,Ad(g_ϕ(s(b)))X)`, proves it smooth on the exact chart target, and uses exact
compatibility of those trivializations with the named quotient atlas to globalize forward and
inverse `C∞` regularity. The quotient homeomorphism is therefore packaged as a diffeomorphism with
unchanged carrier.
`YangMills.Geometry.AdjointBundleGaugeSmoothVectorBundleAutomorphism` repeats the exact local
calculation in the named dependent smooth-vector-bundle structure and derives a base-preserving
`C∞` total-space diffeomorphism. Its carrier is the existing dependent homeomorphism and its
restriction to each fixed fiber is exactly the established continuous-linear equivalence. This
completes the layered smooth vector-bundle-automorphism packaging without replacing either exact
carrier.
`YangMills.Geometry.AdjointBundleGaugeInvariantPairing` then applies the exact forward coordinate
law and adjoint invariance to prove that simultaneous covariant action on both arguments leaves the
descended fiber pairing and its quadratic value unchanged. This is pointwise pairing invariance,
not by itself curvature-contraction, density, action, or observable invariance.
`YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance` combines that theorem with exact
inverse-induced-action curvature covariance to prove pointwise invariance of the chosen and
basis-independent canonical densities for the same pulled connection, derived exterior datum, and
derived structure certificate.
`YangMills.Classical.EuclideanActionGaugeInvariance` transports the exact analytic datum across
that equality, retaining the designated Borel measure, positive coupling, and outer coefficient
definitionally. It derives invariance of the integrated relative-to-measure action for vertical
gauge transformations over the identity base map. No base-diffeomorphism, measure-pushforward, Jacobian, or metric-volume invariance is inferred.
`YangMills.Observables.CurvaturePowerGaugeTransport` transports the existing basic and finite
`1`, `F²`, `(F²)²` interpretations to the exact pulled chain. Their classical carriers are equal,
and the same quantum family, every label, operator nontriviality witness, and quartic anti-collapse
witness are retained. This is exact same-family transport, not a quantum gauge action.
`YangMills.Observables.QuantumGaugeObservableAction` independently requires an algebraic gauge-group
representation on the exact common invariant domain and derives its conjugation action on arbitrary
endomorphisms. A separate invariance certificate is indexed by one exact designated action, so it
cannot silently select a disconnected convenient action, and requires every labeled smeared
operator to be fixed by that action. No unitary or continuous gauge representation or nonidentity
element is required; triviality of a physical gauge representation is not incorrectly excluded.
`YangMills.Observables.QuantumGaugeCurvaturePowerCoherence` applies that exact-action certificate
to every label in the interpreted `1`, `F²`, `(F²)²` fragment and rejects substitution of a
different action at the quartic label.
`YangMills.Observables.SmoothPrincipalGaugeQuantumObservableAction` specializes both the action and
its exact-action invariance certificate to the canonical group of smooth automorphisms of one fixed
principal bundle, without constructing a representation. Further classical/quantum
transformation-law coherence and the broader observable grammar remain open.
`YangMills.Geometry.DirectAssociatedMaurerCartanPullbackSmooth` now derives smoothness of the exact
associated left Maurer–Cartan pullback directly from smooth tangent maps of the gauge function and
`(g,h) ↦ g⁻¹h`, with no supplied principal connection. It packages the unchanged carrier as a
smooth one-form.
`YangMills.Geometry.AssociatedMaurerCartanStructureCandidate` defines the universal left form,
calculates its Cartan expression on canonical left-invariant fields as the negative Lie bracket,
and verifies the exact self-wedge factor two. The associated form is proved equal to the exact
pullback of that universal carrier, while `-1/2[α∧α]` is packaged as a smooth same-carrier derivative
candidate.
`YangMills.Mathematics.OneFormCartanFieldExtension` proves that normed-space Cartan expressions
only depend on field values, packages exact corner-aware centered-chart coordinate fields and their
regularity, proves coordinate-level extension independence, and derives intrinsic independence from
any already supplied Cartan certificate.
`YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport` now transports the complete
intrinsic Cartan expression for arbitrary smooth fields to the exact corner-aware centered-chart
set, and derives intrinsic extension independence from explicit coordinate-form differentiability.
`YangMills.Mathematics.SmoothManifoldOneFormExtChartRegularity` reconstructs the complete degree-one
alternating-map-valued chart carrier from fixed-vector evaluations using a finite basis. Thus
finite-dimensional intrinsic Cartan extension independence now requires no certificate or caller
regularity witness.
`YangMills.Geometry.UniversalMaurerCartanExteriorDerivative` uses this theorem to replace arbitrary
local fields by left-invariant extensions, constructs a genuine all-fields exterior-derivative
certificate with derivative `-1/2[θ∧θ]`, and proves the exact universal group-level structure
equation.
`YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates` identifies every
certificate with centered-chart `extDerivWithin` and proves Mathlib pullback naturality for an
arbitrary smooth map's written-chart representative on the exact chart-safe set.
`YangMills.Geometry.AssociatedMaurerCartanDerivativePullback` proves the associated smooth candidate
is exactly the raw pullback of the certified universal derivative. Exact chart-safe carrier and
locality bridges now yield `pullbackSmoothMapOfForms`, which derives an arbitrary-smooth-map Cartan
certificate from exact smooth pullback packages in finite-dimensional models.
`YangMills.Geometry.AssociatedMaurerCartanExteriorDerivative` applies it to the associated gauge
function, certifies the existing derivative candidate, and proves the exact normalized associated
Maurer–Cartan equation.
`YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinates` now converts every actual
dependent-fiber adjoint-valued form into a fixed-model normed-space form on the exact overlap of a
base extended chart and designated principal chart. The coordinate formula retains quotient-derived
fiber coordinates and `mfderivWithin ... (Set.range IB)` tangent transport, while hostile probes
prevent in-domain nonzero values from being erased by outside-domain totalization.
`YangMills.Mathematics.ContinuousAlternatingMapSmoothEvaluation` reconstructs smooth families of
finite-arity continuous alternating maps from all fixed-tuple evaluations, including arity zero.
`YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinateSmooth` combines this with smooth
local tangent-field evaluation to derive full `C∞` base-coordinate regularity within the exact
overlap for every designated atlas chart and finite-dimensional base model. No smoothness across the
zero-totalization boundary is claimed.
`YangMills.Geometry.PrincipalConnectionLocalAdjointCalculus` now packages on that overlap the exact
local potential from the principal connection, the exact smoothly descended certified curvature,
and the typed degree-three expression `dF + [A∧F]`. Evaluation theorems preserve the same local
section, tangent lifts, quotient coordinate, and inverse-chart transport.
`YangMills.Geometry.PrincipalConnectionLocalExteriorNaturality` derives local-section pullback
naturality from `ContMDiffOn`, recentering at every overlap point and using set-germ equality so the
fixed `baseExtChartDomain` remains the `extDerivWithin` calculus set.
`YangMills.Geometry.PrincipalConnectionLocalCurvatureCoherence` then proves the exact descended `F`
equals the coordinate curvature of that same local `A`.
`YangMills.Geometry.PrincipalConnectionLocalBianchi` derives smoothness of `A`, unique
differentiability of the exact overlap, and its closure-of-interior condition, then applies the
within-coordinate Bianchi theorem to prove the exact same-chain local `dF + [A∧F]` expression
vanishes at every overlap point.
`YangMills.Geometry.PrincipalConnectionDescendedBianchiZero` identifies every designated-atlas-chart local expression
with the corresponding base-chart coordinate of the existing intrinsic smooth zero
adjoint-bundle-valued three-form. This is a result-specific global-carrier bridge, not construction
of a general positive-degree operator.
`YangMills.Mathematics.ContinuousAlternatingMapProjectionIndependence` uses Mathlib's finite
multilinear telescope to prove arbitrary-degree kernel/projection independence.
`YangMills.Geometry.PrincipalFormLiftIndependence` applies it to horizontal fixed-value principal
forms of every degree and canonical local tangent lifts; degree three is explicitly probed and the
existing degree-two horizontality predicate is definitionally compatible.
`YangMills.Geometry.PrincipalFormSmoothDescent` derives right-adjoint representative independence,
actual dependent-quotient-fiber descent, arbitrary designated-chart coordinates, and smooth descent
for every degree. Degree three is probed explicitly and the existing degree-two predicates and
selected carrier are definitionally compatible.
`YangMills.Geometry.PrincipalFormCovariantExteriorCandidate` constructs the exact smooth
positive-degree total-space expression `dω + [Θ ∧ ω]` from the same principal connection, smooth
input form, and supplied ordinary exterior certificate. Its exact derivative and connection bracket
carriers are exposed, its `2 → 3` specialization is probed, and hostile probes block an unrelated
derivative or omitted nonzero bracket.
`YangMills.Mathematics.LieGroupAdjointBracket` packages inner conjugation as a smooth diffeomorphism,
calculates its pushforward on left-invariant fields, and applies Mathlib bracket pullback naturality
to prove that the project's derivative-defined adjoint preserves the intrinsic tangent Lie bracket.
This closes the bracket-covariance ingredient for future candidate equivariance.
`YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeDiffeomorph` transports the complete
positive-degree Cartan expression and exact pulled certificate through smooth diffeomorphisms on the
exact image set under Mathlib's required source-model completeness hypothesis.
`YangMills.Geometry.PrincipalFormCovariantExteriorBracketEquivariance` combines connection/input
equivariance with adjoint bracket preservation to prove the exact bracket correction is
right-adjoint-equivariant in every degree.
`YangMills.Mathematics.LieBracketWedgeHorizontalVertical` and
`YangMills.Geometry.PrincipalFormCovariantExteriorVertical` derive the exact signed bracket term on
one vertical slot, vanishing on two vertical slots, fundamental-vector normalization, and the
conditional cancellation theorem proving candidate horizontality from the precise negative
ordinary-derivative value. The remaining gap is deriving that value from infinitesimal
right-action/adjoint differentiation; it is not accepted as candidate data.
Together with the previously proved verticality of fundamental vectors,
`YangMills.Geometry.PrincipalVerticalTangentGeneration` derives from smooth local triviality that
`ker(dπ)` is exactly the image of the infinitesimal orbit map. For a supplied pointwise connection,
vertical normalization recovers the unique generator as the connection-form value.
`YangMills.Geometry.PrincipalFundamentalVectorField` proves every fixed generator produces a global
`C∞` field, every value is vertical, and every smooth identity-based group curve with the specified
velocity generates the expected right-action tangent. Finite right-adjoint equivariance is exposed
along these curves without assuming a Lie exponential or global flow.
`YangMills.Mathematics.LieGroupRightInvariantField` constructs the smooth right-invariant field, proves its exact invariance under every right
translation, and proves that its exact left-trivialized coefficient is `Ad(g⁻¹)Y`; those model coordinates are
smooth. `YangMills.Mathematics.LieGroupLeftTrivializedFieldDerivative` now uses the certified
universal Maurer--Cartan equation to compute the derivative of any smooth field's left-trivialized
coefficient. It derives the exact `-[X,Y]` formula for the right-invariant field from the narrowly
isolated premise that the relevant left/right manifold Lie bracket vanishes at the identity. The
`YangMills.Mathematics.MixedPartialLieBracket` proves the unrestricted and corner-safe within-set
Schwarz cancellation theorem for opposite partial-derivative fields under exact first-partial
normalization hypotheses, while
`YangMills.Mathematics.LieGroupChartMultiplication` proves exact `C²` regularity of identity-centered
chart multiplication within `range I ×ˢ range I`.
`YangMills.Mathematics.LieGroupInvariantFieldChartIdentity` derives both exact first-partial
normalizations, zero within-range bracket of the normalized partial fields, and identity-point
agreement of Mathlib's chart pullbacks of the left- and right-invariant fields with those partials.
`YangMills.Mathematics.LieGroupInvariantFieldChartTarget` upgrades those pointwise agreements to
exact target-wide field equalities while retaining the chart target and model range separately.
`YangMills.Mathematics.LieGroupInvariantFieldCommutation` then derives the exact Mathlib manifold
Lie bracket's vanishing at the identity. Finally,
`YangMills.Mathematics.LieGroupInfinitesimalAdjoint` combines that commutation with the certified
universal Maurer--Cartan equation to prove `d(Ad(·⁻¹)Y)₁(X) = -[X,Y]` in exact model coordinates.
`YangMills.Geometry.PrincipalFormInfinitesimalEquivariance` applies this formula to the exact
principal-orbit coefficient chain for arbitrary degree, with no exponential map. Horizontality
proves every nondistinguished coefficient derivative vanishes. The positive-degree Cartan formula
then yields the required ordinary vertical derivative from one explicit termwise triangular
bracket-evaluation vanishing premise. `YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin` localizes the entire Cartan
reduction to any explicit open calculus set while retaining all-group orbit adaptation.
`YangMills.Geometry.PrincipalOrbitAdaptedProductField` constructs prescribed-value fields in
base/group product coordinates, smooth on an open centered-base-chart source times the whole group,
with exact all-orbit right transport and normalized fundamental/right-invariant bracket zero. The
`YangMills.Geometry.PrincipalOrbitAdaptedProductBracket` now derives the exact product-manifold
within-bracket vanishing theorem for the vertical fundamental and adapted fields at the normalized
center, with derivatives taken within the natural open product domain.
`YangMills.Mathematics.PartialDiffeomorphLieBracket` packages exact open-restriction bracket
naturality and zero transport, including smooth-principal-trivialization specializations.
`YangMills.Geometry.PrincipalOrbitAdaptedTotalField` transports the adapted product field to the
principal total space at points with normalized fiber coordinate `1`, proving arbitrary prescribed
value, exact open-source smoothness, all-group orbit adaptation, and bracket zero with the principal
fundamental field. `YangMills.Geometry.PrincipalNormalizedTrivialization` left-shifts the fiber
coordinate to normalize any covered point to group coordinate `1`, proves forward/inverse
smoothness, conservatively extends the designated atlas by that one chart, and removes the
coordinate-normalization premise from the adapted-field existence theorem.
`YangMills.Geometry.PrincipalCommonAdaptedTotalFields` strengthens this to an arbitrary indexed
family on one exact common normalized-trivialization source, retaining every prescribed value,
smoothness, all-orbit adaptation, and zero bracket against the designated fundamental field.
`YangMills.Geometry.PrincipalCartanTriangularDischarge` uses that family to discharge every
triangular evaluation: brackets involving the distinguished slot vanish (up to skew symmetry),
while horizontality kills terms where that fundamental slot survives. It derives the exact ordinary
vertical derivative, unconditional cancellation of the full candidate on a fundamental slot, and
full candidate horizontality via vertical tangent generation. The termwise premise is never treated
as candidate data. `YangMills.Mathematics.SmoothManifoldDifferentialFormOutputLinear` transports
smooth forms and positive-degree certificates through exact output continuous-linear maps, while
`SmoothManifoldDifferentialFormDiffeomorphPullback` constructs the exact smooth pullback carrier.
`YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance` compares output-`Ad(g⁻¹)` and
right-translation-pulled certificates on one common-source field family, proving ordinary-derivative
and full-candidate right-adjoint equivariance.
`YangMills.Geometry.AdjointBundlePositiveCovariantExteriorDerivative` descends the same candidate
into the actual dependent adjoint-bundle fibers as a smooth positive-degree form and specializes it
to the exact same-connection curvature as a smooth adjoint-valued three-form carrier `D_A F`. This
specialization remains conditional on the existing same-index curvature structure certificate and a
supplied ordinary curvature exterior certificate. `SmoothManifoldDifferentialFormExtChartRegularity`
now derives arbitrary-degree alternating-map-valued `C∞` regularity on the exact chart target and
corner-model range, and `ManifoldPositiveDegreeExteriorDerivativeExtChart` identifies every such
certificate's centered inverse-chart derivative with the exact `extDerivWithin`, coherently with the
old one-form theorem at `n = 0`.
`YangMills.Geometry.PrincipalConnectionIntrinsicBianchiZero` now identifies the exact principal
candidate at every chart center with the existing same-connection coordinate Bianchi expression,
uses inverse-chart derivative cancellation to derive global principal zero, and proves the bundled
intrinsic `D_A F` equals the canonical smooth zero adjoint-valued three-form. This theorem accepts no
zero or naturality bridge. `YangMills.Geometry.PrincipalCurvatureStructureFiniteDimensional`
separately derives the formerly supplied curvature structure: connection-specific Cartan calculus
uses `Θ(X#)=X` to prove horizontality with the exact half-self-wedge normalization, while exterior
and bracket transport prove right-adjoint equivariance. The finite-dimensional intrinsic Bianchi
wrapper therefore accepts no structure witness. The full triangular Cartan expression transports
for arbitrary local smooth fields through the exact set
`(extChartAt I p).symm ⁻¹' s ∩ range I`, is independent of admissible field extensions in finite
dimensions without using a certificate, and is local under equality of set germs.
`YangMills.Geometry.PrincipalCurvatureExteriorCertificateFiniteDimensional` combines this
infrastructure with coordinate Bianchi to construct the exact ordinary curvature certificate
`dF = -[A∧F]`. Consequently its derived finite-dimensional intrinsic Bianchi theorem accepts only
the connection and the exact connection-indexed first exterior data. Construction of that first
exterior datum, and generic arbitrary-manifold curvature structure/exterior construction, remain
open.

The four-dimensional `CurrentStrength` integration record now requires one exact algebraic quantum
action of its canonical smooth principal gauge group on its same observable family and one
all-label invariance certificate indexed by that exact action. Derived projections connect every
interpreted `1`, `F²`, `(F²)²` label to the same action; hostile probes reject changed operators.
`YangMills.Observables.CurvatureAllPowersInterpretation` extends this with a natural-indexed family for every natural
power `(F²)ⁿ`, with exact classical carriers and exact restriction at exponents zero, one, and two.
The four-dimensional core requires all such labels in its same scalar sector and derives their
invariance under the same designated action. No injectivity or all-power anti-collapse is claimed.
This adds coherence only: it constructs no representation and does not close the missing observable
grammar or further classical/quantum transformation-law debt.

`YangMills.Minkowski.StressEnergyTrace` now defines the mostly-minus trace directly from the exact
same-family stress components and proves its four-dimensional `T⁰⁰-T¹¹-T²²-T³³` expansion.
`YangMills.Renormalization.StressTensorTraceAnomalyNormalization` retains the source
`β(g)/(2g)` convention and requires an explicit source-to-project renormalized `F²` scale for the
outer `(4g²)⁻¹` action convention; `β(g)/(2g³)` is derived only after that supplied bridge.
`YangMills.Renormalization.StressTensorTraceAnomaly` exposes separate physical-bra, on-shell-bra,
physical-ket, on-shell-ket, and nonzero-momentum-test predicates. Its anomaly identity is required
only on their exact admissible conjunction, and one admissible triple must detect the existing
interpreted `F²`; nonzero trace action follows. The four-dimensional `CurrentStrength` core now
requires this exact normalization, selection, and reduced identity on its already connected stress,
`F²`, normalized-beta, and classical-reference chain. Collins–Duncan–Joglekar's unrestricted
mixing family is not erased or promoted to an all-domain operator identity. No datum is constructed.

The previously unindexed user literature bundle under `/root/` is now fully ingested. Seven of its
33 PDFs are byte-identical to already canonical Clay, Freed, Aharony, Hall-notes, OS-I, OS-II, and
Wightman artifacts. Twenty-six distinct artifacts are now retained or added to the Collins record,
with exact native text extraction for 31 bundle PDFs overall. The two image-only Royal Society
papers, Atiyah–Hitchin–Singer 1978 and Atiyah–Bott 1983, retain the updated Mathpix extractor's raw
provenance/line artifacts, calibrated per-printed-page machine drafts, and independent visual
adjudications; the extractor selftest passes, and the adjudications demonstrate why raw confidence
flags are not sufficient for mathematical citation. `docs/SUPPLIED_SOURCE_INGESTION_AUDIT.md`
records every disposition and its impact on current definitions. The audit validates the current
principal geometry, physical-reduced trace, and generic weak-OPE scope; closes known source
acquisition debt for rigorous 2D evidence, Hodge/volume, Poincaré/`SL(2,ℂ)`, Hall–Wightman analytic
continuation, and BRST/EOM operator mixing; and leaves their Lean construction honestly open.
Singer's Corollary 4 is now a scoped negative warning against future continuous global gauge choices
in the stated `S⁴`/analogous `S³` setting, not an unrestricted no-section claim for every carrier.
No source ingestion constructs a theory, acceptance witness, or mass gap.

The first source-enabled 2D continuum stone is now formalized as the uninhabited
`TwoDimensionalGaugeFixedHolonomyMeasureData`. Independent rereading of Driver corrected a tempting
but false design: the gauge group does not act on the complete-axial-gauge probability carrier.
Instead the exact probability law lives on a gauge-fixed sample type, an explicit restriction map
lands in a separate ambient connection type, gauge transformations act there, and random holonomy
and physical observables are pulled back through that exact restriction. The record retains
Driver's target-left endpoint covariance and reverse multiplication order for path concatenation,
requires normalization and nonempty designated path/observable carriers, and exposes hostile probes
against zero probability and disconnected holonomy/invariance replacements. It constructs no
measure.

The next 2D stone extracts the single-group normalized compact Haar construction from the lattice
namespace into `Mathematics.NormalizedCompactHaarMeasure`, preserving the existing derived left,
right, and inversion invariance while removing a continuum-to-lattice dependency. The uninhabited
`TwoDimensionalSelectedLoopHaarDensityLawData` then adds one exact closed loop with strictly
positive supplied area. Its same-chain sampled-holonomy pushforward is exactly an `ENNReal`
central/inversion-symmetric density against that canonical Haar probability; density-measure
normalization and nonzeroness are derived, and an exact existing physical-observable/class-function
bridge derives the selected expectation formula. Closedness also derives conjugation by one
endpoint value from the existing open-path covariance.

Neutral `normalizedCompactHaarDensityConvolution` now fixes the exact source convention
`(f⋆g)(z)=∫f(x)g(x⁻¹z)dμ_H`. The uninhabited
`TwoDimensionalSelectedLoopConvolutionSemigroupData` is indexed by the unchanged marginal law and
requires every positive-time density to be normalized, the same family to satisfy exact
addition/convolution, and its measures to converge weakly to the identity against every continuous
complex test. On the intended Hausdorff compact Lie group, where continuous tests distinguish the
identity, this blocks a time-constant Haar idempotent. The exact selected area
is proved to split into two positive half-area density factors with the same primitive orientation.
The next reusable calculus stone constructs scalar first and iterated derivatives by applying the
actual manifold derivative to the already constructed right-invariant fields. Driver's
orthonormal-basis sum is `rightInvariantScalarLaplacianInBasis`. A nonempty
`InvariantPairingOrthonormalBasisData` is tied to the exact explicit invariant pairing, while the
uninhabited `RightInvariantPairingLaplacianData` requires every other basis orthonormal for that same
pairing to compute the identical operator. Constant annihilation is derived.

The uninhabited `TwoDimensionalSelectedLoopHeatEquationCoreData` is indexed by the invariant pairing,
unchanged selected-loop density law,
unchanged convolution semigroup, and pairing Laplacian. It supplies one strictly positive real
representative that is spatially `C∞` at every positive time and is tied pointwise by
`ENNReal.ofReal` to the same `ENNReal` density. Its ordinary time derivative must equal exactly
`+½` times the same Laplacian. Real centrality and inversion symmetry are derived through the
bridge. It has compact Lie-group scope with no phantom compact-simple alias or index. No density or
PDE solution is constructed.

The uninhabited `TwoDimensionalSelectedLoopBrownianRealizationData` now consumes the general compact
Lie heat core without a compact-simple index and adds an exact probability law on
an independent process sample carrier. The same process starts at the group identity almost surely,
has almost-surely continuous `NNReal`-time paths, and has mutually independent consecutive right
increments; every positive increment is assigned the unchanged normalized-Haar density law. Applying
that law at one positive time derives process-carrier normalization rather than storing it. The
one-time marginal is derived from the identity start and stationary increment rather than stored
again. From the almost-sure continuous-path event, a measurable null hull of all discontinuity
points is constructed. Replacing paths by the identity on that hull gives an everywhere-continuous
jointly `NNReal × Ω` measurable modification, simultaneously almost surely equal to the original at
all times. Identity start, every finite monotone mutual right-increment independence law, every
fixed-time law, and every positive stationary right-increment law are unchanged. These derived laws
repackage the modification as a new `TwoDimensionalSelectedLoopBrownianRealizationData` on the exact
same sample carrier and probability measure, with joint measurability exposed as a theorem. Every
finite time-evaluation vector is measurable and has exactly the original finite-dimensional
distribution. At the selected positive area, the modified marginal as well as the original marginal
is proved exactly equal to the sampled loop-
holonomy pushforward from the original gauge-fixed continuum nucleus. No process or Brownian motion
is constructed.

The pointwise metric bridge now makes the previously private inverse of left Maurer–Cartan
trivialization public and constructs `lieGroupInvariantMetricInner` by precomposing both slots of the
exact invariant pairing. Symmetry and strict positivity are derived. Fixed left translation leaves
coefficients unchanged; fixed right translation gives exactly `Ad(h⁻¹)`, so the same adjoint-
invariance field derives bi-invariance. The reusable
`positiveBilinear_unitEllipsoid_isVonNBounded` theorem minimizes the quadratic form on the compact
unit sphere and proves the finite-dimensional von Neumann-bounded unit-ellipsoid obligation; the
exact tangent-fiber form now satisfies it. The parameter-dependent inverse-left-translation
derivative is also proved smooth in Mathlib's exact tangent coordinates at every center. Reusable
finite-dimensional mathematics proves smooth diagonal precomposition of a continuous bilinear map.
On each exact tangent-trivialization base set, the two nested Hom-bundle coordinates are proved equal
to that polynomial model; neighborhood equality supplies dependent-section smoothness and packages
`lieGroupInvariantContMDiffRiemannianMetric`. The Laplace–Beltrami comparison remains open. No
planar embedding, simplicity theorem, YM measure,
general face product, refinement, gluing, or lattice-limit theorem is constructed. As the first
finite-graph prerequisite, `OrientedEdge` stores only one group coordinate per underlying edge,
reverse orientation evaluates by inversion, finite words multiply later traversals on the left, and
reversing a word gives inverse holonomy. Exact oriented endpoints define the target-left vertex-
gauge action; composability cancels all internal gauge factors, leaving endpoint covariance and
start-vertex conjugation for a closed word. The exact finite product of canonical normalized Haar
probability over those underlying edges is constructed; its edge marginals are Haar and every exact
endpoint gauge action preserves it. Finite oriented-word holonomy is measurable, as is every finite
product of supplied measurable nonnegative density slices; this defines a generic product-Haar
`withDensity` carrier. Arbitrary finite face labels/words do not imply normalization, and the
face-free finite endpoint reduces exactly to unweighted product Haar. This is finite algebra and
measure theory only: no arbitrary `Face` type is misrepresented as an actual planar complement
component. The new uninhabited `TwoDimensionalSimpleBoundaryPlanarGraphData` instead demands a
literal `ℝ²` realization of every ambient path coherent with reversal/concatenation, injective edge
arcs, separated vertices, crossings only at shared endpoints, exact disjoint decomposition of the
trace complement into one unbounded and all bounded connected open regions, and positive area equal
to coordinate Lebesgue volume. Every face word is nonempty, closed, composable, underlying-edge
nodup, and segmentwise realizes an injective-on-`[0,1)` once-around frontier parameterization, so a
doubled circuit is rejected. It permits face-free graphs. This is a topological Jordan-boundary
subclass: every selected edge now carries a concrete strictly partitioned finite decomposition into
vertical affine segments or affinely reparameterized `C¹` horizontal graphs. This is documented as
a normalized parameterization strengthening of Driver Definitions 3.1/3.8, not their verbatim
speed convention. A second finite connected-cell decomposition of the complement after adjoining
the x-axis retains Definition 6.1's finite-component condition. An uninhabited
`TwoDimensionalSimpleBoundaryFaceProductLawData` now states the corresponding restricted
Jordan-subclass formula universally for every measurable, integrable finite vertex-gauge-invariant
complex function on the exact edge configuration. Each such function is tied to an existing ambient
physical observable through the same selected paths, and its original gauge-fixed expectation is
required to equal integration against exact product Haar weighted by the unchanged selected density
at exact geometric areas and boundary words. A designated exact unit member derives normalization
and nonzeroness of this weighted carrier; neither is accepted independently. No graph or face law
instance is constructed. A new reusable `BoundaryConnectedWordCertificate` defines finite graph
bridges by the absence of an edge-avoiding source-to-target oriented path, balances bridge uses once
in each orientation, bounds nonbridge use to one total occurrence, and derives that any repeated
underlying edge must be a bridge. Hostile probes therefore reject doubling an edge whenever an
alternative cycle path exists. Boundary-neutral `TwoDimensionalEmbeddedPlanarGraphData` now factors
the exact paths, conservative injective-arc geometry, endpoint-only intersections, complement
components, x-axis cells, and areas; the simple-boundary record forgets to it without changing any
such field. Uninhabited `TwoDimensionalBoundaryConnectedPlanarGraphData` then imposes literal
connectedness of every bounded face frontier and exact continuous closed segmentwise ordered
traversals realizing the bridge-aware words. This remains a conservative embedded-arc strengthening:
Driver-permitted one-edge loop incidence requires subdivision. No instance is constructed. Uninhabited
`TwoDimensionalBoundaryConnectedFaceProductLawData` now universally covers every measurable,
integrable finite vertex-gauge-invariant complex function, ties it pointwise to an existing ambient
physical observable through the unchanged selected paths, and requires Driver's exact product-Haar
formula using the unchanged density at exact areas and bridge-aware words. The unit case derives
normalization and nonzeroness. Separate uninhabited
`GeneralBoundaryChoice` is the full carrier of every valid simultaneous disconnected-frontier
presentation, rather than a supplier-selected subtype: each exact finite ordered family has
continuously traversed bridge-aware words, nonempty pairwise-disjoint traces, and maximal connected-
frontier semantics rejecting duplicates and artificial splitting. `TwoDimensionalGeneralBoundaryChoiceData`
records Definition 6.3's optional origin, ties it exactly to coordinate zero when present, and proves
zero absent from all vertices otherwise. `TwoDimensionalGeneralBoundaryExpectationLawData` requires
the resulting conditional restricted gauge invariance, exact choice-indexed density products, and one common
ambient expectation for every choice; integral-level choice independence and per-choice
normalization/nonzeroness are derived. No pointwise choice equality is asserted.
`FiniteGraphEdgeSetIsTree` now transcribes Definition 5.1 exactly on the one-coordinate-per-
underlying-edge representation: no nonempty closed composable word supported in the set may use
distinct underlying edges, while connectedness and spanning are not silently added. The mixed finite
product uses identity Dirac mass on tree coordinates and unchanged normalized Haar otherwise, with
exact factors, marginals, probability normalization, and empty-tree recovery. Uninhabited
`TwoDimensionalGeneralBoundaryTreeFreezingLawData` universally retains the same boundary choice,
density, eligible observable, and ambient expectation for every such tree; frozen/unfrozen and
cross-tree/choice integral equality plus frozen-carrier normalization/nonzeroness are derived.
Reusable `FiniteGraphRefinementData` now represents every coarse edge by an exact nonempty
composable fine word with coherent endpoints. Reverse traversal, fine-word substitution, induced
configuration maps, measurability, endpoint-gauge transport, and strict three-stage composition are
derived; identity refinements and their composition inhabit the reusable API. Uninhabited
`TwoDimensionalEmbeddedGraphRefinementData` ties vertices and edge holonomies to two embedded graphs
over the same ambient continuum chain and requires Lévy Theorem 1.6.1 surjectivity at the exact
gauge group. `TwoDimensionalGeneralBoundaryRefinementLawData` joins two existing general-boundary
laws indexed by the unchanged selected-density semigroup, selects valid presentations, constructs
an eligible fine pullback of every coarse observable, identifies its ambient physical observable
with the coarse law's exact one, and requires exact pushforward of the fine weighted measure to the
coarse one. Source-facing refinements require nonempty edge carriers and literal equality of every
coarse ambient path with its recursively concatenated fine word; ambient connection-holonomy
compatibility is derived rather than supplied. Integral equality for every eligible coarse
observable, Corollary 1.6.4 equality in law for every finite coarse-word family and substituted fine
family, exact embedded-map composition, and direct pushforward from coherent pairwise laws are
derived. No graph, refinement, or law instance is constructed.

Lévy §1.1 is now visually adjudicated at PDF p. 15 / printed p. 1. The reusable
`CompactOrientedMeasuredSurfaceData` retains a genuine two-dimensional compact Hausdorff second-
countable smooth manifold-with-corners carrier, exact connectedness, a smooth nowhere-vanishing real
top form selecting orientation, and a finite positive Borel area measure. Every exact extended chart
has one globally measurable density that is smooth and strictly positive on the exact target, and
the restricted surface measure pushes forward to additive Haar/Lebesgue measure weighted by that
same density; a.e. chart measurability prevents vacuous zero `Measure.map`. Real total-area
positivity, measure nonzeroness, and compactness of Mathlib's exact closed boundary set are derived.
Boundary components are the actual connected-component quotient of that set.
`CompactSurfaceBoundaryCirclePresentationData` now requires this exact component carrier finite and
presents each component as the exact range of one smooth embedded copy of Mathlib's genuine unit-
circle manifold. Every actual boundary point is covered by its own component circle; the union is
literally the manifold boundary, distinct component ranges are disjoint, and every parameterization
is injective. Closed surfaces remain admissible and derive an empty component carrier.
`IsPreferredChartOutwardBoundaryVector` now requires a two-sided ray certificate in the exact
model-with-corners range: negative time enters its interior and positive time exits the range.
`CompactSurfaceBoundaryOrientationData` adds smooth nonzero componentwise circle tangents, smooth
ambient fields along the exact parameterizations, genuine outward certificates, and positivity of
the selected surface top form on `(outward, pushed tangent)`. Preferred-chart outwardness is now
proved invariant under every strictly positive vector rescaling, making its dependence on the
positive tangent ray explicit. Its exit clause directly derives nonvanishing and rejects zero;
form positivity separately derives nonvanishing of the pushed boundary tangent. Reusable
`IsEuclideanHalfSpaceOutwardRayAt` mathematics now proves that at a half-space boundary coordinate
the exact two-sided ray condition is equivalent to strict negativity of the zeroth direction
coordinate. For every actual manifold boundary point, zeroth preferred-chart coordinate vanishing
is derived from Mathlib's exact frontier definition; consequently every stored outward field on an
exact presented boundary circle has the strict negative charted-tangent coordinate without an
extra hypothesis. Reusable linear-transport infrastructure now proves that any continuous linear
map preserving the boundary tangent hyperplane has output normal coordinate equal to the input
normal coordinate times the image-normal multiplier. A positive multiplier preserves strict
outwardness, and a continuous linear equivalence satisfying the corresponding forward/inverse
conditions preserves and reflects the full two-sided ray predicate. A new nonlinear tangent-cone
layer proves that the target normal coordinate of any locally half-space-valued differentiable map
has a genuine local minimum at a boundary image. Mathlib's tangent-cone Fermat theorem then forces
every bidirectional source tangent direction into the target boundary hyperplane and makes every
one-sided inward normal derivative nonnegative. Combined with the linear endpoint, chart
independence is reduced to exact source tangent-cone membership, derivative invertibility, and the
strictness argument using the inverse transition. The source-cone membership is now derived for
arbitrary relative neighborhoods of the Euclidean half-space: every zero-normal boundary tangent
appears in both cone directions and the distinguished inward normal appears one-sidedly. Thus a
locally half-space-valued within derivative on such a source automatically preserves the boundary
tangent hyperplane and has nonnegative inward-normal multiplier. Surjectivity now upgrades that
multiplier to strict positivity: a zero multiplier plus tangent preservation would force every
output normal coordinate to vanish, contradicting an inward-normal preimage. Thus strict outward
transport follows without separately constructing an inverse linear equivalence. These results are
now instantiated on Mathlib's actual `extendCoordChange`: its exact source is a relative half-space
neighborhood; smoothness supplies the derivative within that exact source; its target lies in the
same half-space; and Mathlib's inverse-derivative theorem supplies surjectivity. Therefore the actual
transition derivative preserves the boundary tangent hyperplane, has strictly positive inward-normal
multiplier, and transports the complete two-sided outward-ray predicate between boundary chart
coordinates. An exact chain-rule theorem now identifies the second chart's direct
`fromTangentSpace (mfderiv ...)` coordinate with that transition-within derivative applied to the
first chart's direct coordinate. It uses the literal overlap preimage neighborhood, local equality
of `extendCoordChange ∘ e.extend` with `e'.extend`, and Mathlib's within-composition theorem; no
ambient derivative replaces the exact transition-source derivative. Pinned Mathlib still lacks a
general installed boundary-submanifold instance; exposing the final chart-independent
geometry-facing theorem and closure data remain separate. `CompactSurfaceOrientationReversingBoundaryIdentificationData`
now chooses an exact positive number of distinct boundary components on each of two oriented
surfaces, equips every pair with a genuine smooth circle diffeomorphism, and requires its derivative
to send the selected positive left tangent to a strictly negative multiple of the selected positive
right tangent. Exact points on both actual component ranges and nonempty pair indices are derived;
zero-pair, duplicate-component, and zero-speed surrogates are hostilely blocked.
`CompactSurfaceBoundaryGluingQuotient` is now the minimal `Relation.EqvGen` quotient of the exact
disjoint union by those paired points. It has the genuine quotient topology, continuous canonical
maps from both full surfaces. Primitive seam edges are proved functional and injective as a
matching; the full generated relation is exactly equality or one edge in either direction, deriving
both side maps injective. Closed saturation makes the projection closed, so continuity and
injectivity upgrade both side maps to genuine closed topological embeddings. Each seam graph is a compact closed circle image, their finite union is
the primitive relation, and adding the diagonal and reversed relation proves the full generated
equivalence relation closed. Intersecting that relation with a closed subset and projecting the
resulting compact set proves every exact saturation closed; the quotient projection consequently
derives a closed map without assuming a generally invalid product-quotient theorem. Compact classes
of distinct quotient points are then separated by a generalized tube argument and saturated through
the closed projection, deriving explicit disjoint open neighborhoods and a genuine `T2Space`.
Compact fibers are finitely covered inside prescribed quotient neighborhoods by the canonical source
basis; saturated cores of those finite unions give an explicit countable quotient basis and derive
`SecondCountableTopology`. Urysohn metrization and compactness then derive `PolishSpace`; the quotient
is equipped with its canonical Borel measurable structure, derives `StandardBorelSpace`, and has
measurable projection and side inclusions. The projection theorem uses the separately packaged
`Mathematics.sumOpensMeasurableSpace`, which proves that the standard measurable disjoint union has
measurable open sets whenever both summands do. Compactness is derived from the compact disjoint
union and connectedness
derived from the two connected ranges meeting at a positive seam, exact paired-boundary equality,
and a universal lift for sidewise
functions agreeing on every generator. Primitive same-left/right relations, extra generated chains, and side collapse are hostilely
absent. Hausdorffness, second countability, Polish/standard-Borel structure, compactness,
connectedness, and closed side embeddings are now derived; no descended
smooth manifold/orientation or sewn area measure is constructed.
`CompactSurfaceBoundaryGluingSmoothDescentData` now exposes the exact uninhabited obligation on the
same quotient topology: an exact two-dimensional compact oriented measured surface nucleus,
differential immersions of both sides (combined with the already derived closed topological
embeddings to derive genuine smooth embeddings), pullbacks equal to explicit strictly positive multiples of both
side orientation representatives, sum-pushforward area measure, and exact retention of only unselected boundary images. Side-boundary
nullity is no longer stored: arbitrary eligible charts send intrinsic boundary points into the
frontier of the convex model range; additive Haar gives that frontier zero measure; the chart-density
law gives each boundary/chart piece zero surface area; and compactness supplies a finite chart cover,
deriving both full side boundaries null before any gluing witness exists. The exact canonical glued
area measure is now constructed independently as the sum of the two measurable side pushforwards;
its total area is the sum of side areas and is proved finite, strictly positive, and nonzero. The
exact seam, represented by the selected left boundary circles, is compact and measurable. Exact
same-side injectivity and cross-side matching put both side preimages of the seam inside their null
manifold boundaries, deriving zero canonical seam area. The continuous injective side maps are now proved to be measurable embeddings. The same exact
preimage analysis consequently proves the stronger restriction theorem for every measurable side
subset: its embedded image has precisely its original measure, while the opposite-side preimage is
boundary-null. Whole-side total-area recovery is a direct specialization. The selected boundary unions are
constructed independently and proved compact. Their exact unselected-boundary quotient image is a
named Borel candidate, proved canonically null from measurable restriction and side-boundary
nullity. The circle-range seam is proved exactly equal to both the selected-left and selected-right quotient
images, with the right equality retaining the designated circle diffeomorphism. It is disjoint from
the remaining-boundary candidate, and their union is exactly the union of both full original
boundary images before descent. Lévy sewing now derives that every designated sewn seam-loop trace
point and its dependent base label lie in this exact seam, while hostile retained-boundary incidence
is rejected without assuming smooth descent. Exact geometric basepoint injectivity also forces the
included left seam base label to equal the designated sewn seam base label, and the included left
loop trace is derived pointwise equal without an orientation-reversing reparameterization. Both
included side seam traces are proved to lie entirely in the exact seam; arbitrary right parameters
are handled using the inverse designated circle diffeomorphism. The right dependent base is shown to
represent a seam point without falsely equating its mixed-basepoint label to the left-oriented base.
Its represented point is identified exactly both as the selected right boundary point at parameter
`1` and as the sewn seam trace at the inverse-diffeomorphism image of `1`. Descent now identifies both its nucleus measure and manifold boundary with these named
constructions; its boundary nullity is rederived through that exact chain rather than merely inherited
from the generic compact-surface theorem. Same-side
injectivity plus the new exact characterization that cross-side quotient equality occurs only at a
designated pair derive interior placement of every seam point from that boundary equation, removing
it as an independent descent field. Hostile probes reject an unrelated glued measure and
pin all these distinctions.

Lévy Chapter 5, Theorem 5.1.1, equation (5.1), and the opening nonabelian sewing discussion are now
visually adjudicated against PDF pp. 89–94 / printed pp. 75–80. Reusable
`observationGeneratedMeasurableSpace` accepts dependent observation targets, constructs the exact
supremum of their comaps, and proves observation measurability, minimality, exact ambient recognition,
and surjective reindexing. A constant-observation hostile probe yields the trivial sigma field, not
the full field. This prepares finite simultaneous-holonomy fields without claiming the source-false
nonabelian equality of the two side fields with the sewn field.

`SimultaneousConjugacyQuotient` now quotients an indexed `G`-family by one common diagonal
conjugator, not by independently chosen coordinate conjugators. Equality and diagonal invariance are
exact. The quotient carries its genuine quotient topology and the final measurable space induced by
its projection; the projection is continuous and a topological quotient map. The setoid is now
literally Mathlib's orbit relation for the genuine left diagonal-conjugation action. Compactness of
the acting group makes that continuous action proper, deriving Hausdorffness of every finite-family
quotient; open orbit projection retains second countability. Under compact-Polish group and Borel
hypotheses, the final measurable quotient is proved exactly equal to the Borel space of the same
quotient topology. Urysohn metrization of the compact Hausdorff second-countable quotient and compact
metric completeness derive a compatible `PolishSpace`; the Borel equality then supplies the exact
`StandardBorelSpace` needed by Mathlib's regular conditional-kernel APIs. A hostile
parameterized theorem rejects coordinatewise-conjugate families whenever no common conjugator
exists; the empty-index quotient is explicitly subsingleton, so source-facing observation families
must retain nonemptiness where needed. Pointwise group inversion now descends to an involutive
bijection on the exact simultaneous quotient. Its continuity follows from the quotient-map universal
property, while its measurability is proved directly for the final quotient sigma field. This is the
literal inverse conjugacy class required on the second side of Lévy equation (5.1), not a freely
chosen involution. Lévy §2.10 is now visually adjudicated at PDF pp. 62–63 /
printed pp. 48–49: one common diagonal conjugator applies only to loops at one fixed base point,
while mixed-basepoint families are partitioned by a dependent base-point index. The new
`PartitionedFixedBaseFiniteFamily` selects one exact base and one positive finite family in that
fiber; different bases admit independent conjugators, and no observation applies one conjugator
across them. `NonemptyFiniteFamily` now
enforces literal positive arity `n+1`; existence is equivalent to nonemptiness of the caller-supplied
fixed-base loop carrier. Every resulting finite joint holonomy class is measurable on the exact generated sigma field, measurable one-loop holonomies put
that field below any ambient sample field, and exact ambient equality requires the converse coverage
inclusion. Sample-dependent common conjugation at that fixed base leaves every full family observation
unchanged; no theorem applies one conjugator across mixed-basepoint groups.
Generic regular conditional kernels now exist on these finite quotients under the displayed compact-
Polish hypotheses, but the source-facing all-boundary-value fiber/product version remains stronger
than an almost-everywhere selected generic kernel and therefore remains explicit acceptance data.

`BoundaryConditionedProductDisintegrationData` now packages reusable genuine conditional semantics:
Mathlib's `Measure.IsCondKernel` disintegrates the exact joint boundary/whole pushforward; the Markov
kernel gives zero mass to the complement of each exact boundary fiber (without assuming measurable
singletons); boundary reversal is measurable and involutive;
and every boundary value has an exact restriction pushforward equal to the left law times the right
law at the reversed value. Bind reconstruction, whole-law normalization/nonzeroness, and both
conditional marginals are derived. This deliberately distinguishes generic a.e. regular conditional
probability from the stronger all-value source-facing version. The Lévy-specific conditional-
independence sewing record is now present as uninhabited acceptance data.
`TwoDimensionalLevyCompactSurfaceSewingData` ties the exact geometric pair count to literal
`(G/Ad)^p` seam values and three separately partitioned fixed-base holonomy-generated fields. Raw
`G`-valued coordinates are not required measurable on quotient samples. Every dependent base index
maps injectively to an actual geometric point and every loop trace passes through that point,
preventing labels from either merging distinct basepoints or splitting one actual basepoint into
independently conjugated fibers. Exact trace maps identify side
seam loops with the selected geometric component parameterizations and the sewn seam with the same
loop in the topological gluing quotient; the right included trace is related through the exact
orientation-reversing diffeomorphism. Piece restriction holonomies and left/right seam conjugacy-class/inverse coherence feed `BoundaryConditionedProductDisintegrationData`. Its right factor uses the
componentwise descended inverse class, and the all-value product law and both marginals derive.
It does not assert that the side fields generate the whole sewn field.
`TwoDimensionalLevyFurtherConditioningData` now covers Theorem 5.1.1's final clause. Each side
supplies an arbitrary finite collection of distinct geometric basepoint blocks, with one positive
joint family per block; zero blocks omit further conditioning, and injectivity prevents splitting one
base across independent conjugators. The enlarged genuine disintegration conditions on the seam and
both full block tuples, reconstructs the exact same whole law through the exact same restriction,
and factors through side kernels whose index omits the other side's entire tuple. Its inverse-boundary all-value product law
derives. Euclidean-half-space outwardness is now proved independent of every eligible overlapping
atlas chart at an actual boundary point, and every such chart is proved equivalent to the preferred
extended-chart predicate. Uninhabited `TwoDimensionalLevySmoothSewingBridgeData` now forces this
smooth descent and the probabilistic sewing law to share the exact boundary identification and
quotient carrier. It derives smooth-interior placement of every designated probabilistic seam-loop
point, the canonical sum-of-pushforwards area, and the inverse-boundary conditioned product law; the
glued model's exact rank two proves witness-level non-equivalence to 4D Euclidean spacetime.
Inhabiting the smooth/oriented/measured descent contract and constructing
the actual smooth/oriented/measured descent witnesses remain open.

The first Driver Definition 8.1 lattice-approximation component is now exact:
`EpsilonSquareLatticePathCertificate` fixes `ε > 0`, a continuous literal `ℝ²` curve, and a finite
strictly parameter-ordered node list from `0` to `1`; each integer-coordinate step is exactly one
horizontal or vertical directed nearest neighbor, and each curve segment is the exact affine
realization in `εℤ²`. At least one bond is derived, while diagonal, stationary, zero-spacing, and
singleton-node substitutes are rejected. Uninhabited
On the project's conservative embedded-arc strengthening, with subdivision still required for
Driver-permitted one-edge loop incidence, `TwoDimensionalLatticeApproximatingSequenceData` supplies
one embedded fine graph at every
strictly positive spacing, surjective coarse-edge and bounded-face maps, an exact lattice-path
certificate on every fine edge, one nonnegative constant and positive cutoff giving a uniform
coordinate-Lebesgue symmetric-difference area `O(ε)` upper bound, and facewise transport of every valid coarse boundary presentation to its own valid fine
presentation with exact oriented-word and component order. Existing coarse boundary data ensures
this obligation is nonvacuous without forcing colliding face labels to share one presentation. No graph sequence witness is constructed. `twoDimensionalVillainAction` is definitionally the smooth strictly-positive real representative of
the unchanged selected convolution-semigroup density at Driver's exact `ε²` plaquette-area
parameter. It requires the existing Definition 4.7 invariant Laplacian, exact `∂ₜQ = 1/2 ΔQ` equation, an
initial-identity generated operator semigroup, and Driver's displayed convolution-kernel formula.
Continuity, strict positivity, class/inversion symmetry, real Haar-integral normalization, the exact
`ENNReal` bridge, and a normalized nonzero canonical Haar-density single-plaquette measure are
derived. `twoDimensionalWilsonAction` now uses the matrix-trace character of an actual continuous nonzero
finite-dimensional unitary representation. Its positive source-indexed normalizer is exactly tied to
the unnormalized character-weight Haar integral, so continuity, strict positivity, class/inversion
symmetry, integrability, and real Haar normalization are derived rather than disconnected. No
representation or Wilson action datum is constructed. `TwoDimensionalLatticeActionData` now packages
Driver Definition 7.1 once and has exact Villain/Wilson adapters plus an elementary constant-one
inhabitant, without conflating the source-qualified families. `EpsilonSquareLatticeDirectedBond` now gives the exact infinite directed nearest-neighbor bond
carrier at each positive spacing; `EpsilonSquareLatticeConfiguration` enforces reverse-bond
inversion, while `EpsilonSquareLatticeAxialConfiguration` fixes every vertical bond and every
horizontal x-axis bond to the identity. Both induced measurable carriers have measurable coordinate
projections and identity inhabitants. The integer sites now have an exact physical embedding at coordinates `(εm, εn)`, every bond derives a signed physical `ε` step, and a concrete multiplicative-integer axial configuration gives a nonidentity horizontal row-one coordinate and proves the axial carrier is not subsingleton. `EpsilonSquareLatticePlaquette` now supplies the exact physically scaled elementary square, a
literally closed counterclockwise four-bond boundary, and the fixed later-on-the-left holonomy.
`epsilonSquareLatticeFinitePlaquetteActionWeight` is the measurable, everywhere-nonzero finite
product of one unchanged Definition 7.1 action over those holonomies. The nonconstant axial witness
has nonidentity plaquette holonomy. `TwoDimensionalFiniteAxialPlaquettePresentationData` now selects finite orientation-disjoint off-tree
bond coordinates, recovers each through an injective measurable finite-support axial extension, and
selects actual elementary plaquettes while requiring every non-tree boundary bond to be represented
in one of the two coordinate orientations, blocking disconnected constant-action factors. The finite action weight and its exact product-Haar partition
function are definitions; `TwoDimensionalFiniteAxialNormalizerData` certifies that exact value is
nonzero and finite, from which the normalized nonzero finite axial measure is derived. A concrete
unit-group one-coordinate/one-plaquette presentation and normalizer inhabit the API without
constructing a nontrivial field. `twoDimensionalFiniteAxialPushforwardMeasure` maps that same
normalized law through the stored measurable extension to the exact infinite axial carrier; total
mass one, nonzeroness, and every represented-bond coordinate marginal are derived. `TwoDimensionalFiniteAxialProjectiveSequenceData` now requires nested coordinate and plaquette
inclusions, exact consecutive finite-law pushforward, and exhaustion of every off-tree bond and every
elementary plaquette. `TwoDimensionalAxialInfiniteVolumeCylinderLawData` requires a measure on the
exact infinite axial carrier whose restriction to every finite represented coordinate family is the
corresponding normalized finite law; normalization from any one exact cylinder, nonzeroness, and
represented one-coordinate marginals derive. `squareLatticeBoxProjectiveRadius` is definitionally
`stage+1`; exact nearest-neighbor orientation analysis and `Int.natAbs` bounds prove every off-tree
bond and every plaquette eventually occurs. Together with derived consecutive box projectivity this
constructs `twoDimensionalSquareLatticeBoxProjectiveSequenceData` for every normalized action.
`infiniteAxialRecover` now constructs an exact global axial configuration from arbitrary values on
all elementary plaquettes: upper/lower horizontal rows use finite rooted noncommutative products,
reverse bonds invert, and the axial tree is one. The map is measurable, its holonomy recovers every
input plaquette, and every exact box coordinate restriction equals the existing finite recursive
recovery. No measure is introduced in this recovery layer.

The infinite cylinder-law interface is now inhabited for the exhaustive exact-box sequence. The
construction takes the countable iid product of the unchanged normalized one-plaquette action law,
pushes it through `infiniteAxialRecover`, proves every finite plaquette marginal by the exact
`Measure.pi` projection theorem, and transports those marginals through finite recovery to identify
every box coordinate cylinder with `twoDimensionalSquareLatticeBoxMeasure`. Thus
`twoDimensionalSquareLatticeInfiniteAxialCylinderLawData` is a concrete infinite-volume lattice law.
It is not Driver Theorem 7.2: it supplies no boundary-conditioned weak convergence, no continuum
limit, no Wilson/Villain convergence theorem, and no 4D theory or mass gap. `epsilonSquareLatticeBoxPlaquettes` now gives exact
positive-radius centered boxes with lower-left coordinates `-n,…,n-1`, while
`epsilonSquareLatticeBoxAxialCoordinates` gives right-directed horizontal coordinates on the
nonzero rows `-n,…,-1,1,…,n`. Both sets are literally nested with radius; all coordinates are
off-tree and every selected plaquette's non-tree boundary is covered forward or in reverse.
`boxOffAxisRowEquiv` and `boxPlaquetteRowEquiv` explicitly enumerate the actual row subtypes by two
`Fin radius` chains, with positive coordinate row `i+1` aligned above upper plaquette row `i` and
negative coordinate/lower-plaquette row `-(i+1)`. These are geometric equivalences with exact signed
formulas, not arbitrary finite-cardinality relabelings. Exact site bijections then identify every
actual right-directed coordinate and every actual plaquette with a unique horizontal/row pair;
`boxCoordinateChainEquiv` and `boxPlaquetteChainEquiv` compose these into one common
`horizontal × (upper ⊕ lower)` index while retaining literal bond sources and plaquette lower-left
sites. `boxPlaquetteDifferenceForward` applies the rooted upper/lower transforms independently in
each exact horizontal column and `boxPlaquetteDifferenceRecover` applies their recursive inverses;
both inverse laws are proved on the actual coordinate/plaquette subtypes and packaged as a
measurable equivalence. Axis horizontal values are exactly one and represented rows recover the
same raw coordinates, so every transformed plaquette value is proved pointwise equal to the actual
plaquette holonomy of the same box extension. Upper/lower chain splitting, rooted Haar preservation,
finite products across horizontal columns, and literal reindexing then prove that the actual
coordinate-to-plaquette holonomy transform sends normalized coordinate product Haar exactly to
normalized plaquette product Haar; its recursive inverse preserves the reverse pair. Reusable
`Mathematics.MeasurableEquiv.map_withDensity_comp` transports composed densities through exact
measurable equivalences. The normalized Definition 7.1 action now defines a genuine one-plaquette
probability measure; finite product-density induction factors every plaquette-indexed density law.
The original box weight is exactly that product density after the same holonomy transform, deriving
`twoDimensionalSquareLatticeBoxNormalizer_eq_one` and identifying the normalized box-law
pushforward with the independent finite product of the unchanged one-plaquette action law. Hostile
probes reject changed source densities, unrelated transported measures, changed normalizers,
unrelated plaquette product laws, and disconnected replacements for the exact holonomy transform;
an explicit failed consecutive pushforward still blocks projectivity, so factorization is not used
as a proxy for the remaining commuting-square proof. `twoDimensionalSquareLatticeBoxPresentation` now uses the exact coordinate/plaquette subtypes,
constructs a measurable extension taking represented bonds to arbitrary coordinates, reverse bonds
to inverses, and all other bonds to the identity, and proves exact coordinate recovery, finite
support, orientation disjointness, and boundary coverage. Horizontal values on arbitrary rows are
named measurable evaluations of the same extension. Both vertical plaquette edges are proved
axial-tree bonds and the top traversal is exactly the reverse upper-row horizontal bond, deriving
the source-order-sensitive nonabelian formula `H(x,y)=U(x,y+1)⁻¹U(x,y)` for every box plaquette.
Separately packaged `Mathematics.RootedGroupDifference` now constructs the upper rooted transform
`D₀=U₀⁻¹`, `Dᵢ₊₁=Uᵢ₊₁⁻¹Uᵢ` and lower rooted transform
`D₀=U₀`, `Dᵢ₊₁=Uᵢ⁻¹Uᵢ₊₁`, proves explicit recursive recovery in both directions without
commutativity, and packages both as measurable equivalences. A final-coordinate splitting and
measurable skew-product induction proves that both transforms and recursive inverses preserve every
finite product of a common sigma-finite bi-invariant, inversion-invariant measure, covering the
normalized compact Haar use without assuming coordinate independence after the fact. These
triangular coordinates do not falsely identify every plaquette holonomy with one raw coordinate and
feed the now completed box-projectivity proof. A nonidentity multiplicative-integer
coordinate survives the extension. `twoDimensionalSquareLatticeBoxNormalizer` is the exact product-Haar integral of the exact box
weight. Strict positivity proves nonzeroness, while compactness uniformly bounds the common action
and proves finiteness. The resulting normalizer certificate constructs normalized nonzero finite-
coordinate box measures and normalized nonzero same-extension pushforwards to the infinite axial
carrier. `epsilonSquareLatticeBoxCoordinateInclusion` and
`epsilonSquareLatticeBoxPlaquetteInclusion` retain identical bonds/plaquettes at successor radius;
the induced coordinate restriction is measurable. General `Mathematics.finiteProductRestriction`
proves exact marginals of finite products along injective coordinate selections. Successor and
smaller axial extensions agree on every exact boundary bond of each included plaquette, hence their
noncommutative holonomies agree and the coordinate/plaquette restriction square commutes. The
independent plaquette-action product has the exact smaller marginal; conjugating through the
holonomy equivalences derives
`twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward` and constructs
`twoDimensionalSquareLatticeBoxProjectiveConsistencyData` for every normalized Definition 7.1
action. This is finite-box projectivity only, not Theorem 7.2 or an infinite-volume measure. The boundary geometry now separately defines Driver's `Aₙ`, `Aₙ₋₁`, finite variable bonds `Bₙ`,
outer bonds `B̄ₙ`, and frozen complement `Bₙᶜ`. Nearest-neighbor geometry proves `Bₙ ⊆ B̄ₙ`,
and explicit radius-one witnesses distinguish the two sets and exhibit a genuinely frozen bond. The exact finite coordinates for Driver's axial conditioned law are the canonical right-directed
off-axis horizontal `Bₙ` bonds, with rows restricted to `Aₙ₋₁`. The measurable conditioned
extension recovers these coordinates, freezes the axial tree, inverts reverse bonds, and equals the
supplied axial boundary configuration on every bond of `Bₙᶜ`; a hostile probe prevents nonidentity
boundary data from being replaced by the free identity extension. `epsilonSquareLatticeFiniteVolumeInteractingPlaquette` defines `J(Bₙ)` by literal boundary
incidence, and `.iff_box` proves this is exactly the complete `2n × 2n` box plaquette set; hostile
probes reject disconnected or omitted interacting plaquettes. `twoDimensionalSquareLatticeConditionedAxialWeight` is the exact (7.2) product of one unchanged
action over `J(Bₙ)` after the boundary-retaining extension. Strict positivity and compactness prove
its boundary-dependent partition function nonzero and finite. The resulting finite-coordinate law
and pushforward to the infinite axial carrier are normalized and nonzero, and every `Bₙᶜ` bond
equals the supplied boundary value almost surely. `WeaklyConvergesFiniteMeasures` requires every sequence member and limit to be finite and tests every explicitly measurable bounded continuous real observable. The exact
configuration carriers now have their induced product topologies with continuous bond evaluation.
Closed-embedding arguments now derive compactness of both the reverse-compatible infinite product carrier and its exact axial-fixed subcarrier. The exact directed-bond carrier is now proved countable, and under the source-faithful second-countability hypothesis both induced measurable spaces are proved Borel. Compactness and Borel measurability therefore derive every continuous real observable's bounded structured representative; `TwoDimensionalDriverAxialWeakLimitData` retains no independent test-coverage field. Exact conditioned-law normalization also derives every sequence measure's finiteness, while constant-one convergence derives common-limit normalization and finiteness. Universal bounded-continuous convergence is now the only weak-limit analytic field, then requires all axial boundary-conditioned
sequences to converge weakly to the same normalized measure and requires exact agreement with each
free box law on every bounded continuous observable depending only on `Bₙ`, matching (7.6). `positiveLatticeSpacingAtZero` is the punctured right-neighborhood filter and
No arbitrary certified-family record is exposed: `twoDimensionalVillainActionFamily` is exactly the unchanged Villain `Q_{ε²}` chain, while `FaithfulWilsonActionFamilyData` bundles the same Wilson trace representation, normalizer, and actual injectivity used by every spacing-indexed action. `EpsilonSquareLatticePathBondWordData` strengthens every Definition 8.1 fine edge with a nonempty
ordered directed-bond word whose exact source/target lists are the consecutive certified path nodes.
The measurable word holonomy uses later-on-the-left multiplication, and
`TwoDimensionalLatticeApproximatingHolonomyData.coarseRestriction` evaluates exact mapped fine-edge
words. `SmoothUnitaryRepresentationDifferentialData` defines Driver's `p_*` as the exact `mfderiv` of the
same smooth unitary matrix representation at identity and requires its injectivity.
`TwoDimensionalRepresentationInducedPairingCoherenceData` identifies the existing invariant inner
product literally with `-Re tr(p_*X p_*Y)` using genuine contracted matrix multiplication, blocking the previously possible pointwise-function multiplication and any unrelated representation/pairing substitution. Differentiated unitarity derives conjugate-transpose skewness of `p_*X`; trace cyclicity derives zero imaginary part and pairing symmetry, and the real carrier recovers the displayed negative complex trace exactly. Its self-pairing is the sum of all squared matrix-entry norms, so exact differential injectivity derives strict positivity away from zero. `TwoDimensionalWilsonCommonHeatChainData` now has connected compact Lie-group scope without a compact-simple index and closes the dependent chain through the same globally faithful representation, Wilson normalization/actions, pairing, pairing Laplacian, unchanged selected continuum density, heat equation, and kernel. `TwoDimensionalDriverAxialEnlargementData` now requires BC certificates for both `B` and `VB`, exact embedded refinement of every coarse edge, the precise vertical/x-axis tree, and total coverage of every enlarged edge by a coarse subdivision or tree membership. Measurable restriction recovers ambient coarse holonomies and complex observable values exactly. `TwoDimensionalDriverAxialEnlargedHeatExpectationData` states the strip/reflection result (6.1): universally for bounded measurable coarse real functions, the exact base expectation equals the normalized tree-frozen enlarged integral after coarse restriction, using one canonical BC word per face and the unchanged area-density law. `TwoDimensionalDriverAxialLatticeEnlargementData` now supplies the exact collision-safe `B(ε) → VB(ε)` proof geometry: commuting refinement words and lattice holonomy restrictions, a BC enlarged approximation, the exact image of the vertical/x-axis tree, and coverage of every fine enlarged edge by a coarse-fine subdivision or that tree. `TwoDimensionalDriverAxialLatticeFaceGeometryData` adds exact nonempty finite polyomino faces with the entire fine trace removed (preserving internal bridge/slit exclusions), exact positive integer exponents `|R(ε)|/ε²`. Mapped-area first-order control/convergence and eventual bijective face reindexing are now derived from symmetric-difference control, positive disjoint faces, finiteness, and all-spacing surjectivity instead of being independent fields. `TwoDimensionalDriverAxialLatticeProductIdentityData` now states the first enlarged §8 proof equality for every bounded measurable coarse observable: the exact action-indexed Theorem 7.2 lattice expectation equals a normalized `VB(ε)` integral with the certified BC words, exactly `|R(ε)|/ε²` normalized-Haar convolution factors, and the `T(ε)`-frozen carrier. Action continuity and measurable group operations now derive measurability of every convolution power and the complete finite BC density product. Fine-carrier normalization/nonzeroness follow from the universal identity at constant one and the normalized Theorem 7.2 law. Explicit unfolding and hostile probes lock both the coarse restriction and boundary word. `twoDimensionalVillainConvolutionPower_eq_selectedDensity` now derives the Villain semigroup reduction without additional acceptance data: `n+1` factors of the exact `Q_{ε²}` action are `Q_{(n+1)ε²}`. Exact positive polyomino counts then identify each fine-face power with `Q_{|R(ε)|}`, and the full certified BC product is pointwise the unchanged selected-density product. `TwoDimensionalVillainCommonHeatChainCoreData` now captures Driver 8.5's exact representation distinction: only the identity derivative is injective and induces the pairing/Laplacian/heat/kernel; no global faithfulness or Wilson normalization is imposed. `TwoDimensionalDriverVillainConvergenceData` is the uninhabited connected compact Lie-group contract for Theorem 8.5. Its sole new analytic field is the varying-finite-graph selected-density integral limit; compactness now derives bounded measurable test coverage for every continuous coarse function instead of assuming it; the exact product identity and equation (6.1) derive the universal continuous-observable continuum expectation. Analytic inhabitation and Wilson convergence remain open. A visual recheck of Driver printed pp. 601–603 exposed an unresolved internal Wilson-source conflict: Definition 8.4 visibly has no spacing factor in `exp Re χ(g)`, but Theorem 8.8 equation (8.2) requires one-step character eigenvalues approaching `exp(-cτ ε²/2)`. The literal current Wilson constructor is therefore not convergence-ready; Borgs–Seiler Appendix A or an erratum must settle the intended `ε`-dependence before Theorem 8.8/8.10 is canonicalized. No weak
limit, boundary-independence proof, or continuum convergence witness is constructed.

Mathlib's concrete `Matrix.SpecialLinearGroup (Fin 2) ℂ` is now exposed as
`ComplexSpecialLinearTwo`. The literal complex signs embed injectively as determinant-one scalar
matrices `±I`; the negative image is nonidentity and the full sign image is central. Its exact image
subgroup is multiplicatively equivalent to every accepted abstract two-sheet kernel by composition
through the literal signs, and the accepted negative kernel element maps to the negative matrix sign.
The exact matrix-subspace topology is now installed as separately packaged infrastructure.
Multiplication and adjugate inversion are continuous, the matrix inclusion is a topological
embedding, and homogeneous `SL(2,ℂ)` is a Hausdorff topological group. The kernel bridge remains an
abstract subgroup equivalence only: no ambient lift-to-matrix-group identification, homogeneous
Lorentz projection, Lie-group/manifold structure, inhomogeneous semidirect product, or cover
inhabitant is constructed.

The real mostly-minus quadratic form now has an exact coordinate bilinear polarization layer.
Self-pairing, symmetry, exact time-coordinate extraction, the polarization identity, and
nonpositivity at zero time are derived in every supported dimension. Any real-linear quadratic
isometry consequently preserves this same bilinear form. Applied to the existing proof-carrying
proper-orthochronous Lorentz carrier, this derives bilinear preservation and proves that the inverse
image of the time basis has exactly the forward time coefficient. The exact inverse linear
equivalence therefore retains positive time orientation and determinant one, yielding a concrete
inverse inside the same carrier. Whole-future-sheet preservation, composition closure, the full
Lorentz/affine group law, and its topological-group proof remain open.

The compact nonabelian Fourier/Peter–Weyl track now begins with an independently reusable algebraic
bridge. Every square matrix-valued monoid homomorphism acts on standard coordinate vectors as
Mathlib's exact `Representation`; its abstract linear-trace character is proved literally equal to
the original matrix trace. Exact coordinate matrix coefficients, their continuity under a
continuous matrix family, trace continuity, diagonal trace decomposition, and conjugacy invariance
are derived. Driver's existing Wilson representation now exposes this same Mathlib representation,
and its character continuity and centrality are independently rederived rather than relying only on
stored fields. The next analytic slice defines representation-valued Fourier coefficients
coordinatewise with the exact inverse convention `∫f(g)ρ(g⁻¹)`. Continuity and compactness derive
actual integrability against every compact-finite measure, with a named probability-normalized Haar
specialization. Addition, complex scaling, and zero laws are derived, and taking matrix trace is
proved to recover the scalar coefficient against the inverse trace character. The exact complex
convolution `(f⋆g)(z)=∫f(x)g(x⁻¹z)dμ_H` is now defined with the unchanged Driver/Sengupta order.
Genuine compact-product integrability, Fubini, left-Haar substitution `z=x*y`, and
`ρ((xy)⁻¹)=ρ(y⁻¹)ρ(x⁻¹)` derive the forced noncommutative Fourier law
`(f⋆g)̂(ρ)=ĝ(ρ)f̂(ρ)`. A hostile opposite-order probe shows that reversing this result would require
the two Fourier matrices to commute. Hall Proposition 5.17's Haar-averaging core is now constructed
for every continuous finite complex matrix representation. The exact coordinate Hermitian pairing
has a genuinely integrable normalized-Haar average and is invariant under simultaneous action by
the same representation. Its real averaged norm square is representation-invariant and strictly
positive away from zero: the proof uses continuity, positivity at the identity, openness of the
nonzero support, and the Haar measure's positive-open-set property rather than storing positivity.
Conjugate symmetry, first-argument additivity and conjugate homogeneity, the exact real self-norm
identity, nonnegativity, and definiteness now package this same average as a named
`InnerProductSpace.Core`. It is deliberately not installed globally. Its real part is now packaged
as a continuous real bilinear map in the original finite coordinate norm. Strict positivity and the
reusable positive-ellipsoid theorem give exact von Neumann boundedness over `ℂ`; the core diagonal is
continuous, and Mathlib's comparison theorem proves that the induced averaged norm topology is
exactly the original coordinate topology, including dimension zero. The compatible
normed-additive, complex-normed, and inner-product structures are now exposed as named, locally
installable values, with exact averaged-pairing evaluation and no global instance replacement.
Every group matrix is packaged as a complex-linear equivalence whose inverse is the unchanged
matrix action at `g⁻¹`; the action preserves the exact named averaged norm. A noncomputably selected
orthonormal basis of this exact realization is now reindexed by the original `Fin n` matrix size.
Its ordinary complex-linear coordinate equivalence sends each selected basis vector to the exact
Kronecker coordinate, has the exact inverse round trip, and transports the averaged pairing to the
standard coordinate Hermitian pairing. Conjugating the original action through this same exact map
now constructs a genuine continuous matrix representation with formula `σ(g)=Uρ(g)U⁻¹` and an
exact `Representation.Equiv` back to the original coordinates. Standard-pairing preservation is
derived from averaged-pairing invariance. A reusable column/Kronecker theorem then proves the
literal unitary equation `star σ(g) * σ(g) = 1`, including dimension zero. Character invariance is
recovered from the same representation equivalence. A reusable group-algebra module equivalence now
proves irreducibility invariant under every exact representation equivalence. Consequently every
explicit positive-dimensional continuous irreducible matrix representation, without any supplied
unitary law, constructs an equivalent bundled unitary representative and a coordinate-unitary-dual
class. Re-unitarizing an already unitary bundle is proved to retain its exact dual class. The same
Haar-averaged inner product now constructs an invariant orthogonal complement to every
subrepresentation. Finite-dimensional dimension arithmetic proves exact complementarity, hence
semisimplicity of every continuous compact matrix representation and a finite direct-sum
decomposition of its group-algebra module into simple submodules. Every selected simple summand now
has a scalar-restriction reconciliation, exact `Fin (finrank ℂ S)` basis, continuous matrix
coordinate representation, irreducibility proof from the unchanged simple module, and an explicitly
equivalent Haar-unitarized continuous irreducible unitary matrix representative. Arbitrary
non-coordinate representation realization, smooth comparison surjectivity, dual countability, dual
completeness, and Fourier convergence remain open. Finite matrix tensor products are now constructed
as exact Kronecker representations and flattened by the explicit standard row-major
`finProdFinEquiv`, `(i,k) ↦ k + m*i`, to `Fin (n*m)`. Every flattened entry
is proved to be the corresponding product of input coefficients; continuity and the literal
coordinate-unitary equation are preserved. Compact complete reducibility and the simple-summand
coordinate theorem therefore apply directly to each tensor representation. Exact finite summand
analysis and synthesis now reconstruct every vector, represented action, and matrix coefficient.
Consequently every product of two input coefficients is first an exact finite sum through the
selected simple group-algebra summand actions. Exact representation-equivalence coordinates now
expand each such action term as a finite double sum of matrix coefficients of a selected
positive-dimensional continuous irreducible unitary representative, with explicit output and input
weights. Thus coefficient products are proved to lie in finite weighted spans of selected unitary
coefficients. The contragredient `g ↦ (ρ(g⁻¹))ᵀ` is now an exact continuous representation; for
unitary input its coefficients are the pointwise scalar stars of the original coefficients. A
classically selected finite unitary decomposition of that contragredient therefore expands every
starred coefficient as a finite weighted sum of positive-dimensional continuous irreducible unitary
coefficients. Constants and the finite complex span of all such positive-dimensional continuous
irreducible-unitary coefficients are now bundled as an exact `StarSubalgebra ℂ C(G, ℂ)`. Its
multiplication closure is derived through the concrete tensor representation, and its pointwise-star
closure through the contragredient; the carrier is defined directly as the algebraic span rather than
by a closure or top construction (without asserting that this span is extensionally proper). Hall's
compact matrix-group point-separation step is now formalized with its source-visible hypothesis: a
continuous faithful finite complex matrix representation supplies a separating coordinate entry.
Under that explicit data, the coefficient star subalgebra separates points and Mathlib's complex
Stone–Weierstrass theorem proves its topological closure is `⊤`. The general compact-Hausdorff-group
Peter–Weyl point-separation/density theorem remains open because one faithful finite representation
is not assumed there. For the conditional compact matrix-group setting, exact basis-aware
representation-equivalence transport now sends every bundled irreducible-unitary coefficient into
a finite synthesis of the selected representative of its quotient-dual class. An explicit
one-dimensional trivial class supplies constants. Conversely, every selected-representative
synthesis lies in the earlier coefficient span, so the two submodules are exactly equal. Their
common density is now named `UnitaryMatrixDual.HasContinuousPeterWeylDensity`; faithful compact
matrix groups satisfy it, while the general compact-group target remains open. Regularity of normalized compact Haar measure and Mathlib's continuous-to-`L²`
density theorem then inhabit the existing normalized-Haar coordinate-dual `L²` Peter–Weyl completeness target.
The corresponding finite-support synthesis map is now explicitly dense: every `L²` vector has one
finite-support coefficient approximant within every positive tolerance, and inner products against
all such syntheses determine the vector uniquely. No approximating sequence, series enumeration, or
pointwise inversion is inferred. Continuous conjugation-invariant functions are separately bundled as
an exact `StarSubalgebra ℂ C(G, ℂ)`, and finite selected-character synthesis is an injective linear
map into it. On compact groups, `UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity` now names
uniform density in this exact central carrier and yields finite character approximants at every positive tolerance,
but has no inhabitant at arbitrary compact-group generality. Finite character syntheses and all continuous central functions now map
into normalized-Haar `L²`; `UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness` is exact equality
of their named closed spans. The closed continuous-central image span is a deliberate surrogate for
a literal AE-central `L²` carrier, not a proved identification with one. The target is reusable for
arbitrary compact topological groups, beyond Lévy's compact connected and section-specific
semisimple Lie-group scope, but has no inhabitant at that generality. Uniform central density implies
this `L²` target, while the target gives finite character approximants to every vector in the closed continuous-central subspace. It too
remains uninhabited at arbitrary compact-group generality. Hall's conjugation-average step is now isolated as
`CompactGroupCharacterCentralizationData`: a continuous linear map onto the exact central carrier,
identity on central functions, which sends every finite selected coefficient synthesis to a finite
selected-character synthesis. Full continuous density plus this datum implies both central targets;
faithful matrix coordinates supply the full-density premise. Hall's actual normalized-Haar
conjugation average is now a constructed continuous linear map under explicit second countability.
Parametric integration gives continuity; right-Haar invariance gives centrality; probability
normalization gives identity on central functions; the operator is norm-nonincreasing, surjective,
and idempotent. The exact remaining formula is now proved: coefficient synthesis equals
`tr(ρAᵀ)`, the Haar conjugation average leaves the existing Schur average of `Aᵀ`, and normalized
Schur trace supplies the exact `dim(ρ)⁻¹ tr(A)` character weight. Direct-sum induction constructs the
full bridge datum for every finite-support selected synthesis. Thus, under second countability, full
continuous density implies both central targets; faithful finite matrix coordinates now provide
conditional inhabitants. From any central-density inhabitant, a finite-support character family is
noncanonically selected at each tolerance `1/(n+1)` and proved to converge uniformly in `C(G, ℂ)`,
in the exact central subtype, and after mapping to normalized-Haar `L²`. Faithful second-countable
matrix groups therefore satisfy Hall's sequence-level approximation conclusion. The exact finite
character pairing now lives in the actual normalized-Haar `L²` carrier; each selected character
vector and analysis functional has norm one, analysis recovers finite synthesis coordinates, and
its value on a continuous central function is exactly `∫ conj(χ_q)f`. Applying these continuous
functionals to the chosen sequence proves every approximant coordinate converges to that integral,
with one faithful conditional theorem retaining the same sequence across uniform, `L²`, and all
coordinate limits. Independently of density, the entire selected character-vector family is now
orthonormal in normalized-Haar `L²`. Finite and unconditional Bessel inequalities prove square
summability and at most countable nonzero selected-character support for each individual `L²`
vector—without asserting that the whole dual is countable. The exact integrals `∫conj(χ_q)f` for
continuous central `f` inherit summability, Bessel, and countable-support results, while finite
character syntheses satisfy exact norm-square and unconditional-`tsum` Parseval identities. Every
finite selected-character set now determines an actual bounded orthogonal Fourier projection with
exact coordinate truncation, idempotence, finite-support inversion, residual-coordinate vanishing
and orthogonality, finite Parseval/Pythagorean remainder identities, norm contraction, and operator
norm exactly one when nonempty. The unconditional net indexed by all finite selected-class sets is
now proved to converge exactly on the closed finite-character span, where exact character `tsum`
Parseval holds. Convergence on the whole closed continuous-central surrogate is equivalent to the
explicit central `L²` completeness target. Under that target—and conditionally for faithful
second-countable compact matrix groups—the net converges to every continuous central function in
normalized-Haar `L²`, and the exact integrals `∫conj(χ_q)f` satisfy Parseval. This remains a
finite-subset net, not a selected countable ordering, pointwise/uniform inversion, or unrestricted
infinite synthesis identity. Independently, every selected character satisfies the sharp
`‖χ_q(g)‖ ≤ dim(q)` bound and exact global norm `‖χ_q‖∞ = dim(q)`. Any coefficient family with
explicit `Summable (‖a_q‖dim(q))` therefore has an unconditional finite-subset net converging in the
global uniform norm to a continuous central function, with exact pointwise/identity `tsum` formulas
and Weierstrass norm control. On this exact weighted domain, normalized-Haar `L²` analysis and the
source-facing integral recover every original coefficient:
`∫conj(χ_q)(∑a_rχ_r)=a_q`. Every such coefficient family has countable nonzero support without
global dual countability, and weighted uniform synthesis is injective. This is justified restricted
inversion, not inversion of arbitrary continuous or `L²` inputs. No Casimir spectrum or heat-kernel
coefficient family is derived to satisfy that weighted premise. Separately, an explicit uninhabited
`UnitaryMatrixDualHeatTraceSummabilityData` now stores nonnegative candidate Casimir weights and
requires `Summable (dim(q)^2 exp(-(t/2)c_q))` at every positive time. It conditionally constructs the
globally uniformly convergent continuous-central spectral character series, proves exact pointwise
and identity heat-trace formulas, uniform bound, coefficient time-addition law, and Haar coefficient
recovery, and derives selected-dual countability from strict positivity of every heat-trace summand.
Normalized-Haar convolution is now packaged on `C(G,ℂ)` under the explicit second-countability
required by Mathlib's parametric-integral theorem, with continuity, the sharp probability-Haar
bound `‖f⋆g‖∞≤‖f‖∞‖g‖∞`, and bounded linear maps after fixing either ordered input. Hostile probes
ensure this packaging does not introduce ambient commutativity. The exact normalized-Haar
selected-character convolution law is now proved directly:
`χ_q⋆χ_r = if q=r then dim(q)⁻¹χ_q else 0`, retaining the project's fixed
`(f⋆g)(z)=∫f(x)g(x⁻¹z)` order. Distinct classes vanish and central characters commute under this
otherwise nonabelian convention. Bounded linear convolution now extends that law through both
explicitly weighted unconditional uniform sums, giving
`series(a)⋆series(b)=series(a_qb_qdim(q)⁻¹)` without completeness or an unjustified sum/integral
exchange. Driver's pairing-normalized right-invariant Laplacian now also has a smooth complex-valued scalar
carrier using the identical manifold derivative, right-invariant fields, and same-pairing
orthonormal-basis independence contract; constants vanish, but that carrier alone infers no
character eigenvalue. A separate uninhabited `UnitaryMatrixDualCasimirLaplacianBridgeData` now
requires every selected character smooth and `Δχ_q=-c_qχ_q` for the unchanged pairing Laplacian.
It proves each weight unique from `χ_q(1)=dim(q)>0`, the exact `-(c_q/2)` coefficient derivative,
and the single-character `∂ₜ=½Δ` identity without passing either operator through an infinite sum.
Heat-trace summability at `t/2` now also controls the exact coefficient-derivative series at `t`:
the proved estimate `(c/2)e^{-tc/2}≤(2/t)e^{-tc/4}` yields weighted summability, unconditional
uniform finite-subset convergence, a pointwise derivative-candidate `tsum`, and a Weierstrass norm
bound. This candidate is not yet identified with the time derivative of the original infinite
series. The formal Laplacian coefficient series is now also uniformly convergent and exactly twice
the derivative candidate. Uninhabited `UnitaryMatrixDualCasimirHeatEquationInterchangeData`
isolates spatial smoothness/Laplacian passage and pointwise time differentiation; the pointwise
`∂ₜK_t=½ΔK_t` equation is derived only from those fields, not unconditionally. The selected class
of the explicit one-dimensional trivial representation now has character and dimension one; any
geometric bridge forces `c_triv=0` from `Δ1=0`. Exact Haar coefficient recovery consequently gives
the separate conditional normalization `∫K_t dμ_H=1`. Pointwise real-valuedness and strict
positivity are now isolated as uninhabited `UnitaryMatrixDualCasimirHeatPositivityData`; together
with the geometric bridge these fields produce a continuous positive real density, a measurable
positive `ENNReal` density of Haar lintegral one, and a normalized with-density probability measure.
No positivity inhabitant is constructed. Lévy's exact weak identity limit is now also isolated as
uninhabited `UnitaryMatrixDualCasimirHeatInitialIdentityData` with filter `𝓝[Set.Ioi 0] 0` and every
continuous complex test. Under positivity, exact with-density integration transports this limit to
the positive measures; no initial-limit inhabitant or time-zero density is constructed. Unitarity and
unconditional summation derive `χ_q(g⁻¹)=conj(χ_q(g))`, spectral inversion/conjugation, and literal
real/`ENNReal` inversion symmetry. Under positivity, the complex convolution theorem now yields
exact real and source-facing `ENNReal` `x⁻¹z` density semigroup laws. Uninhabited
`TwoDimensionalSelectedLoopSpectralDensityBridgeData` identifies the unchanged selected-loop
density with this spectral density and constructs its existing normalization, convolution, and weak
identity certificate from the geometric bridge, positivity, and initial identity rather than storing
those conclusions again. Smooth complex functions now have exact smooth real-part packaging, and
uninhabited `RightInvariantPairingRealComplexLaplacianCoherenceData` ties real and complex
Laplacians normalized by the same invariant pairing. Together with the spectral density bridge and
series interchange, uninhabited `TwoDimensionalSelectedLoopSpectralHeatEquationBridgeData`
constructs the existing positive smooth real selected-loop `∂ₜQ=½ΔQ` heat core on the unchanged
law, derived semigroup, and real pairing Laplacian. Uninhabited
`TwoDimensionalSelectedLoopSpectralHeatKernelBridgeData` explicitly retains Driver's stronger
arbitrary-continuous-test generated-operator/kernel theorem for that exact core. Uninhabited
`TwoDimensionalWilsonSpectralHeatChainBridgeData` then retains connectedness, faithful smooth
representation, Wilson normalization, and induced-pairing coherence and constructs the existing
common Wilson/heat chain on the spectral semigroup, with exact probes for the representation,
Wilson trace action, pairing, and spectral kernel. Uninhabited
`TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData` also forces a supplied continuous
independent-right-increment Brownian realization and Driver's generated operator to share that exact
spectral heat core; spectral `ENNReal` increment and marginal laws, the selected-area loop law, and
the unchanged `Δ/2` generator/kernel formulas are exposed with changed-law hostility. Exact
with-density Bochner integration and inversion symmetry further prove that the operator at every
deterministic base point equals the unconditional expectation of every
continuous test after right multiplication by any positive stationary increment, with
base-point-sensitive changed-expectation hostility. The existing finite consecutive-increment law
and almost-sure identity start further derive independence of every process value from its following
right increment. At positive times this yields the exact product of two spectral density measures
and, by the noncommutative map `(x,y) ↦ (x,x*y)`, the exact two-time process law, with changed-joint-
law hostility. The operator is also identified directly as deterministic right-translation
integration against the spectral probability measure. Product Fubini then derives the exact
continuous-test weak current-state identity
`E[φ(B_s)f(B_{s+t})]=E[φ(B_s)P_t f(B_s)]`, with changed-identity hostility. The new
reusable `finiteRightIncrementProduct_eq_endpoints` first proves the exact ordered noncommutative
telescope `(x₀⁻¹x₁)…(xₙ₋₁⁻¹xₙ)=x₀⁻¹xₙ`, including zero-step and changed-endpoint probes. Its
process specialization packages the increment-history product as a continuous map, identifies it
pointwise with `B(t₀)⁻¹B(tₙ)`, and uses the unchanged almost-sure identity start to reconstruct the
current state `B(tₙ)` whenever `t₀=0`. Its continuous complete prefix-product vector simultaneously
reconstructs `(B(t₁),…,B(tₙ))` almost surely. The
`TwoDimensionalSelectedLoopFinitePastIncrementIndependence` layer then groups the supplied mutually
independent coordinates: for every finite monotone time family, the complete vector of its first
`n` consecutive right increments is independent of the exact final increment. Exact index/formula
probes reject overlap with the final coordinate. The dependent spectral-transition layer identifies
that final increment with the unchanged spectral probability measure and uses product Fubini to prove
`E[Φ(H) f(S(H)Y)] = E[Φ(H) P_t f(S(H))]` for every continuous finite-history test `Φ`, continuous
history-extracted state `S`, and terminal test `f`; a changed transition value is hostilely rejected.
Almost-sure reconstruction specializes `S` to the ordered history product and rewrites both sides as
`E[Φ(H)f(B(tₙ₊₁))] = E[Φ(H)P_t f(B(tₙ))]` with actual current/future process values. Composing an
arbitrary continuous test with the continuous prefix-product vector then proves the same identity for
the actual finite process history `(B(t₁),…,B(tₙ))`. A separate direct product-law proof now permits
any measurable real history test with an explicit global norm bound; integrability follows from that
bound, the compact continuous terminal factor, and finite history/spectral measures. The resulting
bounded-measurable process-history identity has changed-value hostility. The exact past measurable
space at `s` is now the supremum of the pullbacks by every `B(t)`, `t≤s`; included evaluations are
measurable, these spaces increase with time and lie below the ambient sigma-algebra, and every proved
finite cylinder is past-measurable and satisfies the exact transition test. The uninhabited
`TwoDimensionalSelectedLoopFullPastMarkovData` requires that identity for every bounded real test
measurable for this generated past. Conditional-expectation uniqueness proves that any supplied
universal weak witness gives the exact conditional Markov identity for this generated past;
conditional pull-out proves the converse for every bounded past-measurable test, so these full-past
semantics are equivalent, with direct and changed-version hostile probes. The reusable
`ae_eq_condExp_of_piSystem_setIntegral_eq` now proves the actual complement/disjoint-union closure
from a generating pi-system, and `TwoDimensionalSelectedLoopFullPastPiSystemMarkovData` constructs
both universal semantics from generator, generation, total-integral, and basic set-integral fields.
The concrete sets measurable under some finite supremum of past evaluation pullbacks form a proved
pi-system and generate the exact uncountable-time past. Each cylinder is represented as the preimage
of a measurable set under an explicitly increasing finite evaluation vector. Adjoining `0`, `s`, and
`s+t` gives a proved monotone timeline, so the bounded-measurable finite-history theorem applied to
the cylinder indicator constructs every basic set-integral identity. Thus the unchanged spectral
Brownian bridge now constructs exact weak and conditional full-past Markov semantics; stochastic-
generator identification remains separate future proof debt.
`HasOperatorGeneratorAtZero` now states that debt exactly as the right-hand `NNReal` difference-
quotient limit of the heat operator on every smooth test, with target one half of the unchanged
pairing Laplacian. `TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData` remains uninhabited;
from any supplied boundary limit, the exact positive-increment expectation formula derives
`HasStochasticRightIncrementGeneratorAtZero` at every deterministic base time, and one base time
proves the converse, yielding exact equivalence.
Spectral weak convergence to the identity now derives right continuity of every scalar heat
trajectory by complexification, real-part transport, and the exact spectral-measure operator
formula. `TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData` retains only convergence
of the explicit positive-time pairing-Laplacian derivative. Mathlib's one-sided derivative extension
gives a derivative on `Ici 0`; its slope characterization and the `NNReal` coercion filter construct
the required quotient. A changed-limit probe uses uniqueness of limits. Separately, the reusable
`unitaryMatrixDualCasimirHeatComplexOperator` acts diagonally on every selected irreducible character
with eigenvalue `exp(-tc_q/2)`, proved through unconditional uniform character convolution. Its
scalar right-hand quotient converges to `-c_q/2`, with changed-limit hostility. Finite linearity
constructs coefficientwise heat evolution and the uniform-norm zero-time generator for every finite
selected-character combination. Exact support synthesis identifies this auxiliary presentation with
the canonical finitely supported quotient-dual coefficient carrier, yielding direct canonical heat
and generator theorems. `LinearMapGraphCoreGenerator` now proves the reusable abstract extension:
core convergence plus graph density and an eventual uniform graph-norm bound imply convergence on
the full algebraic domain, without assuming the generator is bounded. The strongest form permits a
possibly proper, unnormed algebraic domain with a separate, not-necessarily-injective linear map into
the ambient normed space; the earlier same-space statement is retained as a specialization. Exact and changed-target
probes protect both interfaces. The selected-character graph-density and heat-quotient graph-bound
instances are not constructed, so extension to every required smooth test and Laplace–Beltrami
comparison remain open. The
common Wilson chain now forgets only its genuinely stronger global-faithfulness and normalization
fields to construct Driver's exact Villain common heat chain. Uninhabited
`TwoDimensionalSpectralVillainWeakLimitBridgeData` ties the unchanged Theorem 7.2 contract to the
literal spectral `Q_{ε²}` lattice action at one positive spacing and derives normalization and
boundary-independent weak convergence, while explicit dimension probes reject the 4D endpoint. The
all-spacing `TwoDimensionalSpectralVillainWeakLimitFamilyBridgeData` supplies the exact family needed
by Theorem 8.5. Uninhabited `TwoDimensionalSpectralVillainProductIdentityBridgeData` then retains
only Driver's enlarged `VB(ε)` expectation identity and constructs the existing product certificate
with the exact spectral action/weak limits and derived normalized fine measures. Uninhabited
`TwoDimensionalSpectralVillainConvergenceBridgeData` adds only Driver's remaining
varying-finite-graph heat-integral convergence field on that unchanged chain; the existing theorem
then derives Theorem 8.5 convergence for every continuous coarse observable to its exact continuum
holonomy expectation, with changed-limit and four-dimensional hostility. Uninhabited
`TwoDimensionalSpectralPlanarLiteratureBridgeData` then dependently indexes a supplied Brownian
realization by this exact convergence chain's spectral semigroup and heat core. It constructs the
existing Brownian/generated-operator bridge and retains both the weak current-state Markov identity
and every-continuous lattice-to-planar-continuum convergence on one unchanged planar chain.
Combining the convolution formula with the exact candidate coefficient time-addition law now proves
the conditional positive-time spectral-family convolution law `K_s⋆K_t=K_{s+t}` in `C(G,ℂ)` and
pointwise in the fixed integral order. No inhabitant of either the heat-trace data or the geometric
bridge, interchange, positivity, or initial-identity data is constructed; no time-zero density,
unconditional infinite-series
heat equation, unconditional pointwise positivity of the summed function, unconditional Haar
normalization, or heat-kernel claim is made. The earlier approximation choices remain arbitrary
finite approximants, not Fourier partial sums; general compact-group density,
global dual countability, unrestricted infinite synthesis/inversion identities, and convergence of a canonically
ordered Fourier series remain open. This does not prove dual countability, infinite Fourier inversion, or the
general compact-group case. An equivalence with Mathlib's abstract `TensorProduct` carrier is also not inferred.
The next Schur precursor is now concrete: for two continuous finite matrix representations and an
arbitrary rectangular matrix `A`, the coordinatewise Reynolds average
`P(A)=∫σ(g⁻¹)Aρ(g)dμ_H` is genuinely integrable and satisfies the exact intertwining identity
`σ(h)P(A)=P(A)ρ(h)`. The proof transports finite matrix-coordinate sums through integrals and uses
the exact right-Haar substitution `g ↦ g*h`. This analytic average is now bundled as Mathlib's
exact `IntertwiningMap`. Mathlib's algebraic Schur machinery derives the irreducible
bijective-or-zero dichotomy, and an explicit inequivalence typeclass forces the entire averaged
rectangular matrix to zero. A hostile probe rejects any claimed nonzero average in that case. The
irreducible self-case is now also closed algebraically: because `ℂ` is algebraically closed,
Mathlib's endomorphism Schur theorem proves every self-average is a complex scalar multiple of the
identity. That scalar is named by choice, while hostile probes reject a nonscalar self-average and
initially avoid assigning an unproved value. The value is now derived in a separate layer:
cyclicity of matrix trace and probability-Haar mass one prove that conjugation averaging preserves
`tr(A)`, so the selected scalar obeys `n·c_A=tr(A)` and, when `n>0`, exactly
`c_A=tr(A)/n`. A hostile probe rejects changing this scalar normalization. The unitary
coordinate bridge is now also derived: one-sided `ρ(g)ᴴρ(g)=1`, together with the exact
homomorphic right inverse `ρ(g⁻¹)`, proves `ρ(g⁻¹)=ρ(g)ᴴ`. Thus inverse entries transpose and
conjugate, the full inverse character is the complex conjugate character, and Driver's stored
real-part inversion law is independently rederived. Applying the normalized Schur averages to exact
matrix units now proves all-index self orthogonality
`∫conj(ρ(g)ₐᵣ)ρ(g)ᵦ𝚌dμ_H=n⁻¹δₐᵦδᵣ𝚌` and exact zero mixed coefficients for explicitly
inequivalent irreducible unitary representations. A hostile probe rejects dropping the inverse
representation-dimension factor. Finite diagonal summation through genuinely integrable coefficient
families then proves every represented positive-dimensional irreducible unitary character has
normalized Haar `L²` norm one and explicitly inequivalent irreducible characters have zero mixed
pairing. A hostile probe rejects a nonzero inequivalent character pairing. Combining these results
with the exact inverse-entry Fourier convention now computes the representation-valued transform
of `ρ(g)ₐᵦ` at `ρ` as the forced transposed matrix unit `n⁻¹Eᵦₐ`, and as zero at an explicitly
inequivalent irreducible representation. A hostile probe shows that replacing `Eᵦₐ` by `Eₐᵦ`
for distinct indices is contradictory. The finite coefficient block is now explicitly packaged:
`A ↦ ∑ᵢⱼ Aᵢⱼρᵢⱼ` is a linear synthesis map into `G → ℂ`, its transform is exactly
`n⁻¹Aᵀ`, and Fourier extraction proves synthesis injective. Its range is therefore linearly
equivalent to the full matrix space and has exact dimension `n²`; hostile probes reject both
pointwise coefficient collapse and a wrong block dimension. On this exact block, the coordinate
Hilbert–Schmidt pairing now gives the algebraic Plancherel identities
`⟨f_A,f_B⟩=n⁻¹⟨A,B⟩ₕₛ=n⟨f̂_A(ρ),f̂_B(ρ)⟩ₕₛ`. A hostile diagonal-matrix-unit probe shows that
omitting the Fourier-side dimension weight forces `n=1`. Finite pairwise-inequivalent irreducible
character families are now packaged dependently across varying representation dimensions: their
synthesis is continuous and central, analysis recovers each exact coefficient, the Haar pairing is
the coordinate pairing, synthesis is injective, and the range dimension equals the family
cardinality. Hostile probes reject coefficient collapse and an equivalence between distinct indexed
members. Finite families of full matrix-coefficient blocks are now packaged with genuinely
dependent representation dimensions. An entire synthesized block transforms to zero at an
inequivalent family member; analysis at `ρᵢ` recovers exactly `dᵢ⁻¹Aᵢᵀ`, synthesis is injective,
and its range has exact dimension `∑ᵢdᵢ²`. Hostile probes reject block-family collapse, a wrong
range dimension, and equivalence of distinct indexed members. A generic synthesis-analysis lemma
now identifies `∫conj(f_A)f` with the Hilbert–Schmidt pairing of `A` against `f̂(ρ)ᵀ`. Consequently
the finite full-block family satisfies both exact algebraic Plancherel formulas
`⟨f_A,f_B⟩=∑ᵢdᵢ⁻¹⟨Aᵢ,Bᵢ⟩ₕₛ=∑ᵢdᵢ⟨f̂_A(ρᵢ),f̂_B(ρᵢ)⟩ₕₛ`; all finite sum/integral
exchanges are justified by compact-domain continuity. The coordinate unitary dual is now a genuine
quotient of all explicitly bundled positive-dimensional continuous irreducible unitary matrix
representations by exact representation equivalence. Every bundle is equivalent to its selected
class representative, distinct selected classes are inequivalent, equivalent bundles have equal
matrix dimension, and injective class labels supply the finite-family inequivalence certificates.
The dependent algebraic direct sum over every coordinate-dual class now gives a genuine
finite-support coefficient carrier. Its synthesis is continuous and injective, Fourier analysis
recovers `f̂_A(q)=d_q⁻¹A(q)ᵀ`, and `A(q)=d_q f̂_A(q)ᵀ` is proved as exact algebraic inversion on
that range. Hostile probes reject coefficient collapse, changed inversion, or expansion of this
result to an unspecified larger carrier. On the same direct sum, additive coefficient and Fourier
pairings now prove all-coordinate-class algebraic Plancherel:
`⟨f_A,f_B⟩=∑qd_q⁻¹⟨A(q),B(q)⟩ₕₛ=∑qd_q⟨f̂_A(q),f̂_B(q)⟩ₕₛ`. A scope probe exposes the
actual finite support and prevents this identity from being read as an infinite-series theorem.
A separate smooth coordinate dual now stores exact `ContMDiff` matrix coordinates and maps
injectively into the continuous dual. Its image is exactly the classes satisfying
`HasSmoothRepresentative`; comparison surjectivity is proved equivalent to every continuous class
having such a representative. A hostile probe shows one missing smooth representative blocks
surjectivity, so no silent dual equivalence is possible. Algebraic synthesis now also lands in
Mathlib's actual normalized-Haar `Lp ℂ 2`, where its inner product is proved equal to the exact
algebraic Fourier pairing. The algebraic `L²` range and closed coefficient span are concrete, and
`HasL2PeterWeylCompleteness` is exactly closed-span equality to top, equivalently density. Hostile
probes show a vector outside the span or nondensity blocks completeness. The faithful compact
matrix-group theorem above now supplies a conditional inhabitant by selected-representative
transport and normalized-Haar regularity; no general compact-group inhabitant is supplied.
The all-coordinate-class character specialization now uses finitely supported scalar coefficients:
synthesis is continuous and central, Haar analysis recovers every exact coefficient, synthesis is
injective, and the Haar pairing is the orthonormal coordinate pairing. Explicit support probes block
reading this as a central infinite-series or density theorem. Linear-trace conjugation now proves
that explicitly equivalent finite coordinate representations have identical trace characters even
across differently presented dimensions. The quotient-selected dual character is therefore proved
pointwise equal to the character of every bundled presentation of its class. Hostile probes reject
changed equivalent or selected-representative character values. For raw coordinate coefficients,
the exact rectangular matrices of each supplied equivalence and inverse are now constructed and
proved to satisfy both inverse laws. Exact intertwining becomes
`σ(g)=E ρ(g) E⁻¹`, and every target coefficient is derived as the full two-index source sum with
both change-of-basis factors. Hostile probes reject changed conjugation/coefficients and a zero
change matrix in positive dimension. Raw entries are not identified. The normalized-Haar mixed
pairing of coefficients from explicitly equivalent presentations is now derived by expanding those
exact sums, justifying every finite sum/integral exchange, and applying the existing self formula.
Its right side retains `dim(ρ)⁻¹`, the conjugated forward coordinate factor, and the conjugated
inverse coordinate factor; identity equivalence is proved to recover the original Kronecker-delta
self formula. Changed-factor probes reject a presentation-independent surrogate. Surjectivity/automatic
continuity-to-smoothness, remaining abstract coordinate
realization/unitarization, countability, the `L²` density proof, infinite-series Fourier inversion,
and heat-kernel spectral expansion remain open.

Current-strength `TwoDimensionalCurrentStrengthLiteratureAcceptanceData` now places the full same-`G`
Driver/Sengupta spectral planar Brownian/weak-limit/product/convergence chain and smooth Lévy
compact-surface sewing bridge in one acceptance record. It derives the major planar and sewing
consequences, retains exact rank-two geometry, rejects zero laws, and hostilely blocks linear
identification of the actual descended model with 4D Euclidean spacetime. It is not called final:
the planar-to-arbitrary-compact-surface heat-law construction and the uninhabited component theorems
remain open. The literature-only inhabitance attempt is now formalized as exact `Nonempty`
decompositions: the joined record requires both major bridges; the planar side requires the exact
Driver convergence chain and Brownian realization indexed by its heat core; the convergence chain
requires the exact enlarged-product bridge and separately named Driver varying-finite-graph
heat-integral convergence obligation; the product
bridge requires the all-spacing family plus the separately named source-facing expectation identity;
that family requires one spectral Wilson chain and a Theorem 7.2 weak limit at every spacing; every
such weak limit requires one candidate measure satisfying separately named boundary-independent
convergence and free finite-volume identification obligations; and the compact side requires both
smooth quotient descent and Lévy sewing on the same identification. None of those missing witnesses
is synthesized. Any eventual final inhabitant must remain strictly separate from the
four-dimensional Clay endpoint.

`TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData` now isolates Theorem 8.4/equation (8.3)
as a finite-dimensional pushforward law: normalized Haar fields on an etched finite graph in the
compact covering group, a finite nonempty curve family, a surjective topological covering projection,
a central kernel bundle class, the explicit inverse global partition function, one
bundle-class-twisted region, every remaining untwisted region factor, and distinguished-region
independence of the projected physical holonomy law rather than the raw edge-field measure. The
bounded and nonnegative measurable-test forms of equation (8.3), its every-distinguished-region
version, and normalization/nonzeroness of every corresponding graph measure are derived from that
equality in law.
Cover-group
compactness is required directly; the source's semisimple/boundary/nonorientable disjunction is not
represented by a content-free tag and remains for a future geometric theorem. The interface does not construct admissible surface curves, Definition 7.6's
area/topology-dependent `Z` factors, their identification with the planar spectral heat kernel, or
the stochastic Yang–Mills measure; those are the next compact-surface coherence debts.

Reusable `NormalizedCompactHaarDensitySemigroupData` now packages the exact positive-time
measurability, class/inversion symmetry, normalization, convolution law, and weak identity used by
the 2D heat chain; the selected-loop semigroup forgets exactly to it. Its measurable-surjective hom
interface transports every positive-time measure and continuous-test integral. The uninhabited
`TwoDimensionalSenguptaCoveringHeatSemigroupBridgeData` applies that interface to the same covering
projection stored by the finite compact-surface law, requiring a covering-group semigroup to push
forward to the unchanged planar density semigroup. An exact `Nonempty` equivalence splits this into
the missing cover-semigroup witness and its dependent measure-homomorphism witness. No cover density
is supplied.

`TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData` now supplies the boundary-conditioned
finite-face formula used in the proof of Theorem 8.4: Definition 7.6's delta constraints are discharged
by fixing external boundary fields, internal edge fields are integrated against normalized product
Haar, positive candidate-face areas sum to each positive region area, face words have three oriented
traversals, and the finite law's fixed central kernel bundle class left-multiplies exactly one
distinguished-face holonomy. The bridge requires the finite compact-surface law's ordinary and
twisted weights to equal these integrals using the same covering density. It does not construct an
embedded surface triangulation. The separate
`TwoDimensionalSenguptaClosedTriangularPresentationData` now closes the immediate finite-incidence
gap: a nonempty face carrier, nonloop endpoints, cyclically composable closed faces with three
distinct sides, orientation-independent two-face incidence for every internal edge, and use of every
external edge are required. No global orientation coherence is imposed, retaining Sengupta's
nonorientable case. This standalone layer is not yet required by the augmented acceptance record; it
remains uninhabited. `TwoDimensionalSenguptaEmbeddedTriangularPresentationData` now states the next
actual-realization obligation: a compact connected Hausdorff boundaryless two-manifold is covered by
embedded closed-disk faces meeting only in common simplices; marked circle sides follow exact
oriented word edges; a nonempty finite composable path family uses every external bond exactly once;
regions form the finite maximal connected partition of its complement; both Definition 7.2
face-chain conditions hold; and stored words are coherent whenever the complex is combinatorially
orientable. `TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData` now ties this exact embedded base to
the finite-law heat-factor and closed one-pair Facts 2–3 chain, requires every embedded curve word to
be literally the finite law's holonomy word, and requires the same finite law's fixed central bundle
class to satisfy `h = h⁻¹` whenever the exact complex is combinatorially
nonorientable. It remains uninhabited, outside the augmented record, and unidentified with the
separate Lévy surface carrier. `TwoDimensionalSenguptaEmbeddedComparisonBridgeData` now upgrades the
selected one-pair comparisons geometrically: embedded fine faces partition exact base face images,
every coarse bond has a nonempty directed fine-word realization without repeated underlying bonds,
coarse-face substitution equals the signed sum of fine-face boundaries after internal cancellation,
and parametrized external paths,
coarse vertices, and regions persist on the same surface. An explicit homeomorphism transports
parametrized edges through endpoint-fixing reparametrizations and transports face disks through
marked-boundary reparametrizations, alongside exact vertices, regions, and curve words. Its boundary
action realizes independent simplex orientations: positive is equivalent to an orientable source
plus orientation preservation, orientable negative reverses, and nonorientable negative permits
arbitrary local choices. It is uninhabited and not itself a universal invariance theorem.
`TwoDimensionalSenguptaUniversalCurveFixedEmbeddedSubdivisionData` now states universal acceptance
for the curve-fixed embedded Fact 2 subclass at fixed universe levels. It quantifies over a concrete
bundled candidate type rather than a supplied relation predicate, requires a factor certificate with
the same face map for every candidate, requires candidate nonemptiness, and carries the
nonorientable fixed-twist condition. Candidates keep external curve bonds and parametrized paths
fixed. `TwoDimensionalSenguptaCurveBondRefinementData` now supplies the exact missing combinatorics:
fine indexed curve words are literal finite-graph substitutions, covering and projected simultaneous
curve holonomies commute, and any supplied graph-measure pushforward transports the whole finite
curve law. Reverse-aware word substitution is now proved associative. Two graph refinements now
canonically construct their direct refinement by substituted edge words and composed vertex maps;
nonemptiness, composability, and endpoints are derived, and any other coherent direct graph is equal.
The direct curve refinement is then derived; its
configuration map is the composite, stagewise measure pushforwards imply the direct pushforward, and
the complete projected finite-curve law transports without a disconnected measure-law witness.
`TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData` lifts this to normalized
equation-(8.3) graph measures: a coarse-to-middle weighted refinement and supplied fine-to-middle
weighted pushforward on the same coherent triple derive the direct fine-to-coarse weighted
refinement and finest-graph stochastic finite law. The graph composite is canonical; the stage
weighted measures and analytic pushforwards remain supplied.
`TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData` now specializes that premise
to a literal normalized equation-(8.3) weighted Haar graph measure: its fine normalizer is the exact
fine graph-weight integral and the fine measure must push forward to the coarse graph measure for
every distinguished region. Fine normalization/nonzeroness and the unchanged projected stochastic
finite-curve law are derived. The weighted pushforward itself remains an explicit obligation;
heat-factor/convolution integration, unnormalized-weight equality, construction/inhabitation of the
fine embedded subdivision, full source-valid subdivisions, and full universal Fact 2 remain open.
`TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData` now closes the conditional one-pair
geometric/heat-factor interface around that graph law: a fine embedded triangular presentation on
the exact same surface partitions coarse face images, preserves vertices and regions, realizes every
coarse total bond by a composable fine word, identifies each external subword with the exact graph
refinement, and enforces signed internal-edge cancellation. Its fine ordinary and fixed-twist graph
weights are exactly the fine boundary-conditioned covering heat factors, so the unchanged projected
stochastic finite law is represented on the actual fine embedded curve words. The record remains
uninhabited and assumes the normalized weighted pushforward.
`TwoDimensionalSenguptaUniversalEmbeddedCurveBondSubdivisionData` now adds universal acceptance over
a concrete fixed-universe candidate class whose source geometry is bundled before analytic
certification. Each candidate contains its fine triangular/embedded presentation, literal split-bond
curve refinement, face partition, total-edge paths, signed cancellation, unchanged regions, and
exact preservation of the base orientability class but no weighted pushforward. Fine
nonorientability therefore derives the same fixed `h = h⁻¹` condition already attached to the base. Every candidate must receive a normalized equation-(8.3) graph-measure
certificate whose ordinary and fixed-twist weights are its own boundary-conditioned covering heat
factors; candidate nonemptiness blocks vacuous quantification, and each certificate reconstructs the
one-pair bridge. The record remains uninhabited; the heat-kernel integration proof, construction,
unrestricted universe scope, and full Fact 2 remain open.
`TwoDimensionalSenguptaUniversalCellwiseEmbeddedHomeomorphismData` now states universal acceptance
for the directly cellwise-compatible embedded Fact 3 subclass at fixed universe levels. Its concrete
bundled candidates contain targets and homeomorphisms with direct cell equivalences, exact mapped
total area, curve words, endpoint-preserving edge transport, independent per-face simplex
orientations, global sign, face disks, and complement regions. Every candidate must receive a
matching factor certificate; candidate nonemptiness and the nonorientable fixed twist are explicit.
Negative global sign does not force local face reversal on a nonorientable source. Homeomorphisms
requiring preliminary subdivisions, full universal Fact 3, and inhabitation remain open.
`TwoDimensionalSenguptaPreliminarySubdivisionHomeomorphismFactorData` now derives the exact algebraic
proof pattern after such subdivisions are supplied: source coarse-to-fine equality, signed cellwise
homeomorphism equality, and reverse target coarse-to-fine equality compose to the coarse ordinary
and transported-twist laws. The target subdivision uses exactly the resulting `h` or `h⁻¹`.
Preliminary-subdivision construction and the geometric/heat-factor proof of curve-bond weighted
refinement remain open.
`TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData` now dependently joins the exact
embedded finite-law base, selected geometric comparison, curve-fixed universal Fact 2 subclass, and
cellwise-compatible universal Fact 3 subclass on the same covering density and fixed bundle class.
Its exact `Nonempty` audit exposes all four dependent witnesses.
`TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData` now retains that exact
chain and dependently adds the fixed-universe universal embedded split-curve-bond Fact 2 record on
its unchanged embedded base and covering density. Its exact `Nonempty` audit separates the prior
chain from the additional split-bond certification, and hostile probes reject omission of either.
This is the strongest current compact finite-law record but remains explicitly nonfinal pending
unrestricted-universe/full Fact 2, general Fact 3, construction, and inhabitation.
`TwoDimensionalSenguptaClosedPresentationInvarianceBridgeData` now dependently ties
closed incidence for the exact finite-law heat-factor base and the exact fine/transported candidates
to one unchanged Facts 2–3 bridge, preventing unrelated presentation witnesses. This combined bridge
also remains outside the augmented record pending embedded and universal source semantics. Fact 0 distinguished-face invariance and Fact 1 positive same-total
area-splitting invariance for both ordinary and fixed-twist factors are now exact uninhabited fields;
A separate `TwoDimensionalSenguptaSubdivisionFactorInvarianceData` now gives one factor-level Fact 2
building block: one coarse/fine candidate pair is tied to one normalized nonzero covering-density
semigroup and central twist and has a surjective region-preserving face map, exact region-total area
equality without fixed simplex allocations or twist-face matching, and equality of all ordinary and
fixed-twist factors. Embedded boundary-word subdivision and universal quantification over all valid
subdivisions remain open. `TwoDimensionalSenguptaHomeomorphismFactorInvarianceData` similarly gives a
one-pair factor-level Fact 3 candidate on one normalized semigroup and central twist: explicit
external/internal edge, face, and region equivalences preserve regions and mapped region-total area
without fixing simplex allocations or twist faces;
external fields transport contravariantly; independent per-face simplex-orientation choices control
word reversal, while the global sign controls `h` versus `h⁻¹`; and ordinary/twisted factors agree. Actual area-preserving surface
homeomorphisms, curve reparameterizations, and universal source quantification remain open. The
new `TwoDimensionalSenguptaFactsTwoThreeBridgeData` prevents disconnected witnesses: both one-pair
certificates start at the exact triangulation stored by one finite-law heat-factor bridge and reuse
its unchanged covering density and fixed central bundle class.

`TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData` now states the first exact same-theory bridge
between the distinct Sengupta and Lévy compact-surface sample carriers. A finite nonempty curve family
is placed in one exact Lévy whole-surface base fiber, and only the simultaneous-conjugacy-class
pushforward laws are equated. The bridge does not identify carriers, compare raw holonomies across
quotient models, construct the curve embedding, or prove the law equality; it remains uninhabited.

`TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData` now dependently joins the exact
current-strength planar/Lévy record, one Sengupta finite law, its covering heat bridge, its
boundary-conditioned finite-face factors, and its finite simultaneous-conjugacy law coherence with
the exact Lévy sewing field already stored by that record. The covering heat target is definitionally
the same planar spectral semigroup selected by the Driver/Brownian chain. Its exact `Nonempty`
decomposition requires compact-simple gauge geometry, the prior current-strength witness, one finite
Sengupta law, and the two bridges dependently indexed by that current record and law; it synthesizes none of them. This join is
still not the final 2D proposition: embedded presentation, Facts 2–3, literature-only inhabitation,
and all underlying analytic/stochastic witnesses remain open. The augmented record now requires the
intended `CompactSimpleGaugeGroupData`; its simple tangent Lie algebra derives Mathlib semisimplicity,
so Sengupta Theorem 8.4's first source alternative is genuinely discharged.

`TwoDimensionalSenguptaEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData` is the prior
dependent join of that exact augmented planar/Driver/Lévy/Sengupta record with the curve-fixed and
cellwise-compatible finite-law chain. The stronger
`TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData` now joins
the unchanged augmented witness to the strongest fixed-universe compact finite-law record, including
universal embedded split-curve-bond Fact 2 certification. It is indexed by the former's exact finite
law, heat factors, planar spectral semigroup, covering density, and fixed bundle class. Its
`Nonempty` equivalence exposes both dependent witnesses without synthesis. The actual descended
compact-surface model retained by this strongest wrapper has exact real rank two and cannot be
real-linearly equivalent to four-dimensional Euclidean spacetime, so the strengthened finite-law
chain does not erase witness-level dimensional separation. This is the strongest current
cross-source 2D join, but unrestricted-universe/full Fact 2, general Fact 3, heat-kernel
integration, construction, and all component inhabitance remain open.

`TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance` now gives that exact strongest
assembled chain a proposition-shaped source index. It is definitionally equivalent to nonemptiness
of the unchanged wrapper. Besides the exact dependent augmented/compact split, its flattened
inhabitance audit separately exposes the compact-simple geometry, current Driver/Lévy chain,
Sengupta finite law, dependent heat factors, finite-law sewing bridge, and strongest compact
finite-law witness; conversion in both directions constructs no missing field. Any inhabitant retains exact rank two and rejects a
four-dimensional real-linear model; a hostile probe shows that replacing the proposition by `True`
loses this conclusion.
`TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance` now adds the exact
`TwoDimensionalSelectedLoopFinitePastCylinderMarkovData` field to those same six components, indexed
by their unchanged nested spectral Brownian bridge. Its `Nonempty` audit exposes the old components
plus the canonically derived finite-coordinate transition record; `.ofCurrent` and `.implies_current`
prove that this full-past strengthening adds no inhabitance hypothesis. The pi-system theorem
constructs full-past semantics rather than accepting a second monotone-class field. Rank-two and 4D linear-model
exclusion persist.
`TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance` is the next
strict proposition-shaped layer: it existentially pairs those prior exact components with
`TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData` on their unchanged nested spectral
Brownian bridge. Its exact decomposition, derived zero-time generator, forgetful implication, rank-two theorem, and
4D exclusion are probed; unlike the full-past field, the pairing-generator boundary-continuity
witness is not constructed. The name remains explicitly `CurrentStrength`: the final source-complete 2D
proposition and literature-only inhabitant are still open.

The preliminary `FourDimensionalCurrentStrengthUniversalAcceptance` declaration is intentionally
qualified and uninhabited. No final source-complete acceptance declaration, placeholder inhabitance
theorem, or arbitrary structure is introduced merely to make the project appear complete.
