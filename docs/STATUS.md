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

Not yet achieved:

- No concrete inhabitant of the gauge-group certificate has been constructed. Mathlib's algebraic
  `SU(n)` API does not supply the complete manifold/compactness/connectedness/tangent-simplicity
  chain, so positive consistency infrastructure remains open.
- No general smooth bundle-map, smooth adjoint-vector-bundle/descent layer, concrete
  principal-connection/curvature/structure-certificate
  witness, automatic curvature horizontality/equivariance theorem, Bianchi/gauge-covariance result,
  symmetry-group, quantum-theory, acceptance, existence, or mass-gap declaration exists.
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
