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

Not yet achieved:

- No concrete inhabitant of the gauge-group certificate has been constructed. Mathlib's algebraic
  `SU(n)` API does not supply the complete manifold/compactness/connectedness/tangent-simplicity
  chain, so positive consistency infrastructure remains open.
- No general smooth bundle-map, smooth adjoint-vector-bundle/descent layer, concrete
  principal-connection/curvature/structure-certificate
  witness, automatic curvature horizontality/equivariance theorem, Bianchi/gauge-covariance result,
  symmetry-group, quantum-theory, acceptance, existence, or satisfying mass-gap declaration exists.
- No Yang–Mills acceptance declaration exists.
- No standalone Git remote exists or has been pushed. The tested candidate
  `git@github.com:elmismisimoxhunca/lean-yangmills-adaly.git` does not exist, and the available SSH
  credential was scoped to the retired repository. Local commits can proceed; remote publication
  remains an explicit infrastructure blocker.
- Clay, Hall, Aharony–Seiberg–Tachikawa, and Freed artifacts are pinned. Clay equation (1) now
  anchors the action formula, invariant quadratic form, and chosen orthonormal curvature
  contraction and relative-to-designated-measure action. Generic bilinear contraction is now proved
  basis-independent, the exact dependent adjoint-fiber pairing is packaged bilinearly, and the
  generic degree-two adapter is applied to the exact curvature. The resulting pointwise contraction
  is basis-independent and the existing action is proved to integrate it, but a general Hodge-star
  bridge and metric-volume compatibility remain pending. OS-I, correcting OS-II, Wightman 1956,
  and Streater–Wightman source artifacts are now acquired and verified. Scalar tempered Schwinger
  families and fixed-order factorial-growth infrastructure are implemented, but the OS source-norm
  bridge, `(E2)`, `(E4)`, and reconstruction remain unimplemented; scalar proper-Euclidean
  covariance `(E1)` and permutation symmetry `(E3)` are now explicit. Wilson and Osterwalder–Seiler
  lattice sources are likewise pinned; finite periodic bonds, plaquette holonomy, local gauge
  transformations, Wilson-type action, normalized product Haar, conditional Gibbs data,
  support-local loop expectations, finite-cutoff reflection-positivity checker, and scaling/
  expectation-limit interfaces are explicit. No Gibbs, positivity, scaling, or continuum-bridge
  inhabitant is constructed, and measure/field/OS continuum identification remains unimplemented.
  Wilson's OPE paper and the Gross–Wilczek/Politzer asymptotic-freedom papers are pinned. Generic
  weak OPE data and the basic exact `F²` interpretation bridge are implemented, but arbitrary
  curvature-polynomial/covariant-derivative interpretation, operator mixing, and prescribed
  ultraviolet coefficient semantics remain unimplemented. The physical joint translation-PVM
  and invariant-mass-gap predicates are now anchored to the visually verified SNAG discussion, and
  the same PVM supplies the Hamiltonian interval view; any satisfying spectral datum and the final
  acceptance integration remain absent.

The absence of an acceptance declaration is intentional: no placeholder theorem or arbitrary
structure is introduced merely to make the project appear advanced.
