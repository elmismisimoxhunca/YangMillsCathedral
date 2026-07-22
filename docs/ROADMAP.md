# Construction roadmap

This roadmap is a goal sequence, not a claim of current completion. Every stone is reviewed and
committed before higher layers depend on it.

## Phase 0 — independent foundation

- [x] Initialize a standalone Lean/Mathlib project.
- [x] Pin and verify the Clay/Jaffe–Witten source artifact.
- [x] Record the no-solution mission, provenance law and dependency architecture.
- [ ] Establish a writable standalone remote.
- [x] Add declaration-level source and legacy-integration ledgers.
- [x] Publish a Crossref/DOI-verified audit bibliography covering existing declarations and every
  currently planned source gap, with a correction log and explicit acquisition/canonicalization
  boundary.

## Phase 1 — dimensions and signatures

- [x] Define Euclidean spacetime dimensions `1 ≤ d ≤ 4`.
- [x] Define spatial dimension as `d - 1` only in reconstruction contexts.
- [x] Define Euclidean and Minkowski quadratic forms without identifying them or asserting reconstruction.
- [x] Add hostile probes for out-of-range and dimension-confused witnesses.

## Phase 2 — gauge geometry

- [x] Pin authoritative Lie-algebra simplicity and gauge-global-form sources.
- [x] Pin authoritative principal-bundle, connection and curvature sources.
- [x] Define compact-simple Lie-group semantics and global-form policy.
- [x] Adopt and source-map Mathlib's ideal/non-abelian Lie-algebra simplicity interface.
- [x] Define and probe the reusable fiberwise torsor core (not a full principal bundle).
- [x] Define algebraic bundle maps and gauge automorphisms (smoothness still pending).
- [x] Define and probe topological equivariant local trivializations.
- [x] Define and probe smooth principal-bundle compatibility.
- [x] Package quotient-map and smooth overlap-transition theorems.
- [x] Define and probe smooth gauge transformations.
- [x] Define and probe the Lie-group adjoint action needed by connection equivariance.
- [x] Define and probe typed pointwise manifold differential forms and pullback.
- [x] Define and probe pointwise principal connection normalization/equivariance.
- [x] Add and probe local smooth-section regularity for differential forms.
- [x] Promote the pointwise form to a smooth principal connection definition.
- [x] Add continuous and smooth degree-one wedge/bracket infrastructure.
- [x] Construct the continuous graded bracket wedge of a one-form with every `n`-form using the
  exact omitted-slot alternating sum, prove degree-one coherence and zero laws, and expose the
  one-with-two three-term formula needed before Bianchi.
- [x] Prove smooth closure of the exact graded bracket wedge from the existing smooth coordinate
  bracket, bundle it without changing the carrier, and retain degree-one smooth coherence.
- [x] Derive additivity and real-scalarity of the graded bracket wedge in each argument, with exact
  probes, as algebraic prerequisites for future curvature expansions.
- [x] Expand the cubic self-bracket with the exact wedge normalization and derive its pointwise,
  manifold, and smoothly bundled vanishing from the cyclic Lie Jacobi identity.
- [x] Add arbitrary-manifold one-form exterior-derivative certification.
- [x] Add a parallel positive-degree Cartan certificate for every `(n+1) → (n+2)` step with
  Mathlib's exact triangular
  indices/signs, normed-space `extDerivWithin` compatibility, certificate agreement, a concrete zero
  certificate, and an exact `2 → 3` specialization; do not claim canonical existence or `d²`.
- [x] Prove the positive-degree formula at `n = 0` equals the earlier one-form Cartan formula and
  provide bidirectional certificate conversions preserving the exact degree-two derivative carrier.
- [x] Combine Mathlib's normed-space `d² = 0` theorem with the positive-degree Cartan bridge,
  including exact within-set, global, and `1 → 2 → 3` nilpotence surfaces; arbitrary-manifold
  `d²` remains debt.
- [x] Connect the actual finite-dimensional group Lie-algebra coordinate bracket to Mathlib's
  bounded-bilinear `HasFDerivAt`/`fderiv` calculus, including the exact self-bracket rule.
- [x] Construct the continuous one-with-`n` wedge for an arbitrary bounded bilinear map and prove
  the actual group bracket's coordinate wedge is exactly the intrinsic graded Lie-bracket wedge.
- [x] Package exact fixed-tuple evaluation as a continuous linear map and derive the same-input
  self-wedge coefficient `HasFDerivAt`/four-term `fderiv` rule.
- [x] Exterior-alternate those coefficient derivatives and prove the exact skew-bilinear
  `-2 • (A ∧_B dA)` identity, including the canonical group-coordinate bracket specialization.
- [x] Prove the degree-one wedge operator-norm bound, bundle it as a continuous bilinear map, derive
  whole-form differentiability, and identify the alternation with Mathlib `extDeriv`.
- [x] Derive the finite-dimensional normed-coordinate Bianchi identity from the exact same
  connection one-form, canonical transported bracket, Mathlib `d² = 0`, self-wedge Leibniz, and
  Jacobi cancellation.
- [x] Prove within-set self-wedge Leibniz and Bianchi variants retaining explicit regularity,
  uniqueness, membership, and closure/interior hypotheses, with exact `univ` recovery.
- [x] Separate raw unrestricted from explicit within-set normed-coordinate pullbacks; specialize
  inverse extended charts using corner-aware `mfderivWithin` on the exact model range, and prove
  evaluation, center recovery, target-local derivative invertibility, linearity, and canonical
  bracket-wedge coherence.
- [x] Derive target-wide and pointwise `C∞` regularity of the exact inverse-chart principal
  connection one-form from stored intrinsic smoothness when the total-space model is finite
  dimensional, using chart-pulled vector fields and finite-dimensional evaluation reconstruction.
- [x] Pull the exact principal connection, its indexed derivative certificate, and its derived
  curvature through the same within-set/chart coordinates, proving the exact coordinate curvature
  equation without identifying the certificate with coordinate `extDerivWithin`.
- [x] State the exact same-connection exterior-naturality obligation with separate tangent-transport
  and calculus sets, and derive conditional within-chart Bianchi for the exact curvature carrier.
  In finite-dimensional total-space models, remove the separately supplied coordinate-regularity and
  order hypotheses via the derived intrinsic-smoothness theorem.
- [x] Reduce inverse-chart exterior naturality to one explicit Cartan-transport equality: derive the
  certified derivative side from the existing manifold Cartan certificate, derive the coordinate
  side from Mathlib `extDerivWithin`, and prove that equality of those expressions is exactly
  equivalent to full naturality.
- [x] Prove the remaining Cartan transport as reusable mathematics from the within-chain rule,
  inverse-chart tangent cancellation, Mathlib Lie-bracket pullback, and constant-coordinate bracket
  vanishing; derive full principal inverse-chart naturality and same-connection coordinate Bianchi
  with only actual chart-target membership.
- [x] Join exact smooth adjoint-bundle curvature descent to the coordinate theorem through the same
  designated local section and tangent lifts. Keep this as a principal-representative chartwise
  bridge, not an intrinsic descended Bianchi theorem, until positive-degree adjoint-bundle
  differentiation and its coordinate coherence are constructed.
- [x] Define principal curvature from a certified derivative and the smooth bracket-wedge.
- [x] State and probe intrinsic curvature horizontality/right-adjoint-equivariance certificates.
- [x] Construct and probe the set-level adjoint associated-bundle orbit quotient.
- [x] Equip the adjoint bundle with its quotient topology and derive its quotient projection.
- [x] Derive representative-independent adjoint-bundle local coordinate and inverse laws.
- [x] Isolate joint adjoint continuity and conditionally package topological local trivializations.
- [x] Derive smooth adjoint regularity from parameter-dependent manifold differentiation.
- [x] Promote quotient charts to Mathlib's generic bundle-trivialization interface.
- [x] Derive exact fiberwise-linear adjoint transition formulas and inverse laws.
- [x] Prove smoothness of the exact model-coordinate adjoint transitions.
- [x] Build a named covering charted-space atlas on the quotient with explicit model transport.
- [x] Package the coordinate adjoint as a smooth continuous-linear-equivalence family.
- [x] Derive exact overlap-source coherence and smooth transition-equivalence families.
- [x] Prove fiberwise-linear groupoid compatibility and the quotient manifold structure.
- [x] Construct the dependent-fiber carrier and base-preserving equivalence to the quotient.
- [x] Pull back the quotient topology and prove a base-preserving total-space homeomorphism.
- [x] Transport named real vector-space structures to every dependent fiber.
- [x] Prove every designated associated fiber coordinate is linear for those structures.
- [x] Transport quotient trivializations exactly to the topology-coherent dependent total space.
- [x] Package the preserved topology and transported atlas as a named Mathlib `FiberBundle`.
- [x] Package the exact linear atlas as a named Mathlib `VectorBundle`.
- [x] Package the exact atlas as a named `C∞` vector-bundle mixin.
- [x] Define dependent adjoint-bundle sections and their exact smooth local-coordinate criterion.
- [x] Define pointwise adjoint-bundle-valued differential forms in actual dependent fibers.
- [x] Define smooth adjoint-bundle-valued forms by exact local field evaluation.
- [x] Prove the exact degree-zero form/section carrier and smoothness bridge.
- [x] Derive smooth principal local sections and projection-right-inverse tangent lifts.
- [x] Prove exact local tangent lifts preserve smooth base tangent fields.
- [x] Prove lift-independence for horizontal principal two-forms.
- [x] Prove adjoint-quotient representative independence under right translation.
- [x] Construct the pointwise dependent-fiber descent of horizontal equivariant two-forms.
- [x] Specialize pointwise descent to the exact certified principal curvature.
- [x] Prove smooth fixed-value form evaluation along maps from ambient smooth extensions.
- [x] Construct smooth chart-local ambient extensions of exact principal tangent lifts.
- [x] Prove smooth principal-form evaluation on exact local tangent lifts.
- [x] Transfer that evaluation through presentation independence to smooth generic two-form descent.
- [x] Specialize smooth descent to the exact certified curvature form.
- [x] Construct gauge-automorphism pullback of principal connections from the exact tangent map;
  derive vertical normalization, right equivariance, smoothness, identity, and contravariant
  composition rather than storing transformed-connection witnesses.
- [x] Pull smooth fixed-value forms through gauge diffeomorphisms in arbitrary degree, prove exact
  Lie-bracket-wedge pullback naturality, and show the curvature formula assembled from the pulled
  derivative carrier equals the pullback of the original exact curvature.
- [x] Prove within-set Cartan-certificate naturality under smooth diffeomorphisms with the explicit
  complete-source-model premise required by Mathlib; derive the premise for finite-dimensional
  principal total-space models, transform the exact indexed exterior certificate, and prove
  canonical principal curvature pullback naturality.
- [x] Construct the unique associated gauge function `g_ϕ` from the principal torsor, derive its
  right-action conjugation law and differentiated projection preservation, and combine canonical
  curvature pullback with horizontality/right equivariance to prove the evaluated local
  `Ad(g_ϕ⁻¹)` curvature formula.
- [x] Identify the unique associated function with exact principal-chart second coordinates,
  derive local-section and whole-chart-source smoothness from existing bundle regularity, and use
  atlas coverage to prove global `C∞` smoothness without assuming regularity of choice.
- [x] Construct the pointwise associated left Maurer–Cartan pullback, derive the exact variable
  principal-action tangent decomposition, and prove Freed's evaluated affine connection formula
  with `Ad(g_ϕ⁻¹)`, the plus sign, and the inhomogeneous `g_ϕ⁻¹dg_ϕ` term.
- [x] For every supplied exact smooth principal connection, derive smoothness of its inverse-adjoint
  transform and use the affine difference identity to bundle the unchanged associated
  Maurer–Cartan carrier as a smooth form without accepting a regularity witness.
- [x] Transport the exact original curvature structure certificate to the canonical gauge-pulled
  connection, deriving transformed horizontality/right-adjoint equivariance and a finite-dimensional
  wrapper; identify the pointwise descended curvature by exact adjoint and inverse-shifted quotient
  representatives without claiming equality to the original adjoint-valued curvature.
- [x] Construct the covariant gauge action on the actual adjoint quotient and dependent fibers with
  exact identity/composition/inverse laws; prove pointwise curvature and evaluations of the exact
  smooth descended package transform by the inverse induced fiber action.
- [x] Prove the exact selected-coordinate `Ad(g_ϕ)` formula and package every fixed dependent-fiber
  action as a continuous real-linear equivalence with exact inverse-gauge carrier and composition.
- [x] Descend continuity through the defining adjoint quotient, package the quotient action as a
  homeomorphism, and transport it to a base-preserving dependent-total-space homeomorphism whose
  fixed-fiber restrictions are the exact continuous-linear gauge actions.
- [x] Prove the arbitrary quotient-chart formula `(b,X) ↦ (b,Ad(g_ϕ(s(b)))X)`, globalize forward
  and inverse `C∞` regularity in the named quotient atlas, and package the quotient action as a
  diffeomorphism with its exact homeomorphism carrier.
- [x] Package the dependent action as a base-preserving total-space `C∞` diffeomorphism in the exact
  named smooth-vector-bundle structure, with fixed-fiber restrictions equal to the established
  continuous-linear equivalences.
- [x] Prove gauge invariance of the exact descended fiber pairing/quadratic value and derive
  pointwise invariance of chosen and basis-independent canonical curvature densities for the exact
  pulled connection/exterior/certificate chain.
- [x] Transport exact action integrability with unchanged measure/coupling and prove vertical gauge
  invariance of the integrated relative-to-measure Euclidean action.
- [x] Transport the finite interpreted fragment `1`, `F²`, `(F²)²` to the exact pulled chain with
  unchanged classical carrier, same quantum family/labels, and retained anti-collapse witnesses.
- [x] Define an independent algebraic quantum gauge action by conjugation on exact common-domain
  operators and require invariance for every label and smearing.
- [x] Derive one-way coherence of the exact designated quantum action with every label in the
  interpreted `1`, `F²`, `(F²)²` fragment and reject substitution of an unrelated action.
- [x] Specialize the action and exact-action invariance certificate to the canonical group of smooth
  automorphisms of one fixed principal bundle, without constructing a representation.
- [ ] Prove any further classical/quantum transformation-law coherence and extend invariance to the
  missing observable grammar.
- [x] Prove connection-independent direct smoothness of the exact associated Maurer–Cartan pullback
  using tangent-map calculus, and package its unchanged carrier as a smooth one-form.
- [x] Calculate the universal Maurer–Cartan Cartan expression on left-invariant fields, identify the
  associated form as its exact pullback, and package the smooth `-1/2[α∧α]` derivative candidate.
- [x] Prove field-extension independence in normed spaces, exact centered-chart coordinates, and
  intrinsically for any already supplied Cartan certificate.
- [x] Prove arbitrary-field partial-chart Cartan transport on the exact range-intersection set and
  derive intrinsic extension independence from explicit coordinate-form differentiability.
- [x] Derive generic finite-dimensional centered coordinate-form regularity and unconditional
  intrinsic extension independence for admissible smooth fields.
- [x] Construct the genuine universal left Maurer–Cartan exterior-derivative certificate and prove
  `dθ + 1/2[θ∧θ] = 0` on the finite-dimensional Lie group.
- [x] Identify the associated smooth derivative candidate exactly with the raw pullback of the
  certified universal derivative, and prove arbitrary-map `extDerivWithin` naturality in centered
  chart coordinates.
- [x] Prove exact chart-safe manifold-pullback/written-chart carrier and locality bridges, construct
  arbitrary-smooth-map certificates from exact smooth pullback packages in finite-dimensional
  models, and derive the certified associated Maurer–Cartan equation.
- [x] Construct fixed-model base extended-chart coordinates for actual dependent-fiber
  adjoint-valued forms on the exact principal-chart overlap, preserving corner-aware tangent
  transport and in-domain nonzero values.
- [x] Derive complete alternating-map-valued `C∞` regularity within the exact base/principal-chart
  overlap for smooth adjoint forms over finite-dimensional base models.
- [x] Package the exact-overlap local potential, exact descended-curvature coordinate, and typed
  same-chain `dF + [A∧F]` expression without asserting vanishing or chart independence.
- [x] Derive exact-set exterior naturality for the locally smooth designated section and prove the
  descended curvature coordinate is the curvature of the same exact local potential.
- [x] Derive exact-overlap potential regularity and domain geometry and prove the local same-chain
  `dF + [A∧F] = 0` theorem.
- [x] Identify every exact local Bianchi expression with the corresponding coordinate of the
  existing intrinsic smooth zero adjoint-valued three-form, without naming it as an operator.
- [x] Generalize horizontal fixed-value principal-form lift independence to every degree using a
  finite multilinear telescope, preserving definitional degree-two compatibility.
- [x] Generalize right-adjoint representative independence, actual dependent-fiber pointwise
  descent, arbitrary designated-chart coordinates, and smooth tensorial principal-form descent to
  every degree, preserving degree-two compatibility.
- [x] Construct the exact smooth positive-degree principal total-space candidate
  `dω + [Θ ∧ ω]`, tied to one unchanged connection, input form, and ordinary exterior certificate.
- [x] Prove that the derivative-defined Lie-group adjoint preserves the intrinsic tangent Lie bracket
  using conjugation diffeomorphism and Mathlib bracket naturality.
- [x] Derive arbitrary-degree Cartan-expression/certificate pullback through smooth diffeomorphisms
  and prove right-adjoint equivariance of the exact bracket correction.
- [x] Derive the bracket correction's exact one-/two-vertical-slot formulas and prove the precise
  ordinary-derivative cancellation rule is sufficient for full candidate horizontality.
- [x] Prove vertical tangents are uniquely generated by fundamental vectors, construct globally smooth
  fundamental fields, and derive their exact right-action curve velocities.
- [x] Construct the smooth right-invariant field and identify its exact left-trivialized coefficient
  as the smooth inverse-adjoint orbit.
- [x] Use the universal Maurer--Cartan certificate to compute derivatives of left-trivialized smooth
  fields and derive `d(Ad(·⁻¹)Y)₁(X) = -[X,Y]` conditionally on left/right invariant-field
  commutation at the identity.
- [x] Prove reusable unrestricted and corner-safe within-set Schwarz cancellation for opposite
  mixed-partial derivative fields under exact first-partial normalization hypotheses and exact
  `C²`-within regularity of Lie-group multiplication in
  the identity-centered chart on `range I ×ˢ range I`.
- [x] Prove both product-range first-partial normalizations and identify the identity-point chart
  coordinates of left- and right-invariant fields with the corresponding centered-multiplication
  partials; derive zero bracket for the exact normalized partial fields.
- [x] Upgrade the pointwise identifications to exact target-wide field equalities, derive intrinsic
  left/right invariant-field commutation at the identity, and prove `d(Ad(·⁻¹)Y)₁(X) = -[X,Y]` in the exact project
  derivative/model-coordinate carriers.
- [x] Apply the infinitesimal formula to the exact principal-orbit coefficient chain, derive all
  nondistinguished coefficient cancellations by horizontality, and reduce the ordinary vertical
  derivative to one explicit termwise triangular bracket-evaluation vanishing premise for globally smooth
  orbit-adapted fields.
- [x] Localize the Cartan reduction to arbitrary open calculus sets and construct prescribed-value
  orbit-adapted fields in base/group product coordinates, with open full-fiber domain, exact
  all-orbit right transport, and normalized fundamental/adapted fiber bracket zero.
- [x] Derive the exact product-manifold within-bracket vanishing theorem for the vertical
  fundamental and prescribed-value adapted product fields at the normalized center, with derivatives
  taken within the natural open domain.
- [x] Package open partial-diffeomorphism bracket naturality and transport the adapted fields through
  a designated smooth principal trivialization at points whose fiber coordinate is normalized to
  `1`, obtaining arbitrary prescribed values, all-orbit adaptation, and total-space bracket zero.
- [x] Normalize a principal trivialization at an arbitrary total-space point by an exact left shift
  of the group coordinate, extend the designated atlas by that one directly certified smooth chart,
  and obtain an adapted total field with arbitrary prescribed value at every point.
- [x] Assemble arbitrary indexed families of adapted fields with prescribed values on one exact
  common normalized-trivialization source, with simultaneous smoothness, all-orbit adaptation, and
  zero bracket against the designated principal fundamental field.
- [x] Use that common family plus horizontality to discharge every triangular Cartan evaluation,
  derive the unconditional fundamental-slot cancellation, and combine it with vertical tangent
  generation to prove full candidate horizontality.
- [x] Prove output-linear and diffeomorphism-pullback transport for positive-degree exterior
  certificates, then use certificate uniqueness to derive full right-adjoint equivariance of the
  ordinary derivative and complete candidate.
- [x] Descend the horizontal/equivariant candidate into the actual dependent adjoint-bundle fibers,
  and specialize it to an exact same-connection smooth intrinsic `D_A F` three-form carrier under
  the existing curvature-structure and supplied curvature-exterior certificates.
- [x] Generalize inverse-extended-chart alternating-map regularity to arbitrary degree and prove
  every positive-degree exterior certificate agrees at the chart center with the exact
  corner-aware `extDerivWithin` carrier, including `n = 0` coherence.
- [x] Connect the intrinsic `D_A F` representative to the existing same-chain coordinate Bianchi
  theorem, derive global principal-candidate zero by exact chart tangent cancellation, and prove the
  bundled descended intrinsic Bianchi identity without accepting a zero or naturality bridge.
- [x] Derive curvature horizontality from vertical generation, connection-specific Cartan
  cancellation and the exact half-self-wedge normalization; derive right-adjoint equivariance from
  exterior/bracket transport; package the exact finite-dimensional structure certificate.
- [x] Specialize the intrinsic `D_A F = 0` theorem so finite-dimensional callers no longer supply a
  redundant curvature-structure witness.
- [x] Prove arbitrary-degree Cartan transport for arbitrary local smooth fields on the exact
  corner-aware chart set, certificate-free field-extension independence, and set-germ locality.
- [x] Use that tensorial/local Cartan infrastructure plus coordinate Bianchi to construct the
  finite-dimensional ordinary curvature exterior certificate as `dF = -[A∧F]`, retaining exact
  same-connection provenance.
- [ ] Construct rather than accept the connection-indexed first exterior data; retain the generic
  arbitrary-manifold curvature structure/exterior certificate interfaces until their hypotheses can
  also be discharged.

## Phase 3 — classical Yang–Mills semantics

- [x] Define and probe the adjoint-invariant positive Lie-algebra inner product.
- [x] Induce its chart-independent positive pairing on actual adjoint quotient fibers.
- [x] Define and probe the positive chosen-orthonormal contraction of exact descended curvature.
- [x] Prove a reusable canonical-tensor theorem making bilinear quadratic contraction independent
  of the chosen orthonormal basis.
- [x] Package the exact quotient-coherent adjoint-fiber pairing as a bilinear map.
- [x] Prove an exact degree-two alternating-map-to-bilinear adapter.
- [x] Apply the adapter in each dependent adjoint fiber and prove the exact curvature contraction
  equals the canonical-tensor contraction and every orthonormal-basis sum.
- [ ] Connect the resulting canonical contraction to a general Hodge-star interface.
- [x] Define and probe the integrable Euclidean action relative to a designated Borel measure and
  positive coupling, with Clay's outer normalization explicit.
- [x] Prove the same action integrates the canonical basis-independent curvature scalar.
- [x] Prove positive rescaling of the named invariant pairing scales the exact fiber pairing and
  canonical curvature scalar by the same factor.
- [ ] Construct metric-volume semantics and prove compatibility with the designated measure.
- [x] Pin and visually verify Wilson's primary operator-product-expansion source.
- [x] Pin and visually verify the independent Gross–Wilczek and Politzer asymptotic-freedom papers.
- [x] Define a prerequisite same-domain family of local operator-valued tempered distributions and
  exact full-product weak bilocal distributions with unit/nonzero hostile evidence and locked
  operator order; strengthen the same family with exact label adjoints, same-representation scalar
  Poincaré covariance, and all-label bosonic locality. No curvature interpretation is claimed.
- [x] Add a reusable nonempty finite-component covariance interface with one strongly continuous
  lift-group representation, exact translation-trivial mixing, same-chain operator covariance, and
  anti-vacuity; separate a tensorial projected-Lorentz strengthening from possible spinorial central
  action and derive the existing nontrivial scalar field as a one-component trivial multiplet.
- [x] Classify every local-observable label in the 3D/4D cores through an explicit scalar/stress/
  residual split: scalar labels retain scalar covariance, exact stress labels retain their rank-two
  law without a duplicate mixing representation, and every residual bosonic label occurs in a
  finite projected-Lorentz multiplet. Spinorial fields remain outside this all-label bosonic-locality
  family and require a separate graded-locality surface.
- [x] Require exact adjoint/conjugate-representation partners for every residual multiplet inside
  the same cover, and fix every Hermitian stress-component label under the existing global family
  adjoint; no disconnected adjoint field family is introduced.
- [x] Add exact operator and adjoint-operator coherence identifying the scalar Wightman field with
  the same family's existing nontrivial label, transferring anti-vacuity and tempered matrix
  elements rather than allowing disconnected scalar and observable sectors.
- [x] Define normalized compact-anchor bilocal diagonal probes with `O(r)` support, an exact
  nondegenerate relative-coefficient/local-field contraction, finite monotone truncations, connected
  full-product remainders, and weak all-order little-`o` asymptotics.
- [x] Define a preliminary explicitly four-dimensional pure-gauge running-coupling/beta sign normal
  form on an open ultraviolet tail, without imposing infrared behavior or inventing the unresolved
  group-dependent coefficient normalization.
- [x] Add a supplied preliminary weak-distribution regular-variation condition on every nonzero
  coefficient of the exact OPE, with normalized short-distance tests, signed radial degrees,
  real running-coupling exponents, nonzero leading limits, and hostile anti-collapse probes.
- [ ] Derive rather than supply the relevant scaling laws: connect the leading beta/OPE coefficients
  to the exact gauge group/invariant-pairing/coupling convention, interpreted curvature-polynomial
  operators, anomalous-dimension mixing, scheme dependence and controlled perturbative remainders.
  Neither the generic OPE nor the supplied regular-variation condition meets Clay's
  prescribed-singularity requirement.
- [x] Define a symmetric Hermitian local stress-energy tensor inside the same local-observable/
  common-domain/Poincaré chain, with explicit rank-two Lorentz covariance, weak conservation and a
  nonzero non-unit energy-density witness.
- [x] Connect controlled `T^{0ν}` charge limits to common-domain momentum generators tied to the
  same physical translation unitaries and joint PVM, with all-family infinitesimal Ward identities.
- [x] Define the mostly-minus trace from the exact existing stress components and state the
  renormalized four-dimensional trace anomaly only on an explicit nonempty physical, on-shell,
  nonzero-momentum weak-matrix-element selection, tied to the exact interpreted `F²`, normalized
  beta function, and classical reference. Keep the CDJ source convention and the separately
  supplied project outer-coupling operator-rescaling bridge explicit; do not promote classical
  tracelessness or assert an unrestricted quantum operator identity.
- [x] Tie a basic nonzero/non-unit quantum `F²` label to the exact canonical curvature density and
  exact classical/quantum spacetime dimension, without asserting a global injective quantization map.
- [x] Extend that exact label to the finite intrinsic scalar fragment `1`, `F²`, `(F²)²`, expose
  exact classical-carrier coherence, and separately require `(F²)²` anti-collapse as an explicit
  project strengthening in the 4D core. The core now carries one exact designated quantum action of the canonical smooth-principal gauge group and all-label invariance certificate, with the finite interpreted fragment
  connected to that same action. A natural-indexed same-family strengthening now covers every
  `(F²)ⁿ`, restricts exactly to the finite fragment, places every label in the scalar sector, and
  derives invariance under the same action. Independent invariant contractions, mixed polynomials,
  covariant derivatives, renormalized mixing, and further classical/quantum transformation-law
  coherence remain open.
- [x] Prove topological-module compatibility for every exact dependent adjoint fiber and define the
  continuous derivative-slot/alternating-curvature tensor carrier, with order zero locked to the
  exact smoothly descended curvature.
- [x] Define an uninhabited Mathlib covariant derivative on exact adjoint sections and tie it in every
  designated chart to the same principal connection by the explicit `dσ + [A,σ]` formula.
- [x] Add Mathlib's standard `C∞` covariant-derivative regularity as an explicit strengthening and
  derive the exact smooth derivative-bundle output for every smooth adjoint section.
- [x] Canonically package the same-connection derivative of every pointwise degree-zero
  adjoint-valued form as a degree-one form, with exact unique-slot evaluation, section coherence,
  and output uniqueness; derive the designated-chart `dσ + [A,σ]` formula for smooth inputs only.
- [x] Use the stored `C∞` covariant-derivative regularity and smooth dependent bundle evaluation to
  prove that the exact degree-one packaged output is smooth for every smooth degree-zero input,
  without introducing a new regularity field or claiming positive-degree differentiation.
- [ ] Extend that same-connection derivative to adjoint-valued forms and positive curvature-tensor
  orders, derive Bianchi rather than storing it as a certificate, and extend the basic bridge to
  interpreted gauge-invariant local curvature polynomials, including renormalized operator mixing.
- [ ] Separate local observables from nonlocal Wilson observables.
- [ ] Add nontrivial positive examples and hostile disconnected-curvature probes.

## Phase 4 — Euclidean and Minkowski quantum surfaces

- [x] Pin OS-I, correcting OS-II, Wightman primary/authoritative source bytes with verified locators.
  - [x] Hash-pin full transformed Project Euclid reader extracts and verify the OS-II correction and
    linear-growth locators as provisional searchable evidence.
  - [x] Acquire, signature-check, text-extract, and visually verify OS-I/OS-II primary article scans,
    the Wightman 1956 paper, and the Streater–Wightman axiomatic source.
- [x] Define normalized scalar tempered Schwinger families and explicit Mathlib fixed-order
  factorial-growth infrastructure, with the OS test-space/seminorm equivalence left visible.
- [x] Define exact positive-arity Schwartz pullback and scalar Schwinger permutation symmetry `(E3)`.
- [x] Define proper-Euclidean rigid motions, exact Schwartz pullback, and scalar covariance `(E1)`.
- [x] Define exact Euclidean time reflection and strict-positive-time Schwartz support infrastructure.
- [x] Construct an explicit nonzero arity-one Schwartz test with strict-positive-time support.
- [x] Define a strict Mathlib subspace using topological-support time ordering and infinite-order
  Fréchet flatness on point-coincidence diagonals.
- [x] Package algebraic finite test sequences with an exact nonzero-arity support finset.
- [x] Represent the scalar zero-point component as a zero-arity Schwartz test and derive exact finite
  natural-arity support for uniform convolution indexing.
- [x] Construct exact continuous configuration split/merge maps and the raw scalar tensor kernel.
- [x] Prove a reusable generic scalar Schwartz tensor product with explicit decay bounds and
  algebraic bilinearity.
- [x] Pull the bundled tensor through exact configuration splitting and prove exact evaluation and
  algebraic bilinearity on concatenated Euclidean configurations.
- [x] Define the unrestricted finite Schwartz-sequence algebra carrier and an exact forgetful map
  from the strict positive-time sequence.
- [x] Define the exact finite per-arity convolution, including zero/one endpoint formulas and the
  nonzero internal singleton-bump split.
- [x] Prove finite support for the convolution family and package it in the unrestricted carrier.
- [x] Construct the named finite-stage final topology and prove its exact universal property.
- [x] Construct named, locally installed additive-group and complex-module structures on the exact
  finite sequence carrier.
- [x] Bundle every generating finite-stage map as a continuous complex-linear map.
- [x] Construct the exact continuous linear natural coordinate injections.
- [x] Prove the exact linear coordinate-injection continuity criterion for the preliminary
  finite-stage final topology.
- [ ] Prove joint sequence addition/scalar continuity and compare the
  finite-stage final topology with OS-I's locally convex direct sum, and prove any needed product
  continuity.
- [x] Construct the exact reverse-conjugate involution on scalar Schwartz components.
- [x] Lift reverse-conjugation and Euclidean time reflection to finite sequences and define the
  exact combined operation `Θ f*`.
- [x] Define and probe the algebraic reflection-positivity form on the current strict Mathlib
  subdomain.
- [x] Define a broader project-dimension Fréchet candidate whose every derivative vanishes outside
  strict positive time order, package the condition as an exact complex Schwartz submodule, install
  its exact induced per-arity Schwartz topology, include the
  strict-support carrier, and provide a nonzero test with hostile probes.
- [x] Construct the exact point/coordinate basis and prove full Fréchet-map vanishing equivalent to
  all ordered coordinate-basis jet evaluations, with a reusable multilinear basis-determination
  theorem and nonzero-detection probes.
- [x] Prove the dimension-generic Fréchet candidate is closed in the exact ambient Schwartz topology
  by expressing it as an intersection of continuous coordinate-directional jet kernels, and package
  its forgetful map as a closed embedding with hostile limit probes.
- [x] Specialize to four dimensions, flatten `(point, coordinate)` exactly as `μ + 4i`, define
  natural-valued multi-indices on `Fin (4n)`, enumerate every coordinate occurrence with exact
  multiplicity, and prove the established Fréchet candidate implies every canonical repeated-basis
  multi-index derivative vanishes.
- [x] Define arbitrary occurrence enumerations of each four-dimensional multi-index, derive exact
  fiber-cardinality multiplicities and an enumeration from every ordered coordinate tuple, prove
  exact tuple recovery, and prove all-enumeration multi-index vanishing equivalent to the existing
  Fréchet/coordinate-jet candidate.
- [x] Prove reusable permutation symmetry of every iterated Schwartz directional derivative from
  second-derivative commutation and permutation-invariant list folds; derive exact independence of
  multi-index occurrence enumeration and equivalence of the canonical multi-index and Fréchet
  candidate predicates.
- [x] Prove the standard Schwartz seminorm family separates points and package named `T1Space` and
  `T2Space` structures as reusable mathematics rather than assuming ambient Hausdorffness.
- [x] Interpret OS-I's four-dimensional `D^α` as the proved permutation-independent repeated-
  coordinate Fréchet derivative, define exact positive-arity source membership, prove it equivalent
  to the Fréchet candidate, transport closedness, install the induced topology, and retain a nonzero
  source-space test with hostile probes while keeping OS-I's scalar zero-point component separate.
- [x] Package each exact positive-arity source space as an exact complex Schwartz submodule and
  transport named additive-group and complex-module structures with exact underlying operations.
- [x] Prove exact source-space addition, negation and complex scalar multiplication continuous for
  the induced Schwartz topology and package named topological-algebra structures.
- [x] Package the exact forgetful map as a real-linear inducing map and transport named real local
  convexity from ambient Schwartz space to every exact positive-arity source space.
- [x] Assemble the separate scalar `f₀`, finitely many exact positive-arity source components and
  exact nonzero support into the four-dimensional algebraic OS source-sequence carrier; map the
  earlier strict sequence componentwise without a properness claim and retain explicit scalar-unit and nonzero-bump sequences.
- [x] Forget the exact source sequence into the unrestricted finite Schwartz algebra without changing
  scalar, support, or positive components; define algebraic source-carrier `(E2)` on the exact
  reflected-star convolution, and prove it implies the strict-subdomain predicate.
- [x] Construct the exact-source finite-stage products, stage maps, exact-support recovery, named
  finite-stage final topology and its all-stage universal property, retaining the separate scalar.
- [x] Identify exact source sequences with a scalar times a dependent finitely supported source-
  space family and transport named additive-group and complex-module structures with exact scalar
  and component laws.
- [x] Prove every exact-source finite-stage extension complex-linear and package it as a continuous
  complex-linear map into the named final topology, with exact support and nonzero-stage probes.
- [x] Install named topological additive-group, continuous complex scalar, and real locally convex
  structures on every exact finite stage, including the independent empty-stage scalar coordinate.
- [x] Present the final topology as the quotient of the disjoint union of all exact finite stages;
  use local compactness of `ℂ` to prove joint complex scalar continuity, derive negation continuity,
  and prove finite-union stage addition and separate sequence addition continuity. Keep joint
  addition conditional on the still-unproved product-quotient property.
- [x] Construct the separately named locally convex final topology as the `sInf` of all stage-continuous
  real-locally-convex topological complex-module topologies; prove it admissible, package its joint
  operations and stage CLMs, compare it with the raw final topology, and characterize equality by
  raw admissibility without asserting that equality or OS-I direct-sum identification.
- [x] Construct the exact scalar/all-positive-arity coordinate map, prove it injective and continuous
  via an admissible induced coordinate topology, and derive Hausdorff separation of the locally
  convex final topology while retaining the explicit nonzero singleton coordinate.
- [x] Prove the finite-stage universal property: a complex-linear map from source sequences into any
  real-locally-convex topological complex module is continuous exactly when every finite-stage
  composite is continuous; package and uniquely determine stagewise continuous-linear maps.
- [x] Construct OS-I's separate scalar and every positive-arity natural injection, prove exact
  finite-stage decomposition and injection continuity, derive the paper's coordinatewise universal
  property, and designate the Hausdorff locally convex final topology as the source-facing locally
  convex direct-sum topology with named topological/local-convex/Hausdorff structures and bundled
  natural-injection CLMs, while keeping the raw topological final topology separately named and
  without asserting equality.
- [x] Package exact Schwartz point evaluation as a continuous real-linear map, prove every kernel
  closed, and prove point evaluations detect and determine every Schwartz map as infrastructure for
  closed support subspaces and half-line quotients.
- [x] Construct OS-I's exact closed negative-half-line Schwartz submodule, prove membership
  equivalent to nonpositive topological support, form the genuine Hausdorff locally convex
  topological complex-module quotient `𝒮(ℝ₊)`, and retain an explicit nonzero positive representative.
- [x] Isolate missing completed projective tensor-product mathematics in a typed interface requiring
  Hausdorff locally convex complex factors, an additive-uniform complete carrier, jointly continuous
  noncollapsing pure tensors, dense pure span, and continuous-linear extension into same-universe
  complete targets, with uniqueness derived from density.
- [x] Define the neutral spatial `ℝ³` selected by four-dimensional spacetime and source-facing
  scalar-functional tensor candidate data for the factors `𝒮(ℝ₊)` and `𝒮(ℝ³)`, with explicit
  nonzero factors forcing a nonzero pure tensor in every supplied candidate; state explicitly that
  scalar extensions do not characterize the completed projective tensor topology.
- [x] Package zero-based fixed-left-associated scalar-functional candidates at every intended finite
  positive tensor power, with jointly continuous noncollapsing successor pure tensors, dense pure
  span, scalar-valued extension, density-derived uniqueness, and a recursively nonzero test; assert
  no completed tensor characterization, nuclearity, associator, permutation equivalence,
  product-Schwartz identification, or carrier.
- [ ] Establish the earlier strict-support subspace's sufficiency/density/completion relation to the
  exact positive-arity OS-I source spaces; prove the half-line quotient complete with the source's
  Fréchet presentation; represent nuclearity; construct or characterize the completed projective
  tensor carrier and iterated powers while keeping them separate from the direct sum and its already
  defined algebraic source-carrier `(E2)`.
- [x] Construct exact simultaneous Euclidean translations on Schwartz tests and finite sequences,
  with inverse and support preservation, as algebraic `(E4)` infrastructure.
- [x] Define normalized nonzero spatial rays, prove escape to infinity, construct the four-dimensional
  ray, and reject a one-dimensional spatial direction.
- [x] Define and probe the exact clustering factorization expression and zero-limit predicate along
  an explicitly supplied direction on the current strict Mathlib subdomain.
- [x] Assemble growth, `(E1)`, `(E3)`, strict-domain positivity, and direction-indexed clustering
  around one coherent normalized family in a non-source-facing candidate record.
- [x] Define source-facing `(E4)` on every exact four-dimensional source pair and normalized nonzero
  spatial direction, and prove it restricts exactly to every strict-direction predicate.
- [x] Define equation (2.1)'s exact flattened-coordinate weighted multi-index least-upper-bound
  control, carrier-exact OS-II `(E0′)` functionals/bounds on `𝒮₀`, and the one-way restriction from a
  separate ambient-tempered-extension strengthening.
- [x] Assemble current-strength `(E0′)`–`(E4)` Euclidean data and narrow same-field uniqueness for
  selected `(R0′)`/relative/source-Wick correlator extensions.
- [x] Define heterogeneous scalar Wightman-realization unitary equivalence intertwining lift groups,
  representations, vacua, common domains, fields and adjoints; derive equality of every finite
  field/adjoint vacuum word.
- [x] Define corrected reconstruction acceptance over the same exact Poincaré lift and selected
  Hilbert universe, requiring heterogeneous Hilbert-unitary equivalence and equality of the
  separately supplied full tempered-distribution families for every corrected, source-Wick-coherent
  output in that scope; same-field uniqueness remains supporting evidence.
- [x] Define proper-orthochronous Lorentz/Poincaré affine kinematics independently of the Euclidean
  Schwinger surface.
- [x] Define a topological-group lift/pre-cover interface and one strongly continuous unitary
  representation whose injective translation subgroup is derived from that same representation.
- [x] Install the exact Lorentz-action/translation coordinate topology on the affine target and
  require the existing surjective lift projection to be a genuine Mathlib covering map, deriving
  continuity, local-homeomorphism, open/quotient behavior, and discrete fibers.
- [x] Strengthen the genuine cover so every exact affine fiber is equivalent to `Fin 2`, deriving
  finite fibers and two distinct lifts without choosing matrix-sign labels.
- [x] Require a named affine-target topological-group law with exact identity/action composition,
  prove multiplication is action-determined, and derive the double-cover projection as a bundled
  group homomorphism.
- [x] Construct the literal complex-unit subgroup `{1,-1}` and derive from the existing homomorphic
  `Fin 2` cover that the exact projection kernel is multiplicatively equivalent to it and central;
  derive a nonidentity negative-sign lift without adding a redundant acceptance field, and prove
  every fiber consists of any selected lift and its distinct negative-sign partner.
- [x] Prove that every identity-projecting lift acts trivially in any cyclic scalar Wightman
  realization, using exact field/adjoint covariance, vacuum invariance, word induction, cyclicity,
  and continuity; bundle the dependent chain to transport the theorem across the 4D core's exact
  propositional cover-to-lift equality.
- [x] Descend the cyclic scalar representation to a choice-independent unitary homomorphism on the
  named affine target; derive strong continuity through the genuine cover's quotient-map law,
  descend common-domain field, adjoint, and same-domain local-observable-family covariance with no
  lift exposed, and integrate both the transported Hilbert representation and original uncast
  domain/field/observable-family covariance into the 4D core.
- [x] Expose Mathlib's concrete homogeneous `SL(2,ℂ)` matrix carrier, embed the literal complex
  signs injectively as the central determinant-one scalar matrices `±I`, derive an abstract
  multiplicative equivalence from every accepted two-sheet kernel to this exact image subgroup, and
  install the exact matrix-subspace topology as a Hausdorff topological group.
- [x] Polarize the exact mostly-minus quadratic form, derive zero-time nonpositivity and bilinear
  preservation, prove inverse time-orientation equality, and construct the exact inverse inside the
  proper-orthochronous Lorentz carrier.
- [ ] Prove whole-future-sheet preservation and composition closure, construct the affine target law,
  build the concrete inhomogeneous semidirect-product cover, and realize its actual projection kernel as that matrix-sign
  image inside the same ambient group rather than merely by abstract equivalence, and upgrade
  relative sheet labels to this realization; then add the required Lie-group/manifold structure.
- [x] Define a normalized Poincaré-invariant vacuum whose full invariant subspace is exactly one
  complex line, tied to the same representation and derived translations.
- [x] Define one dense common domain containing the same vacuum and invariant under the same
  Poincaré representation, with exact restricted unitaries.
- [x] Define a scalar Wightman field and adjoint preserving that exact domain, with coherent
  tempered matrix elements and the conjugated-test adjoint relation.
- [x] Define the exact inverse-affine scalar test pullback and covariance of field and adjoint under
  the same restricted physical unitaries.
- [x] Define finite field/adjoint words on the exact domain vacuum and require their Hilbert-space
  span to be dense.
- [x] Define scalar bosonic locality for field and adjoint using spacelike-separated topological
  supports, prove nonzero locality test pairs exist in dimensions at least two, and prove dimension
  one has no spacelike point pair.
- [x] Define forward-cone joint spectral data independently and tie it to the exact physical
  translation representation through the SNAG Fourier formula.
- [x] Integrate covariance, cyclicity, locality, and forward-cone spectrum on one exact scalar
  field/domain/vacuum/representation chain, while retaining mass gap as an optional predicate.
- [x] Extract normalized algebraic smeared vacuum correlators from exact finite field words and lock
  one- and two-point operator order.
- [x] Require actual full-product tempered distributions at every arity, coherent with exact ordered
  field-word values on every finite pure Schwartz tensor.
- [x] Construct the exact-sign open backward tube `ξ - iη`, `η ∈ V₊°`, and prove explicit
  nonemptiness/strictness in dimensions 1–4.
- [x] Package genuine tube holomorphy and all-direction tempered-distribution boundary convergence,
  with exact integrable tube-function regularizations.
- [x] Require uniform radial polynomial growth on every compact strict imaginary-direction set as an
  explicit normal form; comparison with arbitrary source polynomials remains pending.
- [x] Connect full correlators to relative tempered distributions through exact consecutive-
  difference/normalized-anchor Schwartz lifts, require independence of every normalized anchor, and
  use that exact relative distribution as the polynomially bounded tube boundary.
- [x] Define determinant-one proper complex Lorentz kinematics preserving the exact complex-bilinear
  mostly-minus form, with group action, continuity and a nonidentity four-dimensional element.
- [x] Construct the exact open invariant extended-tube orbit, prove ordinary-tube inclusion and
  strict four-dimensional enlargement, and keep zero excluded at positive arity.
- [x] Package single-valued scalar holomorphic extended-tube continuation with exact restriction,
  invariance, orbit-source independence and an all-arity bridge to the same relative correlator chain.
- [ ] Add the transformation-group topology/analytic structure and derive the continuation and
  covariance theorem rather than merely requiring its conclusion.
- [x] Define the first explicit Euclidean/Minkowski bridge: reverse strict Euclidean point order,
  Wick-rotate `τ ↦ -iτ`, and prove all consecutive relative coordinates lie in the backward tube.
- [x] Require exact genuinely integrable Euclidean/Wightman correlator-value continuation on every
  current strict ordered/flat Mathlib test, using the reverse-Wick analytic function.
- [x] Extend that same coherence to every exact derivative-vanishing ordered OS source test and
  derive the old strict bridge by restriction.
- [x] Define corrected-output Wightman `(R0′)` on the exact full correlator family with one common
  positive order, printed full-coordinate controls, and `0 < ωₙ ≤ α β^(n²)`.
- [x] Require all-arity distribution uniqueness among corrected/coherent correlator extensions on
  one exact field realization, with selected `(R0′)`, relative, and source-Wick data bundled.
- [x] State corrected OS-II reconstruction acceptance requiring fixed-lift heterogeneous
  Hilbert-unitary equivalence and full distribution equality for all universe-relative coherent
  outputs, without constructing an output.

## Phase 5 — translations and mass gap

- [x] Package a normalized, self-adjoint, strongly countably-additive joint
  projection-valued-measure interface.
- [x] Tie energy and momentum to one strongly continuous translation representation through finite
  diagonal spectral measures and an exact, genuinely integrable SNAG Fourier formula.
- [x] Define forward-cone support, exact vacuum-line zero-momentum projection, invariant mass, and
  a positive-threshold joint-spectral gap predicate without constructing a witness.
- [x] Derive the normalized Hamiltonian spectral projection as the energy-coordinate pushforward of
  the same PVM; prove its `(0, Δ)` projection is zero and a bounded positive-energy band is nonzero.
- [x] Reject empty, full, unrelated-representation, vacuum-only, nonpositive-threshold, and
  no-finite-excitation spectral surrogates.
- [x] Define the Clay mass as the supremum of source-facing positive same-PVM Hamiltonian
  thresholds; prove that any stronger physical joint gap makes this set nonempty and bounded above
  with positive supremum.

## Phase 6 — optional lattice route

- [x] Pin and visually verify Wilson and Osterwalder–Seiler primary lattice sources.
- [x] Define dimension-indexed nonempty finite periodic lattices, group-valued positive links,
  endpoint gauge transformations, plaquette holonomy/orientation reversal, and a nontrivial
  normalized nonnegative Wilson-type potential with strictly positive coefficient and exact gauge
  invariance.
- [x] Define signed finite lattice paths, endpoint-covariant holonomy, closed paths, and nontrivial
  closed-loop observables from supplied nonconstant conjugation-class functions with exact local
  gauge invariance; gauge-field nonconstancy and character/continuity interpretation remain pending.
- [x] Define an exact finite-cutoff Gibbs acceptance interface over a supplied normalized,
  gauge-invariant reference measure, with positive finite partition function and genuinely
  integrable bounded-observable expectations.
- [x] Construct probability-normalized compact Haar measure, its exact finite link product and
  marginals, and prove local gauge invariance; specialize the Gibbs checker definitionally to this
  reference and derive partition/Gibbs normalization and invariance from one measurable density.
  No potential-measurability or Gibbs datum is currently constructed.
- [x] Give signed paths exact finite positive-link supports; package bounded measurable class
  observables as support-local, gauge-invariant, genuinely integrable closed-loop expectations
  conditional on the same product-Haar Gibbs datum.
- [x] Define simultaneous spacing-to-zero, sites-per-axis/physical-linear-extent-to-infinity and
  bare-coupling
  trajectories with exact stagewise Gibbs data, explicit bare/action normalization, and conditional
  convergence of support-local observable expectations to an independently supplied target.
- [ ] Define renormalization, continuum field/OS identification, and interpreted-observable bridges;
  the expectation-level scaling interface alone is not a continuum Yang–Mills construction.
- [x] Define explicit even-periodic lattice time reflection and a finite-cutoff reflection-positivity
  checker over designated sufficient positive-link support with an actual-dependence witness and
  the same product-Haar Gibbs datum, with nonzero-domain hostile evidence; keep it definitionally distinct from continuum OS `(E2)`. No positivity datum is
  constructed.

## Phase 6A — compact nonabelian Fourier and Peter–Weyl infrastructure

- [x] Bridge square matrix-valued monoid homomorphisms to Mathlib `Representation` on standard
  coordinate vectors; identify the abstract character exactly with matrix trace, expose exact matrix
  coefficients, and derive coefficient/trace continuity and conjugacy invariance.
- [x] Construct the normalized-Haar average of the standard coordinate Hermitian pairing for every
  continuous finite matrix representation; derive compact-domain integrability, exact simultaneous
  representation invariance, and strict positivity of the averaged norm square from open-support
  positivity of Haar measure.
- [x] Prove the averaged pairing's conjugate symmetry, first-argument additivity/conjugate
  homogeneity, exact real self-norm identity, nonnegativity, and definiteness; package it as a named
  `InnerProductSpace.Core` without overwriting the coordinate carrier's pre-existing norm.
- [ ] Prove compatibility/equivalence with a finite-dimensional normed realization and derive an
  explicit unitarizing coordinate equivalence.
- [x] Construct the coordinatewise Reynolds/Haar average
  `P(A)=∫σ(g⁻¹)Aρ(g)dμ_H` for arbitrary rectangular matrices between two continuous finite matrix
  representations; derive coefficient integrability and the exact intertwining identity
  `σ(h)P(A)=P(A)ρ(h)` by right-Haar substitution.
- [x] Bundle the analytic average as Mathlib's exact `IntertwiningMap`; derive the irreducible
  bijective-or-zero dichotomy and prove that every averaged rectangular matrix vanishes for
  irreducible inequivalent coordinate representations.
- [x] Use algebraic closedness of `ℂ` and Mathlib's endomorphism Schur theorem to prove every
  irreducible self-average is a complex scalar multiple of the identity; name that scalar without
  guessing its value.
- [x] Prove normalized-Haar conjugation averaging preserves matrix trace; derive
  `n·c_A=tr(A)` and, for `n>0`, the exact self-case Schur scalar `c_A=tr(A)/n`.
- [x] Derive from the exact representation homomorphism and one-sided unitary law that
  `ρ(g⁻¹)=ρ(g)ᴴ`, including transposed conjugate entry and full inverse-character conjugation laws;
  rederive Driver's stored real character inversion law from this stronger theorem.
- [ ] Conclude full Haar orthogonality of matrix coefficients with the exact dimension
  normalization.
- [x] Define coordinatewise representation-valued Fourier coefficients with exact inverse
  convention, derive continuous compact-domain integrability, addition/scalar/zero laws, specialize
  to probability-normalized Haar, and identify matrix trace with the scalar inverse-character
  coefficient.
- [x] Define the exact complex Haar convolution `(f⋆g)(z)=∫f(x)g(x⁻¹z)dμ_H` and prove by
  compact-product integrability, Fubini, and left-Haar substitution that the inverse-convention
  matrix Fourier transform satisfies `(f⋆g)̂(ρ)=ĝ(ρ)f̂(ρ)` in the forced reversed order.
- [ ] Construct finite coefficient subspaces, algebraic Plancherel, and character orthogonality for
  central functions.
- [ ] Prove Stone–Weierstrass separation and Peter–Weyl density/completeness in continuous and `L²`
  carriers with explicit topology and measure hypotheses.
- [ ] State and prove only convergence-justified Fourier inversion and central character expansions;
  do not treat formal representation sums as convergent by default.
- [ ] Compare the invariant basis-sum operator with Laplace–Beltrami, derive Casimir eigenvalues on
  coefficients, and construct normalized compact-group heat-kernel spectral expansions with exact
  `½Δ` convention.
- [ ] Feed the derived heat kernel and character expansions into the 2D Driver/Lévy/Sengupta track
  without making Peter–Weyl conclusions acceptance fields.

## Phase 7 — dimension contracts and final checker

- [x] Add the kinematic/lattice degenerate-topological `d = 1` boundary: degree-two local forms and
  plaquette action vanish, spatial clustering/spacelike pairs are absent, but global periodic
  holonomy and analytic tube geometry can remain. This is not a one-dimensional theory witness.
- [ ] Add rigorous `d = 2` consistency models.
  - [x] Prove first nondegeneracy witnesses: a nonzero area two-form, spatial ray, nonzero spacelike
    tests, and a concrete positive-density elementary plaquette for every admissible potential.
  - [x] Ingest and audit Driver, Gross–King–Sengupta, Sengupta, Lévy, Witten, and Atiyah–Bott with
    exact role separation for rigorous probability/holonomy, lattice convergence, heat-kernel
    sewing, and classical geometry.
  - [x] Add the uninhabited source-specific Driver gauge-fixed probability/ambient-holonomy nucleus:
    the sample law is normalized and exact, gauge transformations act only on a separate ambient
    connection carrier, sampled holonomy/observables use the exact restriction map, and physical
    invariance is not falsely promoted to invariance of the gauge-fixed slice measure.
  - [x] Extract probability-normalized compact Haar measure and its left/right/inversion invariance
    into neutral reusable mathematics shared by lattice and continuum layers.
  - [x] Add one uninhabited selected closed positive-area loop marginal: its exact sampled-holonomy
    pushforward is a central/inversion-symmetric density against canonical normalized Haar, and one
    exact physical observable/class-function bridge derives the corresponding expectation formula.
    Deliberately do not call it a heat kernel without metric/Laplacian/Brownian/semigroup data.
  - [x] Fix neutral normalized-Haar density convolution with the exact `x⁻¹ * g` orientation and add
    an uninhabited same-density positive-time convolution semigroup: all-time normalization, weak
    convergence to the identity, and the selected-area two-half split are exact and probed.
  - [x] Construct scalar first and iterated derivatives along the exact right-invariant group fields;
    package Driver's nonempty invariant-pairing-orthonormal basis sum and require exact independence
    from every other orthonormal basis. Constants are derived to lie in the kernel.
  - [x] Add a strictly positive spatially smooth real representative tied pointwise by
    `ENNReal.ofReal` to the unchanged density, indexed at compact Lie-group scope by the same
    semigroup and pairing Laplacian without a compact-simple datum, and require Driver's exact `∂ₜQ = ½ΔQ` sign/factor convention.
  - [x] Add an uninhabited continuous-path group process over that general heat core with exact identity start, mutually
    independent stationary right increments having the unchanged density laws, derived one-time
    marginals, and exact selected-area equality with the sampled loop-holonomy law.
  - [x] Construct an everywhere-continuous jointly `NNReal × Ω` measurable modification by replacing
    paths on a measurable null discontinuity hull; prove simultaneous all-time almost-sure equality,
    identity start, every finite monotone mutual increment-independence law, and preservation of
    every fixed-time and positive stationary-increment law; repackage it as the same Brownian
    acceptance structure on the unchanged sample carrier and probability measure; prove all finite
    time-evaluation vectors measurable with unchanged joint distributions and retain selected-area
    sampled-loop coherence.
  - [x] Transport the exact invariant pairing pointwise by left Maurer–Cartan trivialization; prove
    its inverse, symmetry, strict positivity, exact left/right translation formulas, and
    bi-invariance with the required `Ad(h⁻¹)` convention.
  - [x] Prove finite-dimensional von Neumann boundedness of strictly positive continuous bilinear
    unit ellipsoids by a reusable compact-unit-sphere theorem and discharge the exact obligation for
    each pointwise group tangent pairing.
  - [x] Prove centerwise smoothness of the exact parameter-dependent left Maurer–Cartan derivative
    after Mathlib's tangent-coordinate transport.
  - [x] Prove finite-dimensional smooth diagonal bilinear precomposition, reconcile it exactly with
    the two nested metric Hom-bundle coordinate transports, derive dependent-section smoothness,
    and assemble the actual `ContMDiffRiemannianMetric` with the unchanged pointwise form.
  - [x] Add reusable finite oriented-edge words with one coordinate per underlying edge, exact
    inversion for reverse orientation, reverse-word inversion, and Driver-compatible later-on-the-
    left concatenation.
  - [x] Add oriented source/target semantics, target-left vertex-gauge action, internal-factor
    cancellation for composable words, and exact start-vertex conjugation for closed words.
  - [x] Construct the reusable finite product of canonical normalized Haar probability over one
    coordinate per underlying edge; derive exact marginals and preservation by every endpoint gauge
    action.
  - [x] Prove measurability of finite oriented-word holonomy and finite products of supplied
    nonnegative density slices; construct the generic product-Haar `withDensity` carrier while
    retaining the face-free endpoint and making no normalization or planarity claim.
  - [ ] Compare the metric's Laplace–Beltrami operator with the basis sum.
  - [x] Define a concrete uninhabited simple-boundary topological planar graph certificate: ambient
    path realizations in `ℝ²` coherent with reversal/concatenation, concrete finite vertical/`C¹`-
    horizontal decompositions for every edge with documented affine-speed strengthening, separated
    vertices, injective edge arcs, endpoint-only crossings, exact disjoint complement decomposition,
    a finite connected-cell decomposition after adjoining Driver's x-axis, bounded connected
    open faces, segmentwise word-realized once-around Jordan frontiers, and positive coordinate-
    Lebesgue areas; retain face-free graphs and block doubled circuits.
  - [x] State an uninhabited Jordan-boundary-subclass face-product law universally over every
    measurable, integrable finite vertex-gauge-invariant complex graph function; tie each function
    pointwise to an existing ambient gauge-invariant observable through the same selected paths,
    use the unchanged density at exact geometric face areas and exact boundary words over product
    Haar, and derive carrier normalization from the constant-one case.
  - [x] Isolate finite BC boundary-word combinatorics: exact alternative-path bridge semantics,
    equal opposite-orientation bridge multiplicity, at-most-once nonbridge use, and hostile rejection
    of doubled cycle edges. This is not yet a planar BC certificate.
  - [x] Factor boundary-neutral embedded geometry and integrate the finite word certificate into an
    uninhabited strengthened embedded-arc BC certificate: literal connected face frontiers, exact
    frontier traces, and continuous closed segmentwise ordered traversals with legitimate bridge
    multiplicity. Retain the explicit edge-subdivision requirement for Driver-permitted loop incidence.
  - [x] State the corresponding uninhabited BC face-product law universally over every measurable,
    integrable finite vertex-gauge-invariant complex graph function, with exact ambient-path
    interpretation, unchanged area density, bridge-aware words, product Haar, and unit-derived
    normalization.
  - [x] Add a general disconnected-boundary interface whose choice carrier is the full structure of
    every valid simultaneous presentation, not a supplier-selected family: exact finite ordered
    component words/traversals, nonempty pairwise-disjoint maximal connected frontier traces,
    Definition 6.3's exact optional coordinate-zero root and conditional restricted gauge
    invariance, a universal choice-indexed expectation law, and derived integral-level choice
    independence and normalization.
    Do not impose false pointwise equality across choices.
  - [x] Add Theorem 6.4's universal tree-freezing clause over every Definition 5.1 tree, with exact
    identity-Dirac/Haar product factors, unchanged choice-indexed face density and ambient
    expectation, and derived frozen/unfrozen, cross-tree/choice, normalization, and nonzero results.
  - [x] Add Lévy refinement/projective consistency: exact fine-word configuration maps, reverse
    substitution, endpoint gauge transport, nonempty edge carriers, literal coarse-path/fine-word
    equality, derived ambient-holonomy coherence, surjectivity, strict three-stage composition,
    genuine eligible-observable/ambient-physical-observable coherence between the two existing laws,
    exact selected weighted-measure pushforward, derived pullback integrals and finite word-family
    equality in law, and transitive source-facing pushforward on the unchanged density-semigroup chain.
  - [x] Add the first exact Driver Definition 8.1 component: positive-spacing paths in the directed
    nearest-neighbor graph on `εℤ²`, with finite strictly ordered nodes and exact affine bond
    geometry; reject diagonal, stationary, zero-spacing, and singleton-node surrogates.
  - [x] Add the uninhabited Definition 8.1 approximating graph family on the project's conservative
    embedded-arc strengthening, with explicit subdivision debt for Driver-permitted loop incidence:
    one embedded graph at
    every positive spacing, surjective edge/face maps, exact lattice paths on every fine edge,
    uniform explicit symmetric-difference area `O(ε)`, and universal exact boundary-choice/word
    transport.
  - [x] Identify Driver's Villain single-plaquette action with the smooth strictly-positive real
    representative of the unchanged selected convolution-semigroup density at `ε²`; require the
    exact Definition 4.7 `∂ₜQ = 1/2 ΔQ` chain, an initial-identity generated operator semigroup, and
    Driver's displayed convolution-kernel formula; derive the full inherited action contract,
    including real Haar-integral normalization, plus normalized/nonzero canonical Haar-density
    plaquette measures.
  - [x] Package Driver Definition 7.1 as one common action contract with exact Villain/Wilson
    adapters and an independent constant-one nonvacuity inhabitant.
  - [x] Add Driver's Wilson action from the actual trace character of a nonzero finite-dimensional
    unitary matrix representation, with exact positive Haar-integral normalizers and the full
    inherited continuous/positive/class/inversion/real-normalization action contract.
  - [x] Add the exact infinite directed `εℤ²` bond/configuration carrier and Driver axial tree, with
    exact physical `(εm, εn)` embedding and signed `ε` steps, reverse-bond inversion, measurable
    coordinates, exact tree freezing, identity inhabitants, and a nonidentity off-axis axial
    configuration proving the carrier is not subsingleton.
  - [x] Add exact physically scaled elementary plaquettes, closed counterclockwise boundary
    holonomy in Driver order, and measurable/nonzero finite products of one common action.
  - [x] Add generic finite axial presentations with orientation-disjoint off-tree coordinates,
    measurable finite-support extension, actual plaquettes with complete non-tree boundary-coordinate
    coverage, exact partition functions, and derived
    normalized/nonzero finite product-Haar density measures, their exact finite-support pushforwards
    to the infinite axial carrier, and represented-coordinate marginal identities.
  - [x] Add an exhaustive nested projective finite-presentation contract and a separate exact
    infinite axial probability/cylinder-law interface with finite-stage and one-coordinate marginals.
  - [x] Construct the finite projective sequence from exact radii `stage+1`, exhaustive off-tree
    bond/plaquette coverage, and derived consecutive box projectivity.
  - [x] Construct measurable noncommutative infinite axial recovery from arbitrary plaquette values,
    with exact finite-box coherence and pointwise recovery of every plaquette holonomy.
  - [x] Construct the iid infinite plaquette-action product measure and push it through axial
    recovery; prove all exact-box coordinate marginals and inhabit the infinite cylinder-law record.
    Keep this separate from boundary-conditioned Driver Theorem 7.2 and continuum convergence.
  - [x] Add exact positive-radius centered square-box plaquette and off-axis axial-coordinate sets,
    prove literal radius nesting and complete non-tree plaquette-boundary coverage.
  - [x] Construct the exact square-box adapter to generic finite axial presentations, including a
    measurable reverse/identity extension, coordinate recovery, orientation disjointness, finite
    support, and inherited boundary coverage.
  - [x] Prove exact box partition functions finite and nonzero from compact action bounds, strict
    positivity and product-Haar normalization; construct normalized finite-coordinate and infinite-
    carrier pushforward box measures.
  - [x] Construct exact successor-radius coordinate/plaquette inclusions and measurable restriction;
    state the uninhabited exact consecutive-box measure-pushforward obligation.
  - [x] Define Driver's exact `Aₙ`, `Aₙ₋₁`, `Bₙ`, `B̄ₙ`, and frozen `Bₙᶜ` geometry; prove
    `Bₙ ⊆ B̄ₙ` and hostilely distinguish the two bond sets.
  - [x] Construct exact finite axial `Bₙ` coordinates and a measurable boundary extension retaining
    arbitrary axial boundary data exactly on `Bₙᶜ`.
  - [x] Define `J(Bₙ)` by literal boundary incidence and prove it exactly equals the complete
    `2n × 2n` box plaquette set.
  - [x] Construct the exact (7.2) `J(Bₙ)` action density, finite/nonzero boundary-dependent
    normalizer, normalized finite-coordinate law, and boundary-retaining infinite-carrier pushforward.
  - [x] Add genuinely-finite convergence over measurable bounded-continuous tests, natural axial
    product topology, closed/compact exact carriers, countable-product Borel identification, derived
    all-continuous-test coverage, and an uninhabited full
    Theorem 7.2 axial contract requiring common boundary-independent weak limit
    plus exact free finite-volume expectations on every eligible `Bₙ` observable.
  - [x] Define the exact `ε → 0⁺` filter and spacing-indexed action families retaining the unchanged
    Villain `Q_{ε²}` chain or one fixed Wilson trace representation; make Wilson faithfulness actual
    representation injectivity.
  - [x] Strengthen each Definition 8.1 fine edge with an exact nonempty directed-bond word tied to
    every consecutive certified path node; construct measurable fine/coarse holonomy restriction.
  - [x] Add Driver's standing smooth representation derivative `p_*`, its exact injectivity, and
    coherence of the continuum invariant pairing with `-Re tr(p_*X p_*Y)` using genuine contracted
    matrix multiplication; derive conjugate-transpose skewness, trace reality, pairing symmetry, exact complex-trace recovery,
    the squared-entry norm formula, and strict positivity from unitarity and differential injectivity.
  - [x] Tie one connected-group smooth globally faithful and infinitesimally injective representation
    to the Wilson normalization/actions, exact trace pairing, pairing Laplacian, unchanged selected
    continuum heat density, and kernel.
  - [x] Add Driver's exact `B → VB` enlargement: BC certificates on both graphs, literal coarse-path
    subdivision, exact vertical/x-axis tree, total enlarged-edge coverage, measurable restriction,
    and ambient holonomy compatibility.
  - [x] State Driver equation (6.1) on `VB` for every bounded measurable coarse function through exact
    restriction, canonical BC words, and normalized vertical/x-axis-tree-frozen area-density measure.
  - [ ] Adjudicate Driver Definition 8.4's visibly spacing-independent printed Wilson weight against
    Theorem 8.8/(8.2) and Borgs–Seiler Appendix A; do not accept a Wilson central-limit interface until
    the missing `ε`-dependence is authoritatively resolved.
  - [x] Add the exact collision-safe `B(ε) → VB(ε)` graph/holonomy bridge, including commuting
    refinement words, exact `T(ε)`, total fine-edge coverage, slit-aware finite polyomino faces,
    positive integer convolution exponents, and derived mapped-area convergence/eventual face-product
    reindexing.
  - [x] State the universal enlarged measure/product identity from the first §8 proof equality, with
    exact BC words, `T(ε)`-frozen product Haar, and positive convolution powers.
  - [x] Derive the exact Villain convolution-semigroup reduction from `Q_{ε²}` to `Q_{|R(ε)|}` for
    every fine face and the whole certified BC product.
  - [x] Add the exact differential-induced Villain common heat chain without Wilson/global-faithful
    overstrength, and the uninhabited connected compact Lie-group Theorem 8.5 convergence contract.
  - [x] Visually adjudicate Lévy Chapter 5, Theorem 5.1.1, equation (5.1), and the nonabelian
    sigma-field warning; add reusable dependent-observation generated-measurable-space mathematics.
  - [x] Add the exact simultaneous-conjugacy quotient for indexed holonomy families, its genuine
    quotient topology/final measurable space, finite-family compactness/Hausdorffness/second
    countability, compatible Polish/standard-Borel structure, and exact positive-arity
    finite holonomy observations/generated sigma field over
    one fixed-base loop carrier, mixed-basepoint separation, exact continuous/measurable involutive
    class inversion for boundary reversal, and hostile coordinatewise/empty-family probes.
  - [x] Add reusable genuine joint conditional-kernel disintegration with zero mass outside every
    exact boundary fiber, involutive reversal, all-value product restrictions, and derived bind/
    marginal laws.
  - [x] Add the intrinsic compact connected oriented measured surface nucleus with exact manifold
    dimension, nowhere-zero smooth top form, positive smooth chart densities, and compact exact
    boundary-component carrier.
  - [x] Add finite smooth embedded unit-circle presentations whose exact disjoint ranges cover every
    actual boundary component, while retaining closed surfaces.
  - [x] Add preferred-chart-certified two-sided outward directions and induced boundary orientation
    from the exact surface top form, with smooth/nonzero frame data and zero-vector hostile probes.
  - [x] Characterize exact straight outward rays in the Euclidean half-space by strict negativity
    of the zeroth tangent coordinate, derive boundary-coordinate vanishing from Mathlib's frontier
    definition, and apply the sign theorem to every exact presented boundary-circle field.
  - [x] Prove the derivative-level linear transport endpoint: tangent-hyperplane preservation gives
    an exact normal-coordinate multiplier formula; nonnegative normal transport plus surjectivity
    forces strict positivity; and positive-normal continuous linear equivalences preserve and
    reflect the full two-sided outward-ray predicate.
  - [x] Prove the nonlinear tangent-cone step: a locally half-space-valued within derivative at a
    boundary image maps bidirectional tangent-cone vectors into the boundary hyperplane and has
    nonnegative normal coordinate on every one-sided inward cone vector.
  - [x] Derive those exact source-cone memberships for every relative neighborhood of a half-space
    boundary point: boundary tangents occur in both directions and the inward normal occurs
    one-sidedly, yielding automatic tangent preservation and normal nonnegativity.
  - [x] Instantiate the cone, local-half-space, smoothness, and derivative-surjectivity results on
    Mathlib's actual extended coordinate change, proving its exact within derivative preserves the
    boundary tangent hyperplane, has strictly positive normal multiplier, and transports outward rays.
  - [x] Prove the exact chart tangent chain rule: the direct `mfderiv` coordinate in the second
    overlapping atlas chart equals the transition derivative within its exact source applied to the
    first chart's direct `mfderiv` coordinate.
  - [x] Add positive-arity distinct-component boundary identifications by genuine circle
    diffeomorphisms with exact derivative-level orientation reversal and hostile vacuity probes.
  - [x] Construct the minimal equivalence-closure quotient of the disjoint union by exact paired
    boundary points, with genuine quotient topology, side maps, and compatible-function universal
    lift.
  - [x] Add dependent base-point-partitioned positive finite holonomy observations, so separate bases
    receive separate common conjugators rather than a source-false mixed-base quotient.
  - [x] Add the uninhabited Lévy Theorem 5.1.1 core sewing record with exact `(G/Ad)^p` seam
    conditioning, geometric basepoint-index/trace coherence, exact side/sewn seam traces,
    restriction holonomy and inverse side-seam conjugacy-class coherence, genuine disintegration, componentwise inverse boundary classes, and all-value product/marginal laws without asserting side-field generation.
  - [x] Add Theorem 5.1.1's final further-conditioning clause with arbitrary finite collections of
    distinct fixed-base blocks on both sides (including zero), the same sewn whole law/restriction,
    genuine enlarged disintegration, irrelevant-other-side kernel factorization, and exact
    inverse-boundary product law.
  - [x] Derive every compact surface's intrinsic boundary to be null from arbitrary-chart
    model-frontier membership, convex-range Haar nullity, exact chart-density transport, and a finite
    compact-boundary chart cover.
  - [x] Construct the canonical glued area measure as the exact sum of both side pushforwards and
    derive its exact total area, finiteness, strict positivity, and nonzeroness.
  - [x] Construct the exact compact measurable seam and derive its zero canonical area from
    same-side injectivity, exact cross-side matching, and null side-boundary preimages.
  - [x] Prove both side inclusions are measurable embeddings and that every measurable side subset
    retains exactly its original measure on its embedded quotient image; the opposite pushforward
    contributes only through a null boundary preimage. Derive whole-side total-area recovery.
  - [x] Construct compact selected-boundary unions and the exact Borel remaining-boundary quotient
    candidate; derive its canonical nullity and make smooth descent identify its manifold boundary
    with this named candidate.
  - [x] Identify the circle-range seam exactly with both selected-boundary quotient images, retain
    the right-side circle diffeomorphism, prove disjointness from the remaining-boundary candidate,
    and derive their exact decomposition of both original full-boundary images before descent.
  - [x] Connect Lévy's designated sewn seam-loop traces and dependent seam bases to the exact seam
    set, deriving exclusion from the retained-boundary candidate without smooth descent.
  - [x] Derive exact left seam-inclusion coherence: geometric basepoint injectivity identifies the
    included and designated sewn base labels, and their loop traces agree pointwise without the
    right side's orientation-reversing reparameterization.
  - [x] Prove both included side seam traces lie in the exact seam; use the inverse designated circle
    diffeomorphism for arbitrary right parameters while keeping its mixed-basepoint label separate.
  - [x] Identify the right included base's represented point exactly as both the selected-right
    parameter-`1` point and the sewn seam trace at the inverse-diffeomorphism image of `1`.
  - [x] Add an uninhabited exact smooth/oriented/measured descent contract on the same quotient
    topology, including smooth side embeddings, positive-scale orientation-class pullbacks, derived
    null side boundaries, identification with the canonical glued area, exact remaining boundary,
    and interior seam placement.
  - [x] Derive exact relation closedness, closed projection/saturations, compact equivalence-class
    separation, Hausdorffness, an explicit countable quotient basis, second countability,
    Polish/standard-Borel structure, compactness, connectedness, and closed side embeddings for the
    glued quotient.
  - [x] Prove Euclidean-half-space chart independence of the outward predicate for every eligible
    overlapping atlas chart at every actual manifold boundary point.
  - [ ] Inhabit/derive the smooth/oriented/measured descent witnesses for the glued quotient.
  - [x] Derive exact consecutive square-box projectivity from noncommutative rooted plaquette
    coordinates, product-Haar preservation, action-density factorization, and the literal
    restriction commuting square.
  - [ ] Resolve/formalize Theorem 8.10 and inhabit/derive Theorem 7.2. Keep
    compact-surface gluing distinct from finite-cutoff, classical, and four-dimensional witnesses.
  - [ ] Assemble a final source-indexed 2D acceptance proposition joining the constructed finite
    lattice, heat/Brownian, weak-limit continuum, compact-surface, and sewing chains; attempt to
    inhabit it solely from formalized Driver/Lévy/Sengupta results and record every remaining
    supplied field as a concrete literature or infrastructure debt.
  - [ ] Add hostile separation proving that even an inhabited final 2D proposition cannot inhabit,
    imply, or be coerced into the 4D Clay acceptance proposition.
- [ ] Add a nontrivial but uninhabited `d = 3` continuum acceptance contract.
  - [x] Add a current-strength continuum core hard-wired to coordinate `ℝ³` with coordinate
    Lebesgue action measure, dependently joining compact-simple gauge/classical data, strict
    Euclidean and Wightman chains, strict Wick coherence, one coherent covariant local family,
    exact `F²` interpretation, a same-PVM stress-charge/translation Ward bridge, and a same-PVM
    physical gap.
  - [x] Replace the arbitrary metric index by Mathlib's canonical flat inner-product metric on
    coordinate `ℝ³`; retain coordinate Lebesgue action measure exactly.
  - [ ] Prove the general metric-induced volume bridge to the committed coordinate Lebesgue measure;
    replace current strict Euclidean/reconstruction and Poincaré pre-cover surfaces with corrected
    source-facing OS-II/OS-I reconstruction and genuine covering interfaces before calling the
    three-dimensional contract complete.
- [ ] Add the full `d = 4` Clay acceptance contract.
  - [x] Add an uninhabited current-strength core on canonical coordinate `ℝ⁴`, joining the exact
    classical/action, carrier-exact OS-II `(E0′)` and source-carrier OS-I `(E1)`–`(E4)`, exact-source
    Wick coherence, Wightman `(R0′)`/same-PVM gap, the coherent finite scalar fragment `1`, `F²`, `(F²)²`,
    stress/translation Ward, compact-simple-indexed running coupling, exact weak OPE, corrected
    same-lift reconstruction acceptance, and supplied same-coupling regular-variation surfaces, with
    a required nonzero interpreted `F² × F²`
    zeroth-order term with nonzero same-running-coupling exponent and nonzero leading scaling
    distribution.
  - [x] Tie the same running coupling's one-loop coefficient to an explicit pairing-orthonormal
    basis, the exact tangent bracket, Gross–Wilczek's adjoint-Casimir identity, and
    `11 C₂(G)/(3·16π²)`; identify the exact classical outer coupling with that same running coupling
    at an explicit UV reference scale. This remains supplied convention/normalization data, not a
    connection-level field-rescaling theorem or perturbative calculation.
  - [x] Ingest and audit the supplied Hall/Bargmann/Hall–Wightman, Hodge/volume, composite-operator,
    BRST/EOM mixing, power-counting, and perturbative OPE source chain.
  - [x] Add a preliminary, explicitly `CurrentStrength` universal target quantifying over every
    caller-supplied exact compact-simple gauge certificate while existentially packaging all
    construction-specific bundle, connection, Poincare, Hilbert, field, and unchanged core carriers.
    Derive conditionally that any inhabitant would provide every exact input a witness with positive
    finite same-spectrum gap and an explicit nonzero/non-unit field. No inhabitance theorem is
    supplied, and this is not the final Clay proposition.
  - [ ] Extend the constructed homogeneous `SL(2,ℂ)` carrier and central scalar-sign embedding to the
    concrete inhomogeneous cover, identify its projection kernel with the accepted literal signs,
    and construct the named affine-target group law; add the now
    source-ready curvature/covariant-derivative grammar, BRST/EOM operator mixing, calculated
    perturbative remainders and scheme dependence, and upgrade the preliminary universal target to
    the final source-complete contract. The physical-reduced trace anomaly is present; unrestricted
    mixing-complete trace semantics remain part of the operator-mixing debt.
- [x] Define the exact Clay endpoint predicate, reject every lower dimension `1`–`3`, and prove no
  lower-dimensional Euclidean coordinate carrier (especially the 3D core base) is real-linearly
  equivalent to the four-dimensional carrier.
- [ ] Once the final four-dimensional acceptance proposition exists, prove that no lower-dimensional
  witness can inhabit it; the current index/rank lemmas are supporting evidence only.
- [x] Establish `docs/COMPLETION_AUDIT.md` as a pre-audit-snapshot-anchored prompt-to-artifact checklist
  with explicit verifier limits, dimension/bridge matrices, publication state, and open blockers.
- [ ] Repeat and close every completion-audit row at the final commit.
- [ ] Publish the final acceptance proposition without asserting an inhabitant.

## Per-commit gates

```bash
lake env lean <changed-module>
lake build
python3 scripts/verify_sources.py
python3 scripts/verify_audit_bibliography.py
python3 scripts/audit_lean.py
git diff --check
git status --short
```

A phase is complete only when its source map, definitions, derived theorems, bridges, hostile
probes, build evidence and axiom audit are all present.
