# Yang–Mills Definition in Lean

This repository builds a source-traceable, machine-checked definition of **what a Yang–Mills theory
must satisfy**. It does not construct Yang–Mills theory, prove its existence, prove a mass gap, or
claim a solution to the Clay problem.

## Governing decision

The formalization is built from the ground up. The former `LeanMillenniumPrizeProblems`
implementation is not a dependency and its API is not preserved. The legacy Adaly
`ClayStatement` and hostile probes are archaeological input: useful ideas may be integrated only
after independent validation against primary literature.

**Papers are authoritative. Legacy is the quarry, not the cathedral.**

## Acceptance target

The pinned Clay/Jaffe–Witten source states on PDF p. 6, §4:

> Prove that for any compact simple gauge group G, a non-trivial quantum Yang–Mills theory exists
> on R4 and has a mass gap Δ > 0.

This headline is not the complete contract. The same section also requires gauge-invariant local
curvature fields, short-distance agreement with asymptotic freedom and perturbative
renormalization, a stress tensor, an operator-product expansion with prescribed singularities,
finite supremal mass, and axiomatic strength at least matching the cited Wightman and
Osterwalder–Schrader sources. This project formalizes the full contract a future construction would
have to inhabit. The final target will be a proposition, not a falsely inhabited theorem.

## Construction order

1. Euclidean dimensions and signatures;
2. compact-simple Lie-group semantics;
3. manifolds, principal bundles, gauge transformations, connections and curvature;
4. classical action and interpreted gauge-invariant observables;
5. Euclidean continuum and Osterwalder–Schrader data;
6. Minkowski/Wightman data and physical Poincaré symmetry;
7. joint translation spectral/PVM and mass-gap semantics;
8. explicit reconstruction and coherence bridges;
9. optional lattice-regulator and continuum-limit interfaces;
10. distinct contracts and consistency probes for Euclidean dimensions 1–4;
11. the four-dimensional Clay acceptance proposition.

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md), the goal sequence in
[`docs/ROADMAP.md`](docs/ROADMAP.md), the declaration-level
[`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md), the DOI-verified past/future audit inventory in
[`docs/AUDIT_BIBLIOGRAPHY.md`](docs/AUDIT_BIBLIOGRAPHY.md), the living prompt-to-artifact
[`docs/COMPLETION_AUDIT.md`](docs/COMPLETION_AUDIT.md), and the evidence-only current state in
[`docs/STATUS.md`](docs/STATUS.md).

## Formalization laws

- New Lean source contains no `sorry` and introduces no project axioms.
- Every physical requirement has declaration-level provenance.
- Definitions, witness requirements, derived results, bridges and open specification debt remain
  visibly distinct.
- Euclidean dimension `d` means spacetime dimension; under OS reconstruction it corresponds to
  `(d - 1) + 1` Minkowski spacetime.
- Lower-dimensional theories test shared interfaces but never imply the 4D contract without an
  explicit theorem carrying every required hypothesis.
- Lattice models are regulators/construction interfaces, not silently continuum theories.
- Lean type correctness is necessary but does not establish physical adequacy.
- Every major interface receives positive consistency evidence where available and hostile probes
  against vacuous witnesses.

## Reproducible setup

Requirements: Git, `curl`, and `elan`. The project pins its Lean and Mathlib revisions.

```bash
lake build
python3 scripts/verify_sources.py
python3 scripts/verify_audit_bibliography.py
```

Source-byte and audit-bibliography verification are independent of Lean compilation. All gates are
required; the bibliography verifier is offline by default and accepts `--online` only for an
explicit Crossref refresh.

## Repository layout

```text
YangMills/            Lean source
Sources/              pinned primary/authoritative source artifacts
scripts/              provenance and audit tools
docs/                 architecture, decisions and source maps
YangMills.lean        library root
lean-toolchain        pinned Lean release
lakefile.toml         pinned dependencies
```

## Current status

The standalone foundation, Euclidean dimension index, separate Euclidean/Minkowski quadratic
forms, source-facing Lie-algebra simplicity layer, and compact-connected-simple Lie-group
certificate type and semantics, the fiberwise torsor core, algebraic bundle maps/gauge
automorphisms, topological and smooth equivariant local trivializations, derived open-quotient
projection and smooth overlap-transition theorems, smooth gauge automorphisms, the Lie-group adjoint
action, a typed pointwise manifold differential-form carrier, local-model exterior derivative,
an arbitrary-manifold one-form Cartan certificate, and supplied positive-degree Cartan certificates
with exact normed-space compatibility and a `2 → 3` specialization, alongside smoothly closed
Lie-bracket wedges,
finite-dimensional tangent-bracket continuity/smoothness bridges, smooth differential-form
regularity, pointwise and smooth principal connection-form definitions, the derived smooth gauge-
automorphism pullback of connections with exact identity and contravariant composition laws, the
derived principal curvature formula, intrinsic curvature horizontality/right-adjoint-equivariance certificate semantics,
the adjoint associated-bundle orbit quotient with its quotient topology, base projection, and
representative-independent local coordinates, topological local trivializations backed by derived
adjoint regularity, their exact promotion to Mathlib's generic bundle-trivialization interface, and
derived fiberwise-linear overlap formulas with smooth forward/inverse operator families and exact
source coherence, a named covering quotient chart atlas with explicit tangent-model transport and
proved smooth fiberwise-linear groupoid/manifold compatibility, a base-preserving dependent-fiber
carrier equivalence with an explicitly topology-coherent total-space homeomorphism and named real
vector-space structures on every dependent fiber with every designated associated coordinate proved
linear, quotient trivializations transported exactly to the dependent total space, and that
presentation packaged as named topology-coherent Mathlib `FiberBundle` and `VectorBundle` values
with a named `C∞` vector-bundle mixin, an exact smooth-section interface, smooth form evaluation
along maps under explicit ambient extensions, pointwise and smooth adjoint-bundle-valued
differential-form carriers, an exact degree-zero form/section bridge, and
smooth principal local sections with projection-right-inverse tangent lifts that preserve smooth
base fields and admit exact chart-local ambient extensions supporting smooth principal-form
evaluation, and proved lift and representative independence plus smooth dependent-fiber descent for smooth horizontal
right-equivariant principal two-forms and smooth descent for the exact certified principal
curvature, and the adjoint
action packaged as a
smooth invertible operator family, alongside an explicit positive
adjoint-invariant Lie-algebra inner-product certificate inducing a chart-independent positive
pairing on every actual adjoint quotient fiber and packaging that exact pairing as a bilinear map,
a reusable canonical-tensor theorem proving
basis independence of bilinear quadratic contraction without installing a codomain inner-product
instance, an exact degree-two alternating-map-to-bilinear adapter, and a named smooth Euclidean
metric interface whose pointwise contraction of exact smoothly descended curvature is constructed
canonically, proved equal to every orthonormal-basis sum, proved nonnegative, and proved to scale
exactly under positive rescaling of the named invariant pairing, together with an integrable
real-valued Euclidean action proved to integrate that canonical scalar relative to an
explicitly designated Borel measure and positive coupling (without claiming a general Hodge-star
theorem or metric volume), are implemented. Scalar positive-arity tempered Schwinger distributions,
normalized zero-point data, and a concrete fixed-order factorial-growth estimate over Mathlib
Schwartz seminorms are also implemented as preliminary regularity infrastructure and remain distinct
from OS-II's printed norm. A carrier-exact `(E0′)` surface now characterizes equation (2.1)'s
flattened-coordinate weighted multi-index control by its exact least-upper-bound property and
imposes equation (4.1) on complex-linear functionals over the coincidence-flat `𝒮₀` submodules with
one positive order and factorial-growth sequence. A separate ambient-tempered-extension interface
restricts canonically to this source carrier; no converse extension, control, or family is constructed. Exact positive-arity Schwartz permutation pullback and scalar
Schwinger symmetry `(E3)` are implemented separately. Proper-Euclidean rigid motions, their exact
Schwartz pullback, and scalar covariance `(E1)` are also implemented. Exact first-coordinate time
reflection and strict-positive-time topological-support infrastructure are present, together with
an explicit nonzero compactly supported arity-one positive-time Schwartz test. A concrete strict
subspace also records topological-support time ordering and full Fréchet-derivative flatness on
coincidence diagonals. A broader project-dimension Fréchet candidate now requires every derivative
to vanish outside strict positive time order, is packaged as an exact complex Schwartz submodule,
uses the exact induced per-arity Schwartz topology,
contains the strict-support carrier, and has an explicit nonzero arity-one test. An exact
point/coordinate Kronecker basis now proves that full Fréchet-map vanishing is equivalent to
vanishing on every ordered basis-direction tuple, with nonzero derivatives detected by a tuple.
Each coordinate jet is now an exact continuous complex-linear Schwartz functional; their kernel
intersection proves the dimension-generic candidate closed and its forgetful map a closed embedding.
Separately, the standard Schwartz seminorm family is proved point-separating, supplying named
`T1Space` and Hausdorff structures without a project axiom.
Exact four-dimensional point/coordinate labels are now flattened point-major as `μ + 4i`;
natural-valued multi-indices have an exact occurrence enumeration with each coordinate repeated by
its multiplicity, and Fréchet-candidate membership implies all resulting canonical derivatives
vanish. Every arbitrary ordered coordinate tuple now induces exact fiber-cardinality multiplicities
and an occurrence enumeration that recovers the tuple entrywise; quantifying over all enumerations
is proved equivalent to the Fréchet/coordinate-jet candidate. Iterated Schwartz directional
operators are now proved permutation-invariant from exact second-derivative commutation and
permutation-invariant list folds, so every occurrence enumeration equals the canonical derivative
and the canonical multi-index predicate is equivalent to the Fréchet candidate. The canonical
repeated-coordinate derivative is now named as the formal interpretation of OS-I's four-dimensional
`D^α`; exact positive-arity source membership is defined, proved equivalent to the Fréchet
presentation, proved closed with the induced Schwartz topology, and supplied a nonzero arity-one
test. Each source space is now algebraically equivalent to the exact complex Schwartz submodule,
with named additive-group and complex-module structures whose operations preserve the underlying
Schwartz functions exactly; addition, negation and complex scalar multiplication are proved
continuous for the induced topology through named topological-algebra structures. The exact
forgetful map is also packaged as a real-linear inducing map, transporting named real local
convexity from ambient Schwartz space at every positive arity. OS-I's separate scalar zero-point sequence component is not folded into this subtype. An
exact four-dimensional algebraic source-sequence carrier now combines that scalar with finitely
many exact positive-arity components and exact nonzero support; the earlier strict sequence maps
componentwise without changing its scalar, support or Schwartz components and without a properness
claim, and explicit scalar-unit and nonzero-
bump source sequences prevent collapse. Exact products over every finite positive-arity stage now
include the separate scalar, filter support by actual nonvanishing, recover every source sequence,
and generate a named finite-stage final topology with its exact universal property. Exact source
sequences are also algebraically equivalent to the separate scalar times a dependent finitely
supported source-space family, with named additive-group and complex-module structures and exact
scalar/component laws. Every generating finite-stage extension is now proved complex-linear and
packaged as a continuous complex-linear map into the named final topology. Every finite stage has
named topological additive-group, continuous complex scalar, and real locally convex structures,
including the independent scalar at the empty positive stage. The topology is also
proved to be the quotient of the disjoint union of all finite stages. Local compactness of `ℂ`
yields joint complex scalar continuity; negation, finite-union stage addition, and addition in each
sequence variable separately are continuous. Joint addition on this raw topology remains conditional
on the unproved product-quotient property. Separately, an `sInf` construction now gives the finest
stage-continuous real-locally-convex topological complex-module topology, with joint addition/scalar
operations, local convexity and continuous-linear stage maps. The raw topology lies below this
locally convex final topology in Mathlib's reversed order, and equality is proved equivalent to raw
admissibility rather than asserted. An exact scalar/all-positive-arity coordinate map into a
Hausdorff product is proved continuous and injective, so the locally convex final topology itself is
Hausdorff. A complex-linear map from this topology into any real-locally-convex topological complex
module is now proved continuous exactly when all finite-stage composites are continuous. OS-I's
separate scalar and positive-arity natural injections are constructed, every stage is their exact
finite sum, and the paper's coordinatewise continuity criterion is proved. The Hausdorff locally
convex final topology is therefore selected as the source-facing locally convex direct-sum topology,
with named topological additive-group, complex scalar, real local-convexity and Hausdorff structures
and continuously linear scalar/source injections. The raw topological final topology remains a
separately named auxiliary topology and equality is not asserted or required for this selection. A
reusable continuous Schwartz point-evaluation map supplies closed kernels and exact pointwise
separation. It proves OS-I's negative-half-line Schwartz submodule closed; the genuine quotient
`𝒮(ℝ₊)` is a Hausdorff real-locally-convex topological complex module and contains an explicit
nonzero positive bump class. An uninhabited
completed-projective-tensor
interface requires Hausdorff locally convex factors and an additive-uniform complete carrier, jointly continuous noncollapsing pure
tensors, dense pure span, and continuous-linear extension into same-universe complete targets;
uniqueness is derived from density, but this stronger arbitrary-target interface remains separate
from source-facing use pending authoritative sourcing. The neutral spatial `ℝ³` selected by
four-dimensional spacetime and source-facing scalar-functional tensor candidate data for the
factors `𝒮(ℝ₊)` and `𝒮(ℝ³)` are defined; explicit nonzero tests force a nonzero pure tensor in every
supplied candidate. A zero-based fixed-left-associated family records analogous scalar-functional
candidates at every intended finite positive power, with density-derived uniqueness and recursive
noncollapse. These data do not characterize the completed projective tensor topology. Proper
enlargement and sufficiency/density/completion comparisons with the earlier strict-support subspace,
completeness and the Fréchet presentation of the half-line quotient, actual completed-tensor
carriers and topology, nuclearity, and OS-II-strength reconstruction remain open. Exact source-carrier `(E2)` is now stated on finite derivative-vanishing source sequences via the
unrestricted reflected-star convolution. Completed positive-half-space tensors, nuclearity, and
OS-II-strength reconstruction remain separate open obligations rather than prerequisites for this
algebraic positivity condition. The algebraic finite-sequence carrier
and product are implemented with exact positive and natural-arity support, with its scalar zero-point component represented faithfully as a
zero-arity Schwartz test. Exact configuration split/merge and the raw pointwise tensor kernel are
also implemented. A reusable generic tensor product is proved Schwartz with explicit decay bounds and
algebraic bilinearity, then pulled through the exact Euclidean configuration split with exact raw-
kernel agreement. The finite convolution component is defined at every natural arity, including both
zero-arity endpoints. An unrestricted finite Schwartz-sequence carrier is separate from the strict
positive-time domain, with an exact forgetful map. Finite-support closure is proved and the
convolution is packaged in that unrestricted carrier. A named finite-stage final topology and its
exact stagewise universal property are implemented without a global instance. Named additive-group
and complex-module structures are transported from dependent finite support and likewise require
local installation. Every generating finite-stage map and every exact natural coordinate injection
is bundled as a continuous complex-linear map. The exact linear coordinate-injection continuity
criterion is proved for the preliminary finite-stage final topology; joint sequence addition/scalar
continuity, source-space and locally convex direct-sum identification with OS-I, and convolution
continuity remain pending. Exact reverse-conjugation on scalar Schwartz components is implemented
and kept distinct from Euclidean time reflection. Both operations are lifted to exact finite
sequences and combined in the source order `Θ f*`. The exact algebraic Schwinger evaluation and
nonnegative-real form are defined both on the current strict Mathlib subdomain and on the exact
four-dimensional derivative-vanishing source carrier. Source positivity implies strict positivity
through an exact componentwise bridge; the converse is not claimed. Exact simultaneous
Euclidean translations and their finite-sequence lift are available as algebraic clustering
infrastructure. Normalized spatial rays are constructed in dimensions with a spatial coordinate,
the four-dimensional ray escapes to infinity, and dimension one is proved to have no such direction.
The exact connected factorization expression and zero-limit predicate are defined on both the strict
Mathlib subdomain and every pair of exact four-dimensional source sequences. Source `(E4)` quantifies
over every normalized nonzero spatial direction and implies each strict-direction predicate exactly;
the converse is not claimed. Growth, `(E1)`, `(E3)`, strict positivity, and clustering are
assembled around one normalized family and direction in a non-source-facing candidate record; no
inhabitant is constructed. Independently, proper-orthochronous Lorentz and affine Poincaré
kinematics are now defined for the mostly-minus Minkowski form, with properness, time orientation,
and nontrivial translation probes. A topological-group lift/pre-cover interface and one strongly
continuous unitary representation on a separable Hilbert carrier are packaged without inhabitants;
physical translations are derived from that same representation. The exact affine target now has
its induced Lorentz-action/translation coordinate topology, and a separate uninhabited strengthening
requires the projection to be a genuine Mathlib covering map with local-homeomorphism, open,
quotient, and discrete-fiber consequences. A further uninhabited strengthening makes every exact
fiber equivalent to `Fin 2` and derives two distinct lifts. A named target topological-group law is
also required to have the exact affine identity and action-composition multiplication; the double-
cover projection is thereby a bundled group homomorphism. Its exact identity fiber already has two
sheets, so the group kernel is now proved multiplicatively equivalent to the literal complex-unit
subgroup `{1,-1}` and central, deriving a nonidentity negative-sign lift without another requirement. Relative to any selected lift, its fiber
is proved to consist exactly of that lift and its distinct negative partner. This does not construct
a canonical global section or matrix-label the sheets. For any cyclic scalar Wightman realization
directly indexed by the exact cover, scalar covariance, exact vacuum invariance, and cyclicity now
prove that every
kernel element—and in particular the negative sign—acts as the identity on the full Hilbert space.
A bundled dependent-chain transport now carries this theorem across the 4D core's exact
cover-to-lift equality, so it applies to the core's existing representation rather than a copied one.
Lift-independence then constructs a choice-independent unitary homomorphism on the exact named affine
Poincaré target; its strong continuity is descended through the genuine cover's quotient-map law.
Explicit coherence recovers every original cover unitary and the exact translation unitaries already
tied to the joint PVM, stress tensor, and gap. On the exact cover-indexed scalar chain, the common
domain unitary, scalar field/adjoint covariance, and covariance of every explicitly designated
scalar label in any covariant local-observable family on that same domain are now stated directly on
affine kinematics with no lift choice exposed. Lift-equality transport applies these statements to
the 4D core's exact original domain, scalar field, and scalar sector of its observable family rather
than cast copies; stress-tensor component labels retain their separate rank-two law.
Constructing the target law from future-cone closure and concrete inhomogeneous `SL(2,ℂ)` remains
pending. A normalized vacuum is
now tied to that same representation, with the complete invariant subspace required to be its single
complex line. One dense common submodule contains that vacuum and is invariant under the same
representation, whose unitaries restrict exactly to it. A scalar field and adjoint preserve that
same domain, with coherent tempered matrix elements and the conjugated-test adjoint relation. The
exact inverse-affine test pullback and covariance of both field and adjoint under the same restricted
physical unitaries are packaged. Finite field/adjoint words on the exact vacuum are defined and
cyclicity requires their Hilbert-space span to be dense. Scalar bosonic locality is defined for
field/adjoint pairs with spacelike-separated topological supports; explicit nonzero test pairs exist
from dimension two onward, while dimension one has no spacelike point pair. One normalized,
strongly countably-additive joint momentum PVM is tied to the exact physical translations by the
SNAG diagonal Fourier formula and has forward-cone support. A separate physical
invariant-mass-gap predicate adds the exact vacuum-line projection; its same-PVM Hamiltonian view
kills `(0, Δ)` and requires a bounded positive-energy nonvacuum excitation. The Clay mass is the
supremum of the source-facing positive thresholds whose same-PVM Hamiltonian projection vanishes
on `(0, Δ)` and whose zero projection is the vacuum line. Any one stronger physical joint gap
supplies a bounded excitation that makes this set nonempty and bounded above with positive
supremum, but no threshold or theory is constructed. Covariance,
cyclicity, locality, and forward-cone spectrum are integrated on one exact scalar
field/domain/vacuum/representation chain, while the mass gap remains an additional predicate.
A prerequisite local-observable family now puts every labeled smeared operator and tempered matrix
element on the same common domain, fixes the unit field by Lebesgue smearing, and requires full
bilocal tempered products with exact pure-tensor operator order and nonzero witnesses. The same family can be required to close under an involutive label adjoint, designate an
adjoint-closed scalar-label sector transforming by the scalar law under the same Poincaré
representation/domain chain, and commute for every label pair on spacelike-separated supports.
Tensor or spin labels outside that sector require their own transformation interface. A reusable
finite-multiplet layer now supplies one genuine strongly continuous complex-linear lift-group
representation, exact translation-trivial component mixing, same-domain covariance, and mandatory
nontrivial component. Its separate tensorial strengthening factors through the projected Lorentz
transformation, while the base surface retains possible spinorial central action. The existing
nontrivial scalar label derives an exact one-component trivial multiplet. The 3D/4D cores now
classify every label exhaustively: scalar labels retain the scalar law, exact stress labels retain
only their rank-two law, and every residual bosonic label belongs to a finite projected-Lorentz
multiplet. This avoids an unrelated duplicate law for stress components. Every residual multiplet has an
exact in-cover adjoint partner with the existing family adjoint labels and coefficientwise conjugate
mixing; stress labels are fixed by that same family adjoint. Spinorial fields are outside this
all-label bosonic-locality family and require a separate graded-locality surface. A further exact coherence surface identifies the scalar Wightman field with this family's
existing nontrivial label and identifies its adjoint with the corresponding involutive adjoint
label, transferring family anti-vacuity to the Wightman field and preventing disconnected scalar
and observable sectors. Normalized
compact-first-anchor diagonal probes have linearly scale-controlled support and a canonical
polynomial Schwartz-seminorm envelope. A generic weak OPE checker carries a designated probe and
packages `C(x-y) O(x)` relative tempered coefficients, exact coefficient/local-field contraction, finite
monotone truncations, connected remainders, and all-order little-`o` behavior. A deliberately basic
classical-to-quantum interpretation bridge now maps the normalized unit and the exact canonical
curvature-squared density to labels in one local family, with a nonempty base, exact dimension match,
and nonzero non-unit `F²` action. The dependent adjoint-fiber topology is now proved compatible with
its transported additive/module operations, enabling a continuous multilinear carrier with explicit
derivative slots and two alternating curvature slots. Its order-zero value is exactly the same
smoothly descended curvature. An uninhabited degree-zero adjoint-section derivative interface now
uses Mathlib's intrinsic additivity/Leibniz carrier and requires the exact same-connection local
formula `dσ(X) + [A(X),σ]` in every designated chart. A separate strengthening requires Mathlib's
`C∞` covariant-derivative regularity and derives a smooth derivative-bundle section from every
smooth adjoint section; this is required data, not a construction from the formula. The exact
section derivative is now canonically packaged as a degree-one adjoint-valued form for every
pointwise degree-zero input, with exact evaluation, input-section coherence, and uniqueness. The
stored `C∞` derivative regularity now derives smoothness of this exact output for every smooth input,
and its designated-chart value has the same local formula. Separately, a reusable continuous graded
bracket wedge now combines a one-form with every `n`-form by the exact omitted-slot alternating sum,
with degree-one coherence and the one-with-two three-term formula proved. The existing smooth
coordinate bracket now derives smooth closure of that exact graded carrier and a bundled operation
coherent with the earlier degree-one smooth wedge. Additivity and real-scalarity in each graded
argument are derived explicitly. The exact cubic self-bracket is proved zero, pointwise and
smoothly, by expansion to twice the cyclic Lie Jacobi sum. The positive-degree ordinary Cartan
certificate now makes a supplied `2 → 3` exterior derivative typeable. At `n = 0` its formula is
proved equal to the earlier one-form formula, with conversions in both directions preserving the
exact degree-two derivative carrier. Mathlib's normed-space `d² = 0` theorem now proves the
positive-degree Cartan expression of the same first derivative vanishes within a set and globally,
including the exact `1 → 2 → 3` endpoint. The same finite-dimensional coordinate bracket used by
the actual group Lie algebra is now connected to Mathlib's bounded-bilinear derivative rule, with
exact two-input and self-bracket `fderiv` formulas. Its continuous one-with-`n` coordinate wedge is
constructed with the exact omitted-slot sum and proved to be precisely the coordinate image of the
intrinsic graded Lie-bracket wedge. Exact fixed-tuple evaluation is continuously linear, and every
self-wedge two-vector coefficient now has a derived same-input four-term `fderiv` rule. Exterior
alternation of those coefficients is proved to equal `-2 • (A ∧ dA)` for the exact skew coordinate
bracket. An explicit operator-norm bound packages the wedge as a continuous bilinear map, derives
whole-form differentiability from the same input, and identifies that alternation with Mathlib's
`extDeriv`. Combining this with Mathlib `d² = 0` and coordinate Jacobi cancellation now derives the
exact finite-dimensional normed-coordinate Bianchi identity for `F_A = dA + 1/2[A ∧ A]` and
`D_A F_A = dF_A + [A ∧ F_A]`, all from the same twice differentiable one-form. A within-set version
retains the exact chart-style set, `ContDiffWithinAt`, `UniqueDiffOn`, membership, and
closure-of-interior hypotheses and recovers the global definitions on `univ`. Fixed-value manifold
forms now have distinct raw unrestricted and explicit within-set normed-coordinate pullback
carriers. Inverse extended-chart specialization uses the corner-aware `mfderivWithin` on the exact
model range, with chart-center recovery, target-local derivative invertibility, linearity, and
canonical bracket-wedge coherence. For a finite-dimensional principal total-space model, the exact
connection's stored intrinsic smoothness now derives `C∞` regularity of this whole coordinate
one-form throughout the actual chart target. That regularity result alone asserts no naturality or
geometry outside the chart target; the subsequent Cartan-transport theorem derives naturality on
the target. The exact principal connection, its indexed exterior-
derivative certificate, and the curvature derived from both now satisfy Freed's curvature equation
in arbitrary within-set coordinates and inverse extended charts. For an arbitrary map/two-set
pullback the derivative remains the certificate carrier; in finite-dimensional inverse charts it is
now derived equal to `extDerivWithin` of the exact coordinate connection. An exact
naturality predicate now separates the corner-aware tangent-transport source from the exterior-
calculus set. In finite-dimensional total-space models, intrinsic connection smoothness now
discharges coordinate regularity and its order bound automatically, while Mathlib's extended-chart
theorems derive unique differentiability and closure-of-interior membership. Reusable inverse-chart
Cartan mathematics now proves the remaining within-chain-rule and Lie-bracket transport equality for
arbitrary fixed-value one-forms. Applied to the exact connection, this derives full exterior
naturality and the same-connection coordinate Bianchi theorem at every actual chart-target point,
without accepting naturality, regularity, or Bianchi witnesses. The exact smooth adjoint-bundle
curvature descent is now joined to this result chartwise: its designated base-chart coordinate is
the same principal curvature evaluated on the chart's local section and tangent lifts, and that same
representative obeys coordinate Bianchi. That result-specific bridge alone is not an intrinsic
three-form, but the later general positive-degree construction now supplies the actual descended
`D_A F` carrier under explicit same-chain certificates. Canonical arbitrary-manifold exterior
existence, arbitrary-manifold `d²`, arbitrary-manifold graded Leibniz transport, curvature-exterior
certificate construction, arbitrary-manifold curvature structure, and positive curvature-tensor
orders remain open; finite-dimensional structure and intrinsic descended Bianchi zero are derived. The interpreted observable layer now extends the exact
unit and `F²` labels to the finite intrinsic fragment `1`, `F²`, `(F²)²`, with exact classical
carrier coherence. A separate explicit anti-collapse strengthening requires `(F²)²` to be a new
nontrivial operator in the 4D core; this is not attributed to Clay's footnote. Smooth gauge
automorphisms now pull principal connections back with both connection laws and smoothness derived.
Arbitrary-degree smooth pullback and Lie-bracket-wedge naturality additionally show that the
curvature formula assembled from the exact pulled derivative carrier equals the pullback of the
original curvature. Reusable diffeomorphism mathematics now transports the full within-set Cartan
certificate when the source model is complete, exactly matching Mathlib's public Lie-bracket
naturality hypothesis; finite-dimensional total-space models derive completeness. The resulting
canonical transformed principal `curvatureForm` equals the total-space pullback of the original
exact curvature. Torsor uniqueness now constructs the associated function `g_ϕ` with
`ϕ(p)=p·g_ϕ(p)` and its exact conjugation law. Differentiated projection preservation,
horizontality, and right-equivariance derive the evaluated local curvature formula
`F_{ϕ* A}(p)=Ad(g_ϕ(p)⁻¹)F_A(p)`. The selected `g_ϕ` is identified with explicit second
coordinates on canonical local sections; chart reconstruction and its conjugation law derive
smoothness on every chart source and hence global `C∞` regularity from atlas coverage. Left
trivialization now defines the associated Maurer–Cartan one-form carrier. The variable principal
action tangent splits into fixed right translation plus its fundamental vertical term, so connection
equivariance and vertical normalization derive the evaluated affine formula
`ϕ*Θ=Ad(g_ϕ⁻¹)Θ+g_ϕ⁻¹dg_ϕ`. For every supplied exact smooth connection, joint adjoint regularity
and this affine identity express the unchanged Maurer–Cartan carrier as a difference of derived
smooth forms, yielding an exact smooth-form bundle. The exact original curvature structure
certificate now transports to the canonical gauge-pulled curvature. Its pointwise adjoint-bundle
descent is identified both by the selected-section `Ad(g_ϕ⁻¹)` coefficient and an equivalent
inverse-shifted principal representative; it is not asserted equal to the original adjoint-valued
curvature. The covariant quotient action `[p,X] ↦ [ϕ(p),X]` is now constructed on the actual
adjoint bundle and exact dependent fibers, with identity, composition, and inverse laws. Pointwise
curvature and evaluations of the exact smooth descended package transform by the inverse induced
fiber action. In selected quotient-derived coordinates the forward action is exactly `Ad(g_ϕ)`;
every fixed dependent fiber action is therefore packaged as a continuous real-linear equivalence
whose inverse is the inverse gauge action. Continuity descends through the defining quotient map,
producing a quotient homeomorphism; transport through the exact quotient/dependent carrier
homeomorphism yields a base-preserving dependent-total-space homeomorphism with those exact fiber
restrictions. In every named quotient chart the action is exactly
`(b,X) ↦ (b,Ad(g_ϕ(s(b)))X)`; this globalizes forward and inverse `C∞` regularity and packages the
quotient action as a diffeomorphism. On the named dependent smooth-vector-bundle structure, the
same exact local formula derives a base-preserving total-space `C∞` diffeomorphism whose fixed-fiber
restrictions are the previously established continuous-linear equivalences. This completes the
layered smooth vector-bundle-automorphism packaging. The exact adjoint-fiber pairing and its
quadratic value are invariant when both arguments undergo this action. Direct tangent-map calculus
now proves connection-independent smoothness of the exact associated Maurer–Cartan pullback,
independently of the existing affine-difference proof using a supplied connection. On the universal group form, the exact Cartan
expression on left-invariant fields fixes the sign and `1/2` self-wedge normalization; the
associated form is identified as its pullback and the smooth derivative candidate is packaged.
Reusable mathematics now proves field-extension independence in normed spaces, exact centered-chart
coordinates, and intrinsically once a Cartan certificate exists. Finite-dimensional Cartan tensoriality now upgrades the invariant-field calculation to a genuine
universal exterior-derivative certificate and proves `dθ + 1/2[θ∧θ] = 0` on the group. The
associated derivative candidate is now proved exactly equal to the raw pullback of the certified
universal derivative. Exact chart-safe carrier and locality bridges now construct arbitrary-smooth-map
Cartan certificates from exact smooth pullback packages on finite-dimensional source and target
models. Thus the associated candidate is certified as the exterior derivative of the exact associated
pullback and its normalized Maurer–Cartan equation is derived. Finite-dimensional
basis reconstruction now derives generic centered coordinate-form regularity and intrinsic
field-extension independence for admissible smooth fields, while arbitrary smooth fields transport exactly through the
corner-aware centered chart. Adjoint-bundle-valued forms now also have fixed-model base extended-chart
coordinates on the exact principal-chart overlap, retaining actual quotient fibers and corner-aware
inverse-chart tangent transport. Finite-dimensional base models now derive complete `C∞` regularity
of these alternating-map-valued coordinates within the exact overlap for designated atlas charts;
the exact overlap now carries a typed `dF + [A∧F]` expression whose potential and curvature are tied
to the same connection, local section, tangent lifts, and descended-curvature chain. Local-section
exterior naturality is now derived from `ContMDiffOn` without globally smoothing the totalized
section, and the descended `F` is proved equal on the unchanged overlap to the coordinate curvature
of that same `A`. Exact-overlap potential regularity and domain geometry now discharge the
within-coordinate Bianchi hypotheses, proving this local `dF + [A∧F]` expression vanishes. Every
such exact local expression is now identified with the corresponding coordinate of the existing
intrinsic smooth zero adjoint-valued three-form. That result-specific bridge alone does not construct
the later positive-degree operator or nonzero chart-transition laws; the separate conditional
positive-degree descent now supplies the same-chain intrinsic `D_A F` carrier. A reusable finite multilinear telescope now proves lift independence for horizontal principal
forms of every degree, with degree two definitionally compatible with the existing curvature chain.
Right-adjoint representative independence and smooth descent into the actual dependent quotient
fibers are now derived in every degree, with arbitrary designated-chart coordinate formulas and
exact degree-two compatibility. The exact smooth positive-degree total-space candidate
`dω + [Θ ∧ ω]` is now constructed from one unchanged connection, input form, and supplied ordinary
exterior certificate, including its `2 → 3` specialization. Inner-conjugation diffeomorphism
calculus now proves that the exact derivative-defined adjoint preserves the intrinsic tangent Lie
bracket, closing the algebraic bracket-covariance substep. Positive-degree Cartan expressions and
certificates now transport through smooth diffeomorphisms when the source model is complete, and the exact bracket correction
preserves right-adjoint equivariance in every degree. The correction's exact signed value with one
vertical slot, vanishing with two vertical slots, and fundamental-vector specialization are derived;
the corresponding negative ordinary-derivative value is proved sufficient for candidate
horizontality. Smooth local triviality now proves that every vertical tangent has a unique
fundamental generator, recovered by the connection form, and every fixed generator yields a globally
smooth fundamental field with the expected right-action curve velocity. The smooth right-invariant
field has been constructed and its left-trivialized coefficient proved to be exactly `Ad(g⁻¹)Y`.
The universal Maurer--Cartan certificate now derives the coefficient derivative as `-[X,Y]`
conditionally on the exact identity-point commutation of left- and right-invariant fields. The
corner-safe Schwarz cancellation for opposite mixed-partial fields under the exact first-partial normalization hypotheses and exact `C²`-within
regularity of identity-centered chart multiplication are now proved. Both exact first-partial
normalizations and identity-point chart-coordinate identifications for the left- and right-invariant
fields are also derived. Target-wide chart-field equality and intrinsic left/right invariant-field commutation at the identity is now
proved, and the universal Maurer--Cartan certificate derives the unconditional exact formula
`d(Ad(·⁻¹)Y)₁(X) = -[X,Y]`. The exact principal-orbit coefficient derivative and all nondistinguished horizontal cancellations
are now derived, reducing the targeted Cartan comparison to an explicit termwise triangular bracket-evaluation
vanishing premise. The Cartan reduction is now localized to arbitrary open calculus sets. Prescribed-value
orbit-adapted fields are constructed in base/group product coordinates on an open full-fiber domain,
with exact all-orbit transport and normalized fiber-bracket vanishing. The exact product-manifold within-bracket vanishing theorem is now derived at the normalized center, with derivatives taken
within the natural open product domain. Open partial-diffeomorphism bracket naturality is now packaged, and the adapted fields are
transported through a designated smooth principal trivialization at points with normalized fiber
coordinate `1`, retaining prescribed values, all-orbit adaptation, and total-space bracket zero.
A principal trivialization can now be normalized at an arbitrary point by left-shifting its group
coordinate; a conservative one-chart atlas extension retains the exact torsor, projection/action
certificates, and selected charts while constructing enlarged bundle data with proved smoothness and yields an adapted total field with arbitrary prescribed value at every point. All
prescribed slot fields can now be assembled on one exact common open source, even for an
unrestricted index type. Horizontality now discharges all surviving triangular Cartan evaluations;
fundamental-slot cancellation is unconditional, and vertical tangent generation proves full
horizontality of the positive-degree covariant-exterior candidate. Output-linear transport and
right-translation pullback of positive-degree exterior certificates now prove full right-adjoint
equivariance of both the ordinary derivative and the complete candidate. The candidate now descends
to the actual dependent adjoint-bundle fibers as a smooth positive-degree operator. Its curvature
generic specialization is an exact same-connection smooth adjoint-valued three-form carrier
`D_A F`, initially indexed by the same curvature-structure and ordinary curvature-exterior
certificates. Arbitrary-degree inverse-chart regularity and exact centered
`extDerivWithin` identification are now derived for that supplied certificate. Combining those
results with the same-connection coordinate Bianchi theorem proves the principal candidate globally
zero and the intrinsic descended `D_A F` equal to the canonical smooth zero adjoint-valued
three-form. Finite-dimensional Cartan calculus now also derives curvature horizontality and
right-adjoint equivariance from the connection laws, so the strengthened intrinsic Bianchi API no
longer accepts a structure certificate from the caller. In finite-dimensional manifold models, arbitrary-degree Cartan transport for arbitrary local smooth
fields, certificate-free field-extension independence, exact set-germ locality, and coordinate
Bianchi now construct the curvature-indexed ordinary exterior certificate itself as
`dF = -[A∧F]`. Thus finite-dimensional intrinsic `D_A F = 0` requires only the connection and its
exact connection-indexed first exterior data; that first exterior datum remains supplied rather than
constructed. Generic arbitrary-manifold curvature structure and curvature-exterior construction
remain open. Exact inverse-action
curvature covariance now derives pointwise invariance of both chosen and basis-independent
canonical curvature densities for the full pulled connection/exterior/certificate chain. The exact
analytic datum transports to that chain with unchanged designated measure and coupling, deriving
invariance of the integrated relative-to-measure Euclidean action. This is vertical gauge
invariance, not base-diffeomorphism or metric-volume invariance. The finite interpreted fragment
`1`, `F²`, `(F²)²` transports to the pulled chain with unchanged exact classical carriers, quantum
family, labels, operator witnesses, and quartic anti-collapse data. This remains same-family
transport. Independently, a quantum gauge interface now represents a generic gauge group algebraically on the
exact common domain and derives conjugation on operators. A separate certificate, indexed by one
exact designated action rather than choosing its own convenient action, requires every label and
smearing to be invariant. It asserts neither unitarity nor continuity. The action and its exact-action invariance certificate
are now specialized, without constructing either, to the canonical group of smooth automorphisms
of one fixed principal bundle. A one-way coherence bridge
applies its all-label law to every exact interpreted `1`, `F²`, and `(F²)²` label without replacing
the designated action. Further classical/quantum transformation-law coherence remains open. The
checker still lacks a language of independent invariant contractions,
mixed curvature polynomials, or covariant derivatives, and no canonical injective quantization map
is claimed.
A preliminary four-dimensional perturbative interface now requires a positive running coupling
on an explicit open ultraviolet tail, exact beta flow, ultraviolet limit, and negative cubic leading
normal form. An exact supplied normalization certificate now chooses a basis orthonormal for the
same classical invariant pairing, imposes Gross–Wilczek's adjoint-Casimir contraction identity on
the exact tangent bracket, and fixes the one-loop coefficient to `11 C₂(G)/(3·16π²)`. An explicit
ultraviolet reference scale equates this same running coupling with the outer coupling in the exact
classical action. It does not construct that basis, prove the connection-level field-rescaling
convention, or calculate the perturbative remainder. A separate supplied regular-variation
interface ties every
nonzero coefficient of the exact weak OPE to normalized short-distance Schwartz dilations, signed
real radial degree, a real power of the same running coupling, and a nonzero weak distributional
limit. This is acceptance data, not a perturbative calculation: anomalous dimensions, mixing,
scheme dependence, remainders, independent/mixed curvature-polynomial and derivative labels, and
Clay's prescribed singularities remain open. A separate same-family stress-tensor checker
requires symmetric Hermitian components local relative to the whole family, explicit inverse-matrix
contravariant rank-two Lorentz covariance, weak distributional conservation, and a nonzero non-unit
energy density. A separate anti-confusion contract excludes every stress-component label from the
scalar sector, while general Lorentz mixing for other non-scalar labels remains open. Its symmetry/conservation semantics are independently sourced to an authoritative
gauge-theory energy-momentum review. A separate bridge uses explicit delta-convergent temporal
mollifiers and bounded expanding spatial cutoffs to identify strong `T^{0ν}` charge limits with
common-domain momentum generators tied to the same physical translation unitaries and joint PVM;
it also imposes the corresponding all-family infinitesimal Ward identities. Trace-anomaly semantics
remain open. Normalized algebraic smeared vacuum correlators are extracted from exact
finite field words, with
one- and two-point operator order locked to the same selected vacuum and field. A separate interface
requires an actual full-product tempered distribution at every arity and exact coherence on every
finite pure Schwartz tensor. Determinant-one complex-linear automorphisms preserving the exact
complex-bilinear mostly-minus form now form a named proper complex Lorentz group acting
simultaneously on finite relative configurations; four-dimensional complex negation is an explicit
nonidentity element. The exact extended tube is now the open invariant union of all simultaneous
proper-complex-Lorentz images; a negated standard point proves strict four-dimensional enlargement.
An uninhabited scalar interface now requires a single-valued holomorphic invariant extension and
attaches one at every arity to the exact same relative-distribution/full-correlator/field chain.
Group topology, connectedness, analytic structure, and derivation of the continuation theorem remain
pending. The exact-sign open backward tube `ξ - iη`, `η ∈ V₊°`, is constructed
and proved nonempty in dimensions 1–4. A separate interface requires genuine holomorphy there,
integrable regularized tube-function pairings for every strict direction tuple, and convergence in
the tempered-distribution topology as all directions jointly approach zero. A strengthened
interface additionally requires uniform radial polynomial growth over every compact strict
imaginary-direction set. A connected relative-coordinate interface uses normalized coordinate-
Lebesgue anchor tests to identify each full correlator with one relative tempered distribution and
makes that exact distribution the analytic boundary; coherence is required for every normalized
anchor. The first explicit Euclidean/Minkowski bridge reverses strictly increasing Euclidean point
order, sends `τ ↦ -iτ`, and proves that every resulting consecutive relative coordinate lands in
the exact backward tube. A strict-domain continuation interface then equates each Euclidean
Schwinger distribution on every strict ordered/flat test with the genuinely integrable value of the
same reverse-Wick analytic function. An exact-source continuation interface now extends this equality
to every derivative-vanishing ordered OS source test and derives the strict view by restriction.
Nonzero source values are proved to map into the tube and the integrand vanishes outside its
preimage. Requiring absolute integrability for all such possibly noncompact source Schwartz tests
strengthens OS-I's initial compact-support formula. Separately, OS-II `(R0′)` now requires one common
positive Wightman Schwartz order, exact printed full-coordinate controls, and positive `ωₙ` bounded
by `α β^(n²)` on the same full correlator family. A narrow package now bundles selected `(R0′)`,
relative analytic, and exact-source Wick data and requires all-arity correlator-extension uniqueness
only on the same field realization. A transport relation aligns potentially different lift carriers
by a projection/translation-preserving continuous group equivalence and uses one Hilbert unitary for
representations, vacua, common domains, fields, and adjoints; equality of every finite field/adjoint
vacuum word is derived. Its source-facing specialization fixes the exact lift and group element.
Corrected reconstruction acceptance quantifies over corrected/coherent alternative Hilbert
realizations in the selected universe on that same lift and requires both this fixed-lift unitary
equivalence and equality of the separately supplied full tempered-distribution families. This remains
an uninhabited acceptance condition: any proof or construction of reconstruction,
arbitrary-polynomial comparison, derivation or inhabitation of the
extended-tube continuation interface, and full observable interpretation remain pending, and no continuation or correlator
datum is constructed. No concrete gauge-group, connection, invariant-inner-product, curvature, or
structure-certificate witness,
symmetry group, source-facing reconstruction theorem, quantum-theory witness, Yang–Mills existence
claim, or mass-gap claim is present.

The independent finite-cutoff lattice layer now packages nonempty periodic vertices, group-valued
positive links, cyclic shifts, endpoint gauge transformations, plaquette holonomy, and a
nonnegative conjugation- and inversion-invariant nontrivial Wilson-type potential with a strictly
positive coefficient. Gauge invariance, plaquette orientation independence, zero identity action,
and dimension-one absence of plaquettes are proved. Signed paths, endpoint-covariant holonomy, and
Wilson-loop observables built from supplied nonconstant conjugation-class functions are explicit;
the elementary four-step path is proved closed with holonomy equal to the plaquette. A finite-cutoff Gibbs acceptance interface now
constructs the exact finite product of probability-normalized compact-group Haar measure and
proves its link marginals and local gauge invariance. For a measurable positive Boltzmann density,
partition positivity/finiteness, Gibbs normalization, and Gibbs gauge invariance are derived on that
same reference chain. Signed paths carry exact finite positive-link supports; bounded measurable
class observables are proved support-local and integrable, and their closed-loop expectation is
defined only from supplied product-Haar Gibbs data. No potential-measurability datum, Gibbs datum,
or evaluated expectation is constructed. An explicit even-periodic time reflection handles time-link
orientation reversal and supports a separate finite-cutoff Osterwalder–Seiler positivity checker with
a mandatory nonzero positive-support test. No positivity datum, continuum limit, or identification
with continuum OS data or the continuum action/PVM is made. A separate scaling-trajectory checker
requires spacing and bare coupling to vanish while sites per axis and physical linear extent
diverge, keeps the
bare coupling distinct from the action coefficient, and can require convergence of exact lattice
observable expectations to an independently supplied target functional. No trajectory, target,
renormalization bridge, or continuum identification is constructed.

The first dimension-specific boundary now proves that continuous local two-forms and plaquette
actions vanish in Euclidean spacetime dimension one, with no spatial clustering direction or
spacelike pair. It separately proves that a nontrivial periodic one-site holonomy may remain and
that the analytic Wightman tube is nonempty. These are boundary facts, not a one-dimensional theory
or a route to the four-dimensional contract. An explicit Clay-endpoint predicate rejects every
supported dimension `1`–`3`, and finite-rank proofs rule out any real-linear identification of their
coordinate spacetimes—especially the 3D core base—with the exact four-dimensional core base.

The first dimension-two consistency layer proves the opposite local nondegeneracy: an explicit
continuous area two-form evaluates to one, a normalized spatial direction and nonzero spacelike-
separated Schwartz tests exist, and a concrete `2 × 2` periodic one-link gauge field realizes every
prescribed group element as one selected plaquette holonomy. Every admissible nontrivial plaquette
potential therefore has a concrete strictly positive local plaquette density. These remain
kinematic and finite-cutoff witnesses—not a continuum two-dimensional Yang–Mills theory, OS datum,
Wightman theory, or mass-gap result—and dimension two is proved distinct from Clay's dimension four.
The separate uninhabited `TwoDimensionalGaugeFixedHolonomyMeasureData` now records Driver's rigorous
continuum acceptance nucleus without constructing it: a normalized law on an exact gauge-fixed
sample carrier maps into a distinct ambient connection carrier, on which gauge transformations,
endpoint-covariant holonomy, and gauge-invariant physical observables live. Sampled holonomy and
observables are tied to that exact restriction map. No action or invariant measure is falsely
asserted on the gauge-fixed slice. A separate uninhabited selected-loop strengthening now requires
one exact closed loop with positive supplied area, identifies its sampled-holonomy pushforward with
an `ENNReal` central/inversion-symmetric density against the neutrally constructed canonical
normalized compact Haar measure, and derives one exact physical class-observable expectation
formula. Neutral reusable convolution now fixes
`(f⋆g)(z)=∫f(x)g(x⁻¹z)dμ_H`; a further uninhabited same-density certificate requires normalization
at every positive time, exact addition/convolution, and weak convergence to identity against every
continuous complex test, deriving the selected-area two-half split. Reusable manifold calculus now
constructs scalar first and iterated derivatives along the exact right-invariant group fields and
Driver's finite orthonormal-basis Laplacian sum; an uninhabited certificate ties the basis to the
same explicit invariant pairing and requires independence from every other such basis. The next
uninhabited layer is indexed by the exact compact-connected-simple project group and ties a strictly
positive spatially smooth real family pointwise, via `ENNReal.ofReal`, to the unchanged density; it
requires Driver's exact `∂ₜQ=½ΔQ` sign and factor against that same Laplacian. A further uninhabited
process realization starts at the identity almost surely, has almost-surely continuous paths and
mutually independent stationary right increments with those unchanged density laws. Its one-time
marginals are derived, including exact equality at the selected area with the sampled loop-holonomy
law. The metric bridge now transports the exact invariant pairing to every group tangent fiber by
left Maurer–Cartan trivialization and proves its inverse, symmetry, strict positivity, and left/right
invariance with the exact `Ad(h⁻¹)` convention. A reusable finite-dimensional compact-unit-sphere
argument now proves von Neumann boundedness of every strictly positive continuous bilinear unit
ellipsoid and discharges that exact obligation for each group tangent fiber. The exact
parameter-dependent derivative `D_y(x⁻¹y)|_{y=x}` is now proved smooth after Mathlib's tangent
coordinate transport at every center. Finite-dimensional evaluation mathematics proves smooth
diagonal bilinear precomposition; exact nested Hom-bundle coordinate reconciliation then packages
the unchanged positive bi-invariant form as Mathlib's full `ContMDiffRiemannianMetric`. No density,
solution, or process is constructed; Laplace–Beltrami comparison remains open before treating
this as a completed source heat-kernel chain. Finite oriented-edge words now retain one coordinate
per underlying edge, inversion under reversal, and Driver's later-on-the-left transport order.
Oriented endpoints now derive target-left/source-right-inverse vertex-gauge covariance, cancellation
at every internal vertex of a composable word, and start-vertex conjugation for a closed word. The
finite product of one canonical normalized Haar probability per underlying edge is constructed,
with exact marginals and endpoint-gauge invariance. Finite word holonomy and finite products of
supplied nonnegative density slices are proved measurable, yielding the generic product-Haar
`withDensity` carrier; no normalization is inferred for arbitrary words. This is reusable
algebra/measure theory, not by itself a planar graph certificate or face law. A separate concrete
uninhabited simple-boundary topological planar certificate now requires exact ambient path curves
coherent with reversal/concatenation, concrete finite vertical/`C¹`-horizontal admissibility
decompositions for every edge (with explicitly stronger affine-speed normalization), separated
vertices, injective edge arcs, endpoint-only crossings, full disjoint complement decomposition, a
finite connected-cell decomposition after adjoining Driver's x-axis, a segmentwise word-realized
once-around Jordan frontier, and coordinate-Lebesgue area. This is a strengthened subclass, not yet Driver's full BC scope:
bridge-multiplicity boundaries remain open. On this exact Jordan subclass, an uninhabited
face-product law now quantifies over every measurable, integrable finite vertex-gauge-invariant
complex graph function, assigns it an existing ambient gauge-invariant observable through the same
edge paths, and requires its expectation to equal integration against product Haar weighted by the
unchanged selected density at exact face areas and words. The exact unit case derives normalization
of that carrier. No planar graph instance, heat kernel, planar/Yang–Mills measure, or model is
constructed. Reusable finite BC word infrastructure now defines a bridge by absence of an
edge-avoiding source-to-target path, permits at most one traversal in each opposite orientation for
bridges, permits at most one total traversal for nonbridges, and rejects doubling of cycle edges.
A boundary-neutral embedded geometry now factors the unchanged paths, conservative injective-arc
strengthening, endpoint-only intersections, exact complement components, x-axis cells, and areas.
An uninhabited embedded BC certificate adds literal connectedness of every bounded face frontier and
an exact continuous closed ordered traversal carrying the bridge-aware word. As before, Driver-
permitted one-edge loop incidence must first be subdivided into embedded arcs. No graph or law instance is constructed. An uninhabited BC face-product law now universally
quantifies over every measurable, integrable finite vertex-gauge-invariant complex graph function,
ties it to an existing ambient physical observable through the unchanged paths, and requires the
exact product-Haar formula with unchanged densities at geometric areas and bridge-aware words. Its
unit case derives normalization and nonzeroness. A separate general-boundary interface now records
the universal carrier of every valid simultaneous boundary presentation, with finite ordered
component words, exact traversals, pairwise-disjoint nonempty traces, and maximal connected-frontier
semantics that reject duplication and artificial splitting. Driver Definition 6.3's origin is
optional, exactly tied to coordinate zero when present, and proved absent otherwise. The uninhabited
expectation law uses the corresponding conditional restricted gauge invariance, computes every choice-indexed product-Haar integral from the same
ambient observable, and derives integral-level choice independence without false pointwise
holonomy equality. A further universal Theorem 6.4 strengthening quantifies over every Driver tree—
an underlying-edge set with no nonempty closed distinct-edge path—and uses the exact mixed product
with identity Dirac mass on tree coordinates and unchanged Haar elsewhere. It retains the unchanged
choice-indexed density and ambient observable expectation, deriving frozen/unfrozen and cross-tree/
choice integral equality plus normalization and nonzeroness. Refinement/gluing and lattice-limit
layers remain explicit debt.

A first uninhabited three-dimensional current-strength continuum core is now hard-wired to
three-dimensional spacetime and its two-dimensional spatial slice. Its classical base is exactly
coordinate `ℝ³`, its metric is Mathlib's canonical flat inner-product metric, and its designated
action measure is coordinate Lebesgue measure; only the general metric-induced-volume API bridge
remains explicit debt. It dependently joins one compact-simple
physical gauge group and exact classical curvature/action chain to one strict
Euclidean scalar candidate, one Wightman representation/vacuum/domain/field/spectrum chain, exact
full and relative correlators, strict Wick coherence, the same coherently connected covariant local-
observable family, an exact `F²` interpretation, a symmetric conserved local stress tensor whose
regulated charges and Ward identity use that same joint PVM/translation chain, and a positive
physical gap on the same spectrum.
It imports no lattice regulator, four-dimensional OS spatial-`ℝ³` tensor surface, or four-dimensional
running-coupling data, and no inhabitant is constructed. The `CurrentStrength` qualifier retains the
known OS-II/source-space reconstruction and genuine Poincaré-cover debts.

A parallel uninhabited four-dimensional current-strength core now fixes coordinate `ℝ⁴`, the
canonical flat metric and coordinate Lebesgue measure, then dependently joins the same classical,
carrier-exact OS-II `(E0′)` plus source-carrier OS-I `(E1)`–`(E4)` package, Wightman,
exact derivative-vanishing source Wick coherence, corrected-output Wightman `(R0′)`, observable, the finite scalar fragment `1`, `F²`, `(F²)²` and its exact same-family natural-power extension `(F²)ⁿ`,
stress/translation, and same-PVM gap surfaces at the actual Clay dimension. Its exact observable
family now carries one designated algebraic action of the canonical smooth principal gauge group,
an all-label invariance certificate for that same action, and derived invariance of each interpreted
`1`, `F²`, `(F²)²` label and every natural-power label; no representation is constructed and no unitarity or continuity is
implied. Unlike the lower-dimensional core it also requires the
four-dimensional pure-gauge running-coupling/beta normal form with an exact supplied
adjoint-Casimir/invariant-pairing one-loop normalization, exact same-family bilocal products/weak OPE, supplied regular-variation scaling by that same
coupling, and an anti-disconnection bridge forcing the interpreted `F² × F²` input to have one
nonzero contracted zeroth-order OPE term whose coupling exponent and leading scaling distribution
are both nonzero. The mostly-minus trace is now defined directly from the same stress components,
and a supplied Collins–Duncan–Joglekar physical-reduced anomaly interface requires one nonempty
on-shell/nonzero-momentum weak sector tied to the exact interpreted `F²`, normalized beta, and
classical reference. The source `β(g)/(2g)` convention and a separately supplied `g⁻²`
renormalized-operator conversion to the project's outer-coupling convention remain explicit; no
unrestricted trace identity is asserted. Its Euclidean package retains explicit ambient tempered extensions but restricts
to carrier-exact OS-II `(E0′)` and requires corrected same-lift, universe-relative reconstruction
acceptance with heterogeneous Hilbert-unitary equivalence and full tempered-distribution uniqueness.
This is still not the final Clay contract: concrete inhomogeneous `SL(2,ℂ)`, matrix realization of
the accepted literal-sign kernel, and construction of the named affine-target group law,
source-faithful curvature-polynomial observables, renormalized OPE coefficients/remainders, and
mixing-complete trace semantics beyond the selected physical reduction remain open. No inhabitant is
constructed.

Primary OS-I and correcting OS-II article scans, Wightman's 1956 paper, and the corrected Princeton
edition of Streater–Wightman are hash-pinned with exact text extractions. Load-bearing OS-II and
Wightman-axiom pages were visually verified. Wilson 1974 and Osterwalder–Seiler 1978 lattice sources
are also pinned and visually checked without identifying finite-cutoff results with the continuum
target. Wilson's 1969 OPE paper and the independent Gross–Wilczek/Politzer 1973 asymptotic-freedom
papers are pinned as observable and ultraviolet-consistency evidence. The Collins–Duncan–Joglekar trace-anomaly preprint and supplied published article are pinned and
cross-checked at their mixing and physical-reduction equations. The complete 33-PDF user literature
bundle is now inventoried: seven files are byte-identical to existing canonical artifacts and 26
distinct sources are retained with manifests and native extraction, except that the two image-only
Atiyah scans use calibrated Mathpix per-page drafts plus independent visual adjudication. This
closes the known acquisition gap for rigorous 2D evidence, Hodge/volume, Poincaré/`SL(2,ℂ)`,
extended-tube, and composite-operator/BRST mixing work; it does not implement those remaining Lean
interfaces. See `docs/SUPPLIED_SOURCE_INGESTION_AUDIT.md`. Source acquisition constructs
no Euclidean, lattice, observable, renormalized, or Wightman theory.
