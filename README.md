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
[`docs/AUDIT_BIBLIOGRAPHY.md`](docs/AUDIT_BIBLIOGRAPHY.md), and the evidence-only current state in
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
regularity, pointwise and smooth principal connection-form definitions, the derived principal
curvature formula, intrinsic curvature horizontality/right-adjoint-equivariance certificate semantics,
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
Schwartz seminorms are also implemented as preliminary regularity infrastructure; they are not yet
identified with OS-II `(E0′)`. Exact positive-arity Schwartz permutation pullback and scalar
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
carriers and topology, nuclearity, and OS-II-strength reconstruction remain open. `(E2)` remains
absent pending those comparisons, a separately constructed completed tensor product for
positive-half-space tests, and the source-facing
reflection-positivity inequality; the algebraic finite-sequence carrier
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
nonnegative-real form are defined on the current strict Mathlib subdomain, but are deliberately not
identified with source-facing `(E2)` before the carrier/topology comparison. Exact simultaneous
Euclidean translations and their finite-sequence lift are available as algebraic clustering
infrastructure. Normalized spatial rays are constructed in dimensions with a spatial coordinate,
the four-dimensional ray escapes to infinity, and dimension one is proved to have no such direction.
The exact connected factorization expression and zero-limit predicate are defined along an explicitly
supplied direction on the strict Mathlib subdomain, but are not identified with source-facing `(E4)`
before the carrier/topology comparison. Growth, `(E1)`, `(E3)`, strict positivity, and clustering are
assembled around one normalized family and direction in a non-source-facing candidate record; no
inhabitant is constructed. Independently, proper-orthochronous Lorentz and affine Poincaré
kinematics are now defined for the mostly-minus Minkowski form, with properness, time orientation,
and nontrivial translation probes. A weaker topological-group lift/pre-cover interface and one
strongly continuous unitary representation on a separable Hilbert carrier are packaged without
inhabitants; physical translations are derived from that same representation. A genuine topological covering projection remains pending. A normalized vacuum is
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
bilocal tempered products with exact pure-tensor operator order and nonzero witnesses. The same
family can be required to close under an involutive label adjoint, transform covariantly under the
same Poincaré representation/domain chain, and commute for every label pair on spacelike-separated
supports. Normalized
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
`D_A F_A = dF_A + [A ∧ F_A]`, all from the same twice differentiable one-form. Canonical
arbitrary-manifold existence, chart independence,
arbitrary-manifold `d²`, arbitrary-manifold graded Leibniz transport, positive-degree covariant exterior
differentiation, and
positive curvature-tensor orders remain open. This is not a general
curvature-polynomial/covariant-derivative language or a canonical injective quantization map. A preliminary four-dimensional perturbative interface now requires a positive running coupling
on an explicit open ultraviolet tail, exact beta flow, ultraviolet limit, and negative cubic leading
normal form. It intentionally leaves the group-dependent one-loop coefficient and invariant-pairing/
coupling normalization disconnected. A separate supplied regular-variation interface ties every
nonzero coefficient of the exact weak OPE to normalized short-distance Schwartz dilations, signed
real radial degree, a real power of the same running coupling, and a nonzero weak distributional
limit. This is acceptance data, not a perturbative calculation: anomalous dimensions, mixing,
scheme dependence, remainders, interpreted curvature-polynomial labels, and Clay's prescribed
singularities remain open. A separate same-family stress-tensor checker
requires symmetric Hermitian components local relative to the whole family, explicit inverse-matrix
contravariant rank-two Lorentz covariance, weak distributional conservation, and a nonzero non-unit
energy density. Its symmetry/conservation semantics are independently sourced to an authoritative
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
same reverse-Wick analytic function. Nonzero test values are proved to map into the tube and the
integrand vanishes outside its preimage. Requiring absolute integrability for all such strict
Schwartz tests strengthens OS-I's initial compact-support formula, and the carrier support itself
also remains stronger than OS-I: the exact
source-space comparison, arbitrary-polynomial comparison, derivation or inhabitation of the
extended-tube continuation interface, reconstruction, and full observable interpretation remain pending, and no continuation or correlator
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
or a route to the four-dimensional contract.

Primary OS-I and correcting OS-II article scans, Wightman's 1956 paper, and the corrected Princeton
edition of Streater–Wightman are hash-pinned with exact text extractions. Load-bearing OS-II and
Wightman-axiom pages were visually verified. Wilson 1974 and Osterwalder–Seiler 1978 lattice sources
are also pinned and visually checked without identifying finite-cutoff results with the continuum
target. Wilson's 1969 OPE paper and the independent Gross–Wilczek/Politzer 1973 asymptotic-freedom
papers are pinned as observable and ultraviolet-consistency evidence. Source acquisition constructs
no Euclidean, lattice, observable, renormalized, or Wightman theory.
