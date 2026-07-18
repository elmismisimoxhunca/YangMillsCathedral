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
[`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md), and the evidence-only current state in
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
```

Source verification is independent of Lean compilation. Both gates are required.

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
action, a typed pointwise manifold differential-form carrier, local-model exterior derivative and
an arbitrary-manifold one-form Cartan certificate, a smoothly closed Lie-bracket wedge,
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
coincidence diagonals. `(E2)` remains absent pending its embedding/sufficiency/density/completion comparison
with OS-I's derivative-vanishing ordered spaces, the induced topology on each arity space, the
identification of the named finite-stage final topology with OS-I's locally convex direct sum, the
distinct completed tensor product for positive-half-space tests, and the source-facing
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
Normalized algebraic smeared vacuum correlators are extracted from exact finite field words, with
one- and two-point operator order locked to the same selected vacuum and field. A separate interface
requires an actual full-product tempered distribution at every arity and exact coherence on every
finite pure Schwartz tensor. The exact-sign open backward tube `ξ - iη`, `η ∈ V₊°`, is constructed
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
source-space comparison, arbitrary-polynomial comparison, extended-tube continuation,
reconstruction, and observable interpretation remain pending, and no continuation or correlator
datum is constructed. No concrete gauge-group, connection, invariant-inner-product, curvature, or
structure-certificate witness,
symmetry group, source-facing reconstruction theorem, quantum-theory witness, Yang–Mills existence
claim, or mass-gap claim is present.

The independent finite-cutoff lattice layer now packages nonempty periodic vertices, group-valued
positive links, cyclic shifts, endpoint gauge transformations, plaquette holonomy, and a
nonnegative conjugation- and inversion-invariant nontrivial Wilson-type potential with a strictly
positive coefficient. Gauge invariance, plaquette orientation independence, zero identity action,
and dimension-one absence of plaquettes are proved. Signed paths, endpoint-covariant holonomy, and
Wilson-loop observables built from supplied nonconstant conjugation-class functions are explicit; the elementary four-step path is
proved closed with holonomy equal to the plaquette. A finite-cutoff Gibbs acceptance interface now
constructs the exact finite product of probability-normalized compact-group Haar measure and
proves its link marginals and local gauge invariance. For a measurable positive Boltzmann density,
partition positivity/finiteness, Gibbs normalization, and Gibbs gauge invariance are derived on that
same reference chain; bounded observable integrability remains explicit. No potential-measurability
or Gibbs datum is constructed. No lattice positivity, continuum limit, or identification with the
continuum action/PVM is made.

Primary OS-I and correcting OS-II article scans, Wightman's 1956 paper, and the corrected Princeton
edition of Streater–Wightman are hash-pinned with exact text extractions. Load-bearing OS-II and
Wightman-axiom pages were visually verified. Wilson 1974 and Osterwalder–Seiler 1978 lattice sources
are also pinned and visually checked without identifying finite-cutoff results with the continuum
target. Wilson's 1969 OPE paper and the independent Gross–Wilczek/Politzer 1973 asymptotic-freedom
papers are pinned as observable and ultraviolet-consistency evidence. Source acquisition constructs
no Euclidean, lattice, observable, renormalized, or Wightman theory.
