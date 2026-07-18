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
local installation; topological vector-space compatibility, identification with OS-I's locally
convex direct sum, and any required joint continuity remain pending. Exact reverse-conjugation on scalar Schwartz components is implemented
and kept distinct from Euclidean time reflection. Both operations are lifted to exact finite
sequences and combined in the source order `Θ f*`. The exact algebraic Schwinger evaluation and
nonnegative-real form are defined on the current strict Mathlib subdomain, but are deliberately not
identified with source-facing `(E2)` before the carrier/topology comparison. `(E4)` is also absent. No
concrete gauge-group, connection, invariant-inner-product, curvature, or structure-certificate witness,
symmetry group, reconstruction bridge, quantum-theory witness, Yang–Mills existence claim, or
mass-gap claim is present.

Primary OS-I and correcting OS-II article scans, Wightman's 1956 paper, and the corrected Princeton
edition of Streater–Wightman are hash-pinned with exact text extractions. Load-bearing OS-II and
Wightman-axiom pages were visually verified. Wilson 1974 and Osterwalder–Seiler 1978 lattice sources
are also pinned and visually checked without identifying finite-cutoff results with the continuum
target. Wilson's 1969 OPE paper and the independent Gross–Wilczek/Politzer 1973 asymptotic-freedom
papers are pinned as observable and ultraviolet-consistency evidence. Source acquisition constructs
no Euclidean, lattice, observable, renormalized, or Wightman theory.
