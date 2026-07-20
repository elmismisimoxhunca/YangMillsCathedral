# Streater–Wightman axiomatic QFT source record

## Identity

- R. F. Streater and A. S. Wightman, **PCT, Spin and Statistics, and All That**.
- Princeton University Press paperback with revised preface and corrections, 2000.
- Originally published by W. A. Benjamin in 1964; later printings include corrections.
- ISBN-10: `0-691-07062-8`.
- ISBN-13: `978-0-691-07062-9`.
- Clay/Jaffe–Witten reference [45] cites the original 1964 edition.
- Retained file: `pct_spin_statistics_all_that.pdf`, 218 PDF pages.
- Text extraction: `pct_spin_statistics_all_that.txt`, produced by `pdftotext -layout`.

## Artifact provenance

The scan was supplied under `/projects/` with a third-party filename. Its front matter identifies the
Princeton edition, authors, publication history, ISBNs, and copyright. The relevant pages were
rendered and visually checked. The scan is therefore authoritative book content, but its byte origin
is not represented as a direct Princeton publisher download.

## Load-bearing visually verified locators

Printed pages and section numbers are authoritative; text lines refer to the retained extraction.

- Printed p. 9, §1-3; PDF page 19; extraction lines 494–528, equations `(1-4)`–`(1-6)`:
  - fixes the four-dimensional mostly-minus scalar product;
  - defines Lorentz transformations as invertible linear spacetime maps preserving it;
  - records closure and inverse at the source level.
- Printed p. 10; PDF page 20; extraction lines 529–575, equations `(1-7)`–`(1-9)`:
  - classifies components by `det Λ` and the sign of `Λ⁰₀`;
  - calls determinant-one transformations proper and positive-time-component transformations
    orthochronous;
  - exhibits time and space inversion as excluded components.
- Printed p. 12; PDF page 22; extraction lines 596–624, equations `(1-14)`–`(1-15)`:
  - defines the determinant-one `2 × 2` matrix action on real four-vectors;
  - states `Λ(-A) = Λ(A)` and that `Λ(A) = Λ(B)` implies `A = ±B`;
  - identifies `A ↦ Λ(A)` as a homomorphism from `SL(2,ℂ)` onto the restricted Lorentz group.
  The retained page was rendered and visually checked for the two-to-one statement.
- Printed p. 13; PDF page 23; extraction lines 642–668:
  - defines the complex Lorentz group by the complexified form-preservation law;
  - separates determinant `+1` and `-1` components and calls the former proper;
  - states that `1` and `-1` are connected in the proper complex component and prints an explicit
    connecting curve.
- Printed p. 14; PDF page 24; extraction lines 669–685, equations `(1-19)`–`(1-20)`:
  - presents the `SL(2,ℂ) × SL(2,ℂ)` realization of proper complex Lorentz transformations;
  - prints their multiplication action on complex spacetime vectors.
- Printed p. 14; PDF page 24; extraction lines 686–706, equations `(1-22)`–`(1-23)`:
  - defines inhomogeneous/Poincaré elements as translation–Lorentz pairs;
  - gives affine action `x ↦ Λx + a` and the semidirect-product multiplication law;
  - identifies the inhomogeneous `SL(2,ℂ)` group used later for spinorial representations.
  Combined with the exact `A = ±B` result on printed p. 12, this motivates—but does not state
  verbatim—the project's multiplicative identification of the affine cover kernel with literal
  complex signs.
- Printed p. 92; PDF page 102; extraction lines 3890–3934:
  - states the SNAG representation `U(a,1) = ∫ exp(i p·a) dE(p)` for translations;
  - identifies `E` as a projection-valued measure on momentum space;
  - prints intersection multiplicativity, countable additivity on disjoint Borel sets, and
    normalization `E(ℝ⁴) = 1`;
  - identifies absence from the physical energy-momentum spectrum with `E(S) = 0` and notes that
    Lorentz covariance permits discrete point spectrum only at `p = 0`.
  The retained PDF page was visually checked; this is the primary source anchor for the project's
  joint translation-PVM surface rather than an inference from finite-cutoff lattice data.
- Printed p. 96, §3-1; PDF page 106; extraction lines 4058–4109: fields are operator-valued
  distributions and the axioms for fields and field theory begin.
- Printed p. 97; PDF page 107; extraction lines 4110–4134, axiom `0`:
  - states live in a separable Hilbert space;
  - there is a continuous unitary representation of the inhomogeneous `SL(2,ℂ)`/Poincaré cover;
  - translations have energy-momentum generators;
  - the energy-momentum spectrum lies in the closed forward cone;
  - there is an invariant vacuum unique up to phase.
- Printed p. 98; PDF page 108; extraction lines 4137–4181, axiom `I`:
  - smeared fields and adjoints share a dense invariant domain containing the vacuum;
  - matrix elements are tempered distributions.
- Printed p. 99; PDF page 109; extraction lines 4183–4217, axiom `II`: covariance of fields under
  the same Poincaré representation on the common domain.
- Printed p. 100; PDF page 110; extraction lines 4222–4257, axiom `III`:
  - local (anti)commutativity at spacelike separation on the common domain;
  - explicitly defines the adjoint field by `φ*(g) = [φ(conj g)]*` (the conjugation bar is visually
    present in the retained scan although imperfectly represented by text extraction).
- Printed pp. 100–101; extraction lines 4258–4304: trivial constant fields are explicitly noted and
  a field theory is required to have a vacuum cyclic for polynomials in smeared fields.
- Printed p. 63, §2-4; PDF page 73; extraction lines 2733–2752:
  - defines the extended tube as the union of all simultaneous proper-complex-Lorentz images of the
    ordinary tube;
  - prints the exact existential orbit characterization and transformation-law setup.
- Printed pp. 65–66; PDF pages 75–76; extraction lines 2822–2863, lemma and Theorem 2-11:
  - states the path lemma used for single-valuedness;
  - states single-valued holomorphic continuation to the extended tube and proper-complex-Lorentz
    covariance. The present Lean geometry uses the domain definition only; the analytic theorem
    remains a separate obligation.
- Printed p. 118; PDF page 128; extraction lines 4978–5007, reconstruction theorem uniqueness:
  - any other scalar field theory with the same vacuum expectation values is unitarily equivalent;
  - the unitary maps the vacuum, intertwines the Poincaré representations and smeared fields, and
    transports the common domain exactly.
  The retained page was rendered and visually checked. It is the source anchor for heterogeneous
  Wightman-realization unitary equivalence, not a claim that the project has constructed either
  realization or the intertwiner.
- Printed p. 111; extraction lines 4671–4709: cluster decomposition and the text's threshold
  description of a mass gap. This passage is supporting physical semantics only; it does not replace
  the required joint translation-PVM definition.

## Formalization decision

This source controls the Minkowski/Wightman acceptance surface: Hilbert space, one physical
translation/Poincaré representation, common invariant domain, operator-valued tempered
distributions, covariance, locality, forward-cone spectrum, invariant unique vacuum, and cyclicity.
Those requirements must remain connected to the same representation and domain. When the scalar
Wightman field is used alongside the separately sourced gauge-invariant local-observable family, an
explicit project coherence surface identifies it with that family's existing nontrivial label and
identifies its adjoint with the exact involutive adjoint label. This anti-disconnection requirement
is a formalization strengthening, not a new existence claim from the book.

The affine Poincaré target now carries the topology induced by its pointwise Lorentz action and
translation coordinate. `ProperOrthochronousPoincareCoverData` requires the existing exact
surjective lift projection to satisfy Mathlib's genuine covering-map predicate. Printed p. 12 states
that the homogeneous map identifies exactly `A` and `-A`; the strengthened double-cover interface
therefore requires every affine fiber to be equivalent to `Fin 2`. Equation `(1-22)` also controls a
named target group interface: its identity and multiplication must have the exact affine actions,
and it must be topological for the canonical coordinate topology; the cover projection then derives
as a bundled homomorphism. `complexSignSubgroup` constructs the literal complex-unit subgroup
`{1,-1}`. The exact identity fiber's `Fin 2` equivalence then derives, rather than separately
requires, a multiplicative equivalence of the projection kernel with these signs; order-two kernel
centrality is derived as well. Relative to any chosen lift, every point in its fiber is then proved
to be that lift or its distinct negative-sign partner. This names the abstract group kernel and gives
relative sign labels, not a matrix carrier, canonical global section, or matrix `A ↦ -A`
identification. For a scalar Wightman realization indexed definitionally by that exact cover,
`ScalarWightmanAxiomSurfaceData.unitary_eq_refl_of_projection_eq_identity` derives that every
identity-projecting lift acts trivially: covariance fixes field/adjoint words, vacuum invariance
fixes their base vector, and cyclicity plus continuity reaches the full Hilbert space. This is a
project derivation from axioms `0`–`III`, not a separately printed theorem. The cover interfaces
remain uninhabited and do not construct the book's inhomogeneous `SL(2,ℂ)` or derive
proper-orthochronous closure.

The checker follows the book's explicit printed-p. 92 SNAG/PVM presentation rather than stopping
at the generator-level summary on printed p. 97. Energy, momentum, invariant mass, the vacuum
projection, the energy-coordinate Hamiltonian spectral view, and the mass-gap predicate must all use
that same joint spectral object. Connecting the
Clay gap semantics and exact vacuum line to this PVM is a formalization strengthening intended to
block disconnected Hamiltonians, vacuum-only spectra, or surrogate gaps.

`ScalarWightmanFixedLiftUnitaryEquivalence` formalizes the printed-p. 118 uniqueness relation
between two already supplied scalar realizations over the same exact Poincaré lift: group transport
is the identity, and one Hilbert unitary handles the representation, vacuum, common domain, field,
and adjoint. A more general project transport relation can compare explicitly equivalent lift
carriers, but that generalization is not attributed verbatim to the source. Neither interface asserts
that reconstructed outputs or intertwiners exist.

No Wightman theory, vacuum, field, PVM, existence proof, or mass-gap witness is supplied by retaining
this source.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256:
  `98dc436e383b4e50ef3b6d82f3948b912b64c67b2d6e64bef6dcf7f9feb8012f`.
- `SHA256SUMS.txt` verifies the PDF and exact text extraction.
