# Source record

## Identity

- **YM2: Continuum Expectations, Lattice Convergence, and Lassos**.
- Author(s): Bruce K. Driver.
- Publication: Communications in Mathematical Physics 123 (1989), 575–616.
- Identifier: 10.1007/BF01218586.
- Retained PDF: `ym2_continuum_lattice_lassos.pdf` (42 PDF pages).
- Exact native extraction: `ym2_continuum_lattice_lassos.txt`, produced with `pdftotext -layout`.

## Audit role

Rigorous two-dimensional continuum expectations, lattice convergence, holonomy/lasso observables, and source-specific consistency evidence.

## Ingestion and locator status

The PDF was supplied by the user in the 2026-07-19 literature bundle, signature-checked, copied
without byte changes, hash-manifested, and text-extracted. Ingestion does not by itself make every
statement load-bearing: exact printed-page/equation/theorem locators and any OCR-sensitive formulas
must be visually checked and entered in `docs/SUPPLIED_SOURCE_INGESTION_AUDIT.md` and
`docs/SOURCE_MAP.md` before supporting a canonical physical declaration. Hashes verify identity of
the retained bytes, not interpretation.

## Visual adjudication of load-bearing admissibility text

The native PDF was independently inspected at PDF p. 6 / printed p. 580 and PDF p. 9 / printed
p. 583 on 2026-07-21. Definition 3.1 visibly says that a horizontal path has the form
`(t, σ(t))` for a **continuous** real function. Definition 3.8 visibly says that an admissible
continuous planar curve can be broken into finitely many vertical line segments and
`C¹`-horizontal curves. The superscript `1`, hyphenation, and finite-piece wording agree with the
retained native extraction. The project's affine-speed piece presentation is a documented
parameterization strengthening, not wording attributed verbatim to Driver.

PDF p. 17 / printed p. 591 was independently inspected on 2026-07-21 for Definitions 6.1/6.2.
Definition 6.1 visibly requires: each curve piecewise `C¹`; finitely many connected components of
`ℝ² \ (S ∪ {x-axis})`; each curve admissible under Definition 3.8; and no immediate retracing after
arc-length parameterization. Definition 6.2 visibly requires a finite directed graph on a discrete
planar vertex set, bonds crossing one another or themselves only at endpoints, endpoint-map
coherence, and an admissible collection of bond curves. These conditions agree with the retained
native extraction.

PDF pp. 15–16 / printed pp. 589–590 were independently inspected on 2026-07-21 for
Definition 5.1 and the exact `D_T g` measure preceding Theorem 5.3. The pages visibly define a tree
as an orientation-stable bond subset with no nonempty closed path using distinct unoriented bonds;
connectedness is a separate strengthening, not part of the base tree condition. They visibly assign
identity point mass to tree bonds and Haar measure to all other underlying bond coordinates. The Lean
underlying-edge representation makes orientation stability automatic and formalizes exactly this
no-loop predicate and mixed finite product measure.

PDF p. 18 / printed p. 592 was independently inspected on 2026-07-21 for Definition 6.3 and
Theorem 6.4. The page visibly defines restricted gauge invariance by requiring the vertex gauge to
be the identity at the distinguished origin, states the area-indexed boundary-holonomy product-Haar
expectation formula, declares the right-hand side independent of all boundary-holonomy choices, and
separately states invariance under freezing any tree to the identity. The Lean general-boundary law
currently formalizes the exact conditional coordinate-zero restricted-gauge clause and quantifies
choice independence over the full structure of every valid simultaneous presentation, whose traces
are nonempty, pairwise disjoint, and maximal connected frontier subsets. The universal tree-
freezing strengthening now quantifies over every exact Definition 5.1 tree, uses the exact mixed
identity-Dirac/Haar product, and retains the unchanged face density and ambient expectation.

PDF p. 8 / printed p. 582 was independently inspected on 2026-07-21 for Proposition 3.5; the
visible formula confirms that traversing `σ` and then `τ` gives `P(τ)P(σ)`, fixing later traversal on
the left. PDF pp. 23–24 / printed pp. 597–598 were independently inspected the same day for
Definition 7.1, equations (7.1)–(7.4), and Theorem 7.2; continuity, positivity, class/inversion
symmetry, real Haar normalization, the vertical-plus-x-axis axial tree, plaquette products, delta
boundary conditions, free-boundary formulas, weak limits, boundary independence, and finite-cylinder
restriction were confirmed. No finite-volume measure is yet claimed by the current
plaquette-product layer.

PDF p. 27 / printed p. 601 was independently inspected on 2026-07-21 for Definition 8.1 and the
opening statements of Definitions 8.3/8.4 and Theorem 8.5. The page visibly fixes the infinite
nearest-neighbor directed graph on `εℤ²`, requires approximating graph edges to be paths in that
graph, gives surjections on bonds and bounded regions, requires symmetric-difference area of order
`ε`, and preserves admissible boundary sums. The Lean layer formalizes exact positive-spacing
nearest-neighbor path geometry and an uninhabited Definition 8.1 family on the project's
conservative embedded-arc strengthening. Driver-permitted one-edge loop incidence requires
subdivision. The interface has surjective edge/face maps, uniform explicit symmetric-difference area
order, and universal exact facewise boundary-presentation transport. Definition 8.3 is represented
by identifying the Villain action with the smooth strictly-positive real representative of the
unchanged semigroup density at `ε²`, requiring the exact Definition 4.7 `∂ₜQ = 1/2 ΔQ` chain, an initial-identity generated operator
semigroup, and the displayed convolution-kernel formula. Its full inherited action contract,
including the real Haar-integral normalization, and its normalized nonzero Haar-density plaquette
measure are derived. Definition 8.4 is represented by an actual continuous nonzero finite-
dimensional unitary matrix representation, its exact matrix-trace character, and positive source-
indexed normalizers tied to the unnormalized Haar integral; the complete inherited real action
contract is derived. Definition 7.1 is also packaged as one common action interface with exact
Villain/Wilson adapters and a separately labeled constant-one inhabitant. The exact infinite directed `εℤ²` bond carrier, reverse-inversion configurations, and
axial-tree-fixed measurable carrier are now explicit, including the vertical plus x-axis tree, exact
physical `(εm, εn)` embedding with signed `ε` steps, and a concrete nonidentity off-axis axial
configuration. Exact elementary plaquettes now retain a physically scaled closed counterclockwise
boundary, Driver's path-product order, and measurable everywhere-nonzero finite products of one
common action over their holonomies. Generic finite axial presentations now select orientation-
disjoint off-tree bonds, use injective measurable finite-support extensions, require every selected
plaquette's non-tree boundary bonds to be represented in one of the two coordinate orientations, and
define exact product-Haar partition functions and normalized finite density measures. The same
measurable extensions push these laws to normalized nonzero measures on the exact infinite axial
carrier with exact represented-coordinate marginals. An uninhabited nested projective-sequence contract additionally requires exact consecutive finite-law
pushforward and exhaustion of every off-tree bond and elementary plaquette. An infinite axial
probability interface has every finite-coordinate cylinder equal to the corresponding normalized
finite law. This is only projective cylinder infrastructure motivated by one conclusion of Theorem
7.2; it does not state uniqueness, exact square boxes, boundary-conditioned measures, weak limits,
or boundary independence. Exact positive-radius centered square-box plaquette sets and off-axis right-directed axial coordinate
sets now use the source `-n,…,n-1` / nonzero-row bounds, are literally nested with radius, and cover
every non-tree plaquette boundary orientation. The concrete box adapter now produces the generic
finite presentation using exact subtypes and a measurable extension that applies inversion to
reverse coordinates and identity elsewhere, with exact recovery/support/coverage. Compactness now bounds the exact box action weight and strict positivity/product-Haar normalization
prove its exact partition function finite and nonzero. Normalized finite-coordinate and same-
extension infinite-carrier box measures are constructed. Literal successor-radius coordinate/plaquette inclusions and measurable restriction are constructed;
an uninhabited projectivity datum states exact consecutive box-measure pushforward. The distinct source sets `Aₙ`, `Aₙ₋₁`, `Bₙ`, `B̄ₙ`, and frozen complement `Bₙᶜ` are now
represented exactly; nearest-neighbor geometry proves `Bₙ ⊆ B̄ₙ`, and radius-one hostile witnesses
prevent collapsing them. The finite Haar coordinates for (7.2) are now exact canonical right-directed off-axis horizontal
`Bₙ` bonds, and their measurable extension retains arbitrary axial boundary data on `Bₙᶜ` rather
than silently using the free identity extension. `J(Bₙ)` is now defined by literal plaquette-boundary incidence with `Bₙ` and proved exactly equal
to the complete `2n × 2n` box plaquette set, with hostile omission/disconnection probes. The exact (7.2) product density over this same `J(Bₙ)` is constructed on the boundary-retaining
extension. Strict positivity and compactness prove the boundary-dependent normalizer nonzero and
finite, yielding normalized nonzero finite-coordinate and infinite-carrier pushforward laws with
almost-sure `Bₙᶜ` retention. A genuinely-finite convergence predicate over measurable bounded-continuous tests, natural axial
product topology, and explicit all-continuous-test coverage bridge now support an uninhabited full
Theorem 7.2 axial contract: every boundary-conditioned sequence must
converge to one normalized measure, and that measure must equal every free finite law on all eligible
`Bₙ` observables as in (7.6). For §8, the punctured `ε → 0⁺` filter and exact spacing-indexed Villain/Wilson families retain the
unchanged `Q_{ε²}` chain or one fixed actual trace representation/normalizer; Theorem 8.10
faithfulness is actual representation injectivity. Each Definition 8.1 fine edge may now carry an exact nonempty ordered directed-bond word tied
source/target-wise to every consecutive certified path node; measurable later-on-the-left holonomy
constructs exact coarse restriction along the mapped fine edge. Driver's opening §2 and sign-sensitive equation (2.1) were visually adjudicated against PDF p. 3 /
printed p. 577 on 2026-07-21: `p_*` is the derivative at identity, injectivity is the standing
hypothesis, and the real form has the leading minus sign `-trace(p_*A p_*B)`. Lean writes the real
carrier as `-Re trace`; deriving vanishing imaginary part from differentiated unitarity remains part
of the future analytic chain. Driver's standing §2 representation chain now defines `p_*` as the exact identity `mfderiv` of one
smooth unitary matrix representation, requires its injectivity, and identifies the continuum
invariant pairing literally with `-Re tr(p_*X p_*Y)`. A dependent common-chain record now ties the same connected-group representation (globally faithful
and infinitesimally injective), Wilson normalization/actions, exact trace pairing, pairing Laplacian,
and unchanged selected continuum density/heat equation/kernel. The proof-required `B → VB` enlargement now has BC certificates on both graphs, literal coarse-edge
subdivision paths, the exact vertical/x-axis tree, total coverage excluding unrelated enlarged edges,
and measurable ambient-compatible coarse restriction. Adding the strip-independence/reflection
expectation law on this enlargement, inhabiting Theorem 7.2/projectivity, and formalizing Theorems
8.5/8.10
convergence over exact transport remain explicit debt.

PDF p. 21 / printed p. 595 was independently inspected on 2026-07-21 for Theorem 6.6.
The page visibly quantifies over a gauge-invariant function on the BC graph configuration space and
states that its continuum holonomy expectation equals integration of that function against one Haar
coordinate per bond weighted by the product, over bounded regions, of `Q` evaluated at geometric
region area and boundary holonomy. The proof visibly identifies this theorem as the BC special case
of Theorem 6.4. The project's measurable/integrable complex-valued qualification supplies the
formal hypotheses needed by the Bochner integral. The project retains both a Jordan-boundary
subclass and a separate strengthened embedded-arc BC interface with graph-theoretic bridge
multiplicity and the corresponding uninhabited face-product law. The latter conservatively requires
subdivision of Driver-permitted one-edge loop incidence; no graph or law instance is constructed.
The general non-BC cut-choice scope of Theorem 6.4 remains separate.

## Artifact chain

- `FETCH_TIMESTAMP.txt` records repository ingestion time.
- `SHA256SUMS.txt` covers the retained PDF and extraction.
