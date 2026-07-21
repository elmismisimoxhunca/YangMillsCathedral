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

PDF p. 27 / printed p. 601 was independently inspected on 2026-07-21 for Definition 8.1 and the
opening statements of Definitions 8.3/8.4 and Theorem 8.5. The page visibly fixes the infinite
nearest-neighbor directed graph on `εℤ²`, requires approximating graph edges to be paths in that
graph, gives surjections on bonds and bounded regions, requires symmetric-difference area of order
`ε`, and preserves admissible boundary sums. The Lean layer formalizes exact positive-spacing
nearest-neighbor path geometry and an uninhabited Definition 8.1 family on the project's
conservative embedded-arc strengthening. Driver-permitted one-edge loop incidence requires
subdivision. The interface has surjective edge/face maps, uniform explicit symmetric-difference area
order, and universal exact facewise boundary-presentation transport. Actions, lattice
measures, and convergence remain explicit debt.

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
