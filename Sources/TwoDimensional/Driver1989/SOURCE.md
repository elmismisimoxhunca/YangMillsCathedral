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
