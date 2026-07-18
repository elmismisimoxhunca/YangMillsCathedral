# Wilson lattice gauge source record

## Identity

- Kenneth G. Wilson, **Confinement of Quarks**.
- *Physical Review D* **10** (1974), 2445–2459.
- DOI: <https://doi.org/10.1103/PhysRevD.10.2445>.
- APS record: <https://link.aps.org/doi/10.1103/PhysRevD.10.2445>.
- Retained file: `confinement_of_quarks.pdf`, 15 PDF pages.
- Text extraction: `confinement_of_quarks.txt`, produced by `pdftotext -layout`.

## Artifact provenance

The PDF was supplied under `/projects/`. It has `%PDF-1.4` magic, is unencrypted, carries APS title,
author, and copyright metadata, and contains printed pp. 2445–2459. The first PDF page also contains
the tail of the preceding journal article above Wilson's title; the Wilson article itself is complete.
The load-bearing pages were rendered and visually checked.

## Load-bearing locators

- p. 2445; PDF page 1; extraction lines 13–45: the model is a four-dimensional Euclidean lattice
  gauge theory with exact lattice gauge invariance, compact/angular gauge variables, a
  strong-coupling expansion, and an explicit warning that the strong-coupling limit lacks Lorentz
  or Euclidean invariance.
- pp. 2448–2450, §III.A–B; PDF pages 4–6; extraction lines 241–365:
  - lattice sites and link variables are introduced;
  - local gauge transformations and gauge-invariant link combinations are displayed;
  - the periodic lattice gauge-field action appears in equation (3.9);
  - equations (3.10)–(3.12) compare it with the continuum action as lattice spacing tends to zero;
  - the continuum limit is explicitly described as a separate, renormalization-sensitive problem.
- Later §§III–IV extend the construction to non-Abelian compact groups and organize the
  strong-coupling expansion by lattice paths and surfaces.

## Formalization decision

This source controls the optional lattice-regulator surface: oriented links, group-valued link
variables, plaquette holonomy, local vertex gauge transformations, Wilson action, loop observables,
and lattice dimension/cutoff data.

The lattice carrier is not the continuum Euclidean theory. A finite-cutoff witness may enter the
checker only through an explicit scaling/continuum-limit bridge that preserves interpreted
observables and the required continuum axioms. Wilson's own caveats about lost continuum symmetry
and the difficulty of the limit are retained as anti-vacuity constraints.

No confinement theorem, continuum limit, Yang–Mills existence theorem, or four-dimensional mass gap
is imported from this paper.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256:
  `6eadfb8d3e3cd217c379623857c6e1ab31e7298edbfd2c18f7ea93d17b49582c`.
- `SHA256SUMS.txt` verifies the PDF and exact text extraction.
