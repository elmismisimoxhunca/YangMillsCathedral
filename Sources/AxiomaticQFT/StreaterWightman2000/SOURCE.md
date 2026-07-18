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
- Printed p. 100; PDF page 110; extraction lines 4222–4257, axiom `III`: local (anti)commutativity at
  spacelike separation on the common domain.
- Printed pp. 100–101; extraction lines 4258–4304: trivial constant fields are explicitly noted and
  a field theory is required to have a vacuum cyclic for polynomials in smeared fields.
- Printed p. 111; extraction lines 4671–4709: cluster decomposition and the text's threshold
  description of a mass gap. This passage is supporting physical semantics only; it does not replace
  the required joint translation-PVM definition.

## Formalization decision

This source controls the Minkowski/Wightman acceptance surface: Hilbert space, one physical
translation/Poincaré representation, common invariant domain, operator-valued tempered
distributions, covariance, locality, forward-cone spectrum, invariant unique vacuum, and cyclicity.
Those requirements must remain connected to the same representation and domain.

The checker will strengthen the book's generator-level presentation by requiring an explicit joint
translation spectral/PVM interface. Energy, momentum, invariant mass, the vacuum projection, and
the mass-gap predicate must all be derived from that same joint spectral object. This strengthening
is a formalization decision intended to block disconnected Hamiltonians or surrogate spectra.

No Wightman theory, vacuum, field, PVM, existence proof, or mass-gap witness is supplied by retaining
this source.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256:
  `98dc436e383b4e50ef3b6d82f3948b912b64c67b2d6e64bef6dcf7f9feb8012f`.
- `SHA256SUMS.txt` verifies the PDF and exact text extraction.
