# Osterwalder–Seiler lattice gauge source record

## Identity

- Konrad Osterwalder and Erhard Seiler, **Gauge Field Theories on a Lattice**.
- *Annals of Physics* **110** (1978), 440–471.
- DOI: <https://doi.org/10.1016/0003-4916(78)90039-8>.
- Retained file: `gauge_field_theories_lattice.pdf`, 32 PDF pages.
- Text extraction: `gauge_field_theories_lattice.txt`, produced by `pdftotext -layout`.

## Artifact provenance

The PDF was supplied under `/projects/`. It has `%PDF-1.3` magic, is unencrypted, and its visible
article header, authors, journal, volume, pages, date, and publisher identifier match the cited work.
The PDF metadata title is the publisher PII rather than the article title. The complete scan was
successfully text-extracted and the load-bearing pages were rendered and visually checked.

## Load-bearing locators

- p. 440; PDF page 1: the abstract states a rigorous nonperturbative lattice approximation,
  verification of physical positivity of Schwinger functions, a positive self-adjoint transfer
  matrix, infinite-volume existence/analyticity at strong coupling, Wilson confinement, and a Higgs
  mechanism in lattice gauge theories. These are lattice results, not continuum-4D existence.
- pp. 442–443; PDF pages 3–4; extraction lines 116–176:
  - directed bonds and plaquettes are defined;
  - compact-group link configurations and plaquette conjugacy classes are introduced;
  - the lattice Yang–Mills action, Gibbs measure, finitely supported local observables, local gauge
    transformations, and gauge invariance are specified.
- p. 448; PDF page 9; Theorem 2.1; extraction lines 361–433: reflection positivity
  `⟨(ΘF) · F⟩ ≥ 0` is proved for gauge-invariant positive-time observables; `Θ` is antilinear. This
  finite-cutoff lattice positivity must remain distinct from continuum OS data.
- p. 455; PDF page 16; Theorem 3.5; extraction lines 701–726: sufficiently strong coupling gives
  uniform exponential clustering for finitely supported bond observables, described as a lattice
  mass gap. The theorem refers to earlier work for the proof.

## Formalization decision

This source controls finite-cutoff lattice gauge invariance, local observables, reflection
positivity, transfer-matrix compatibility, and strong-coupling exponential clustering.

Theorem 3.5 is not the Clay mass-gap requirement: it is a strong-coupling lattice statement and does
not by itself supply a continuum limit, physical Poincaré translations, a joint translation PVM, or
a four-dimensional Wightman theory. Separate bridge records must carry lattice observables and
reflection positivity into any proposed continuum OS surface before reconstruction.

No lattice witness is required by the canonical continuum acceptance record; the lattice route is an
optional construction/regulator interface.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256:
  `58861ff0dfbc7f2f6af3ce178f2b8ac82ae4d560b8cdde8e3f988fa891b67547`.
- `SHA256SUMS.txt` verifies the PDF and exact text extraction.
