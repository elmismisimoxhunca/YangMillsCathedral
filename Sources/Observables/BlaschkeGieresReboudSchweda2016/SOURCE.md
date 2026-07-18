# Gauge-theory energy-momentum tensor source record

## Identity

- Daniel N. Blaschke, François Gieres, Méril Reboud, and Manfred Schweda,
  **The Energy-Momentum Tensor(s) in Classical Gauge Theories**.
- arXiv:1605.01121v2 [hep-th], 6 July 2016.
- Stable source: <https://arxiv.org/abs/1605.01121>.
- Retained arXiv PDF: `energy_momentum_tensors_gauge_theories.pdf`, 34 PDF pages.
- Exact `pdftotext -layout` extraction: `energy_momentum_tensors_gauge_theories.txt`.

## Provenance and load-bearing locators

The retained file has PDF magic and arXiv title/author/version metadata. PDF pages 1, 3, 5, 8,
and 9 (respectively the unnumbered title page and printed pp. 2, 4, 7, and 8) were rendered and
visually checked for the title/abstract, component interpretation, conservation/charge formula,
symmetric/gauge-invariant improved-tensor discussion, and load-bearing equation `(2.11)`. It is an authoritative
review used to define the standard classical gauge-theory content of the word “stress tensor”; it
is not evidence for existence of a quantum Yang–Mills theory.

- Abstract, PDF p. 1 (unnumbered title page), extraction lines 38–49: the improved non-Abelian
  gauge-field energy-momentum tensor is gauge invariant and symmetric.
- §2 opening and §2.1.1, printed pp. 3–4, PDF pp. 4–5, extraction lines 180–239: translation
  invariance yields a rank-two energy-momentum current obeying local conservation
  `∂_μ T^{μν}=0`; spatial integrals of `T^{0ν}` give conserved energy-momentum charges and generate
  spacetime translations, with gauge subtleties explicitly noted.
- §2.1.3, printed pp. 5–6, PDF pp. 6–7, extraction lines 280–340: the pure Yang–Mills canonical
  tensor is locally conserved but needs improvement for gauge invariance and symmetry; symmetry is
  related to the mechanical angular-momentum current.
- §2.2.1, equation `(2.11)`, printed p. 8, PDF p. 9, extraction lines 430–470: the improved pure
  Yang–Mills tensor is explicitly stated to be conserved, symmetric, and gauge invariant; in four
  dimensions it is classically traceless.

## Formalization decision

Clay/Jaffe–Witten requires a stress tensor but does not print component axioms. The Lean checker
uses this review for symmetry and weak local conservation, while Streater–Wightman supplies the
quantum common-domain, adjoint, covariance, locality, and tempered-distribution semantics. The
project chooses an explicit contravariant rank-two Lorentz-component convention and records that
choice in the declaration-level source map.

The present checker deliberately does **not** infer a quantum stress tensor from the classical
formula, impose classical tracelessness on the quantum theory, or claim the trace anomaly. The
review's charge formula motivates a future Ward/generator bridge to the exact physical translation
representation/PVM; that bridge remains open.

## Artifact chain

- Retrieval time: `FETCH_TIMESTAMP.txt`.
- `SHA256SUMS.txt` verifies the retained PDF and exact text extraction.
