# Quantum gauge-theory trace-anomaly source record

## Identity

- John C. Collins, Anthony Duncan, and Satish D. Joglekar,
  **Trace and Dilatation Anomalies in Gauge Theories**.
- Published in *Physical Review D* **16** (1977), 438–449.
- DOI: <https://doi.org/10.1103/PhysRevD.16.438>.
- Preprint report `COO-2220-88`, October 1976.
- Stable KEK scan: <https://lib-extopc.kek.jp/preprints/PDF/1977/7701/7701010.pdf>.
- Retained scan: `trace_dilatation_anomalies_gauge_theories.pdf`, 22 PDF pages.
- Exact `pdftotext -layout` extraction: `trace_dilatation_anomalies_gauge_theories.txt`.

The retained KEK artifact is a library scan of the authors' preprint, not a retyped secondary
source. Its title, authors, report number, abstract, and equations agree with the published article
identity recorded by DOI/Crossref and INSPIRE (`Collins:1976yq`).

## Load-bearing locators

The title/abstract on PDF p. 1 and the equation pages on PDF pp. 9–10 were rendered and visually
checked against the scan.

- Abstract, PDF p. 1, extraction lines 16–40: the trace anomaly in an interacting non-Abelian gauge
  theory involves precisely the gauge-variant operators that mix with the naive trace under
  renormalization; the trace becomes soft on shell exactly at a beta-function fixed point.
- §III, preprint pp. 17–18, PDF p. 9, equations `(3.16)`–`(3.19)`, extraction lines 757–815: the
  renormalized trace contains the gauge-invariant normal product
  `O₁ = -1/4 F^a_{μν} F_a^{μν}` together with the complete mixing family of gauge-noninvariant,
  ghost, fermion-equation, and mass operators. Equation `(3.19)` is the arbitrary-momentum
  renormalized anomaly before physical/on-shell reduction.
- §III, preprint p. 19, PDF p. 10, equations `(3.20)`–`(3.21)`, extraction lines 776–837: with
  physical external wave functions, on shell and at nonzero momentum, the ghost and
  equation-of-motion terms vanish. The full trace reduces to the mass term plus
  `β(g_R)/(2 g_R) N[F^a_{μν}F_a^{μν}]`. In massless pure Yang–Mills only the displayed `F²` term
  remains.
- §IV opening, preprint p. 20, PDF p. 10, equations `(4.1)`–`(4.3)`, extraction lines 839 onward:
  the arbitrary-momentum proof uses the period terminology “BRS” and keeps the unphysical mixing
  structure visible rather than treating the simple physical formula as an unrestricted bare
  operator equality.

## Formalization decision and normalization boundary

The checker defines the stress trace by contracting the already designated stress components with
its mostly-minus metric; it does not create a disconnected trace label. The quantum trace-anomaly
interface is restricted to designated physical weak matrix elements and targets the exact existing
renormalized `F²` label.

Collins–Duncan–Joglekar place the coupling in the field strength and obtain `β(g)/(2g) F²` after the
physical/on-shell reduction. The project's classical geometric curvature is coupling-independent and
its action coefficient is `(4 g²)⁻¹`. Rewriting the source formula as `β(g)/(2g³)` for that outer-
coupling convention requires a field-rescaling/renormalized-operator normalization bridge that the
project has not proved. Therefore the first canonical interface retains an explicit nonzero anomaly
coefficient tied to the same beta function and reference coupling only through a separately stated
normalization obligation; it does **not** silently choose either power of `g`.

The paper proves a perturbative renormalized insertion formula, not existence of a four-dimensional
Yang–Mills theory, a stress tensor in the project's Wightman representation, or a mass gap. The Lean
record remains supplied and uninhabited.

## Artifact chain

- `FETCH_TIMESTAMP.txt` records retrieval time.
- `SHA256SUMS.txt` verifies the retained PDF and exact text extraction.
