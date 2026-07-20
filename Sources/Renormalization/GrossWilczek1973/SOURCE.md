# Gross–Wilczek asymptotic-freedom source record

## Identity

- David J. Gross and Frank Wilczek, **Ultraviolet Behavior of Non-Abelian Gauge Theories**.
- *Physical Review Letters* **30** (1973), 1343–1346.
- DOI: <https://doi.org/10.1103/PhysRevLett.30.1343>.
- Retained APS article: `ultraviolet_behavior_nonabelian.pdf`, 4 PDF pages.
- Exact `pdftotext -layout` extraction: `ultraviolet_behavior_nonabelian.txt`.

## Provenance and load-bearing locators

The supplied `/projects/gross1973.pdf` has `%PDF-1.4` magic and APS metadata. Printed pp. 1343–1345
were rendered and visually checked.

- p. 1343; PDF page 1; extraction lines 1–49: equations (1)–(4) formulate ultraviolet scaling through
  the renormalization group, running coupling, beta function, and fixed points at nonexceptional
  Euclidean momenta.
- p. 1344; PDF page 2; extraction lines 69–150: equations (5)–(9) give the Yang–Mills setup, the
  negative leading pure-gauge beta function, its ultraviolet limit for semisimple non-Abelian gauge
  groups, and visible matter contributions. The retained PDF page was visually checked for equation
  (8), `βᵥ(g) = -(g³/16π²)(11/3) C₂(G) + O(g⁵)`, and the immediately following convention
  `∑_{b,c} C_{abc} C_{dbc} = C₂(G) δ_{ad}`; extraction lines 131–140 locate the OCR-degraded display.
- pp. 1344–1346: the conclusions concern perturbative ultraviolet behavior and logarithmic
  corrections, not a nonperturbative construction or infrared mass gap.

## Formalization decision

This source controls only a perturbative ultraviolet consistency interface: an explicit scale/running
coupling, beta-function convention, ultraviolet limit, and observable/Green-function asymptotics with
quantified logarithmic or remainder behavior. Gauge group and matter dependence must remain visible.

`AdjointCasimirNormalizationData` states the displayed basis-level Casimir convention on the exact
tangent Lie bracket and the invariant pairing used by the classical action.
`GroupNormalizedOneLoopBetaData` then identifies the preliminary running coupling's positive leading
coefficient with `11 C₂(G)/(3·16π²)`. `ClassicalRunningCouplingReferenceData` additionally chooses
an explicit ultraviolet logarithmic reference scale and equates the same running coupling there
with the outer coupling in the project's classical action. This records the convention obtained by
rescaling the source's coupling-inside-curvature presentation to an outer `1/(4g²)` coefficient; no
connection-level field-rescaling theorem is claimed. The basis, Casimir identity, and equalities are
supplied acceptance data; the `O(g⁵)` remainder is not calculated or represented by this interface.

No finite-order coefficient or slogan “asymptotically free” may stand in for a full continuum quantum
theory, OS/Wightman reconstruction, existence, confinement, or mass gap.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256: `fc51fe7db8f9c9db4b39da7c97b022c3bbf84fa0e7bdfe2ac037dac25967da99`.
- `SHA256SUMS.txt` verifies both retained artifacts.
