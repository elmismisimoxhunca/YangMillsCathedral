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
  groups, and visible matter contributions.
- pp. 1344–1346: the conclusions concern perturbative ultraviolet behavior and logarithmic
  corrections, not a nonperturbative construction or infrared mass gap.

## Formalization decision

This source controls only a perturbative ultraviolet consistency interface: an explicit scale/running
coupling, beta-function convention, ultraviolet limit, and observable/Green-function asymptotics with
quantified logarithmic or remainder behavior. Gauge group and matter dependence must remain visible.

No finite-order coefficient or slogan “asymptotically free” may stand in for a full continuum quantum
theory, OS/Wightman reconstruction, existence, confinement, or mass gap.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256: `fc51fe7db8f9c9db4b39da7c97b022c3bbf84fa0e7bdfe2ac037dac25967da99`.
- `SHA256SUMS.txt` verifies both retained artifacts.
