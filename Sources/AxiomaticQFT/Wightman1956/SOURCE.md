# Wightman vacuum-expectation-value source record

## Identity

- A. S. Wightman, **Quantum Field Theory in Terms of Vacuum Expectation Values**.
- *Physical Review* **101** (1956), 860–866.
- DOI: <https://doi.org/10.1103/PhysRev.101.860>.
- APS record: <https://link.aps.org/doi/10.1103/PhysRev.101.860>.
- Retained file: `vacuum_expectation_values.pdf`, 7 pages.
- Text extraction: `vacuum_expectation_values.txt`, produced by `pdftotext -layout`.

## Artifact provenance

The PDF was supplied under `/projects/`. It has `%PDF-1.4` magic, is unencrypted, and its embedded
metadata carries the title, author, DOI/URL keywords, copyright creator, producer, and dates. The
journal, volume, issue, date, and page are visibly printed in the rendered article header rather than
stored as dedicated metadata fields. The complete article was successfully rendered and visually
checked, and is retained as the primary artifact.

## Load-bearing locators

- p. 860, opening and §1; PDF page 1; extraction lines 8–28:
  - vacuum expectation values are distributions;
  - Lorentz covariance, absence of negative-energy states, positivity, analyticity, and local
    commutativity are identified as structural constraints;
  - the paper explicitly says it does not show that an interacting example exists.
- p. 860, equations (1)–(5): covariance of the scalar field and vacuum expectation values under the
  inhomogeneous Lorentz group, including invariance of the vacuum.
- pp. 860–862, §§2–4: consequences of Lorentz invariance and absence of negative-energy states,
  including analyticity and spectral-support information.
- pp. 864–866: reconstruction of a neutral scalar field from vacuum expectation values satisfying
  the stated conditions.

## Formalization decision

This original paper supports the separation between a family of vacuum expectation distributions
and a reconstructed field theory, together with covariance, positivity, spectral support,
analyticity, locality, and reconstruction coherence. It is restricted to a neutral scalar field and
does not by itself provide the full gauge-theory acceptance interface; the later
Streater–Wightman axioms control the general Wightman surface.

The paper's explicit nonexistence disclaimer is preserved: a reconstruction implication from data
satisfying axioms is not a construction of nontrivial Yang–Mills data.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256:
  `ac354c65e81cd328b25e682ba19bad8fd5b1825da2110aaf3ca73388cf338c25`.
- `SHA256SUMS.txt` verifies the PDF and exact text extraction.
