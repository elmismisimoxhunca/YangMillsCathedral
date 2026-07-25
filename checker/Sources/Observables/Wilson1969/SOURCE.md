# Wilson operator-product source record

## Identity

- Kenneth G. Wilson, **Non-Lagrangian Models of Current Algebra**.
- *Physical Review* **179** (1969), 1499–1512.
- DOI: <https://doi.org/10.1103/PhysRev.179.1499>.
- Retained APS article: `non_lagrangian_current_algebra.pdf`, 14 PDF pages.
- Exact `pdftotext -layout` extraction: `non_lagrangian_current_algebra.txt`.

## Provenance and load-bearing locators

The supplied `/projects/wilson1969.pdf` has `%PDF-1.4` magic, APS metadata, and visibly printed
journal/title/author/pages. Printed pp. 1499–1501 were rendered and visually checked.

- p. 1499; PDF page 1; extraction lines 6–35: products at coincident points are not assumed to have
  meaning; products of local fields at short separation instead have expansions with singular
  coefficient functions multiplying local fields.
- p. 1500, §II, equations (2.1)–(2.4); PDF page 2; extraction lines 117–166: the two-field OPE has an
  infinite local-field family, only finitely many terms contributing to a fixed order, and a stated
  domain as matrix elements between fixed states; covariance and time-ordered products are discussed.
- p. 1501, §III; PDF page 3; extraction lines 179–260: scale transformations and field dimensions
  organize homogeneous short-distance coefficient behavior.
- p. 1502; PDF page 4; extraction lines 261–290: fields are ordered by dimension, with finitely many
  linearly independent local fields below each finite dimension bound and finitely many singular
  coefficient functions.

## Formalization decision

This historical primary source motivates a typed local-observable/OPE interface with separated
operator labels, coefficient distributions, local fields, state/matrix-element domains, truncation
or remainder control, covariance, and short-distance/scaling parameters. A bare binary multiplication
operation is not an OPE, and coincident-point products cannot be smuggled in definitionally.

Wilson's model assumptions are not accepted as a nonperturbative Yang–Mills construction. Future Lean
requirements must state their convergence/asymptotic and domain semantics explicitly and connect
observables to the same quantum theory used for reconstruction and spectral claims. The basic
curvature-squared interpretation is now connected explicitly to the weak OPE: the ordered `F² × F²`
input must have a nonzero coefficient and nonzero selected local-field matrix element already at
zeroth order. This is a project anti-disconnection requirement, not a coefficient calculation or a
claim printed by Wilson for nonperturbative four-dimensional Yang–Mills.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- PDF SHA-256: `5afdadea273bef2d23db7e53465006197f38a574e7554ff1b40ec8281e91aca5`.
- `SHA256SUMS.txt` verifies both retained artifacts.
