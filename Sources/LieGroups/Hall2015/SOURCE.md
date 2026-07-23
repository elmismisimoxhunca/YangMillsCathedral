# Source record

## Identity

- **Lie Groups, Lie Algebras, and Representations, second edition**.
- Author(s): Brian C. Hall.
- Publication: Springer GTM 222 (2015).
- Identifier: 10.1007/978-3-319-13467-3.
- Retained PDF: `lie_groups_lie_algebras_representations.pdf` (452 PDF pages).
- Exact native extraction: `lie_groups_lie_algebras_representations.txt`, produced with `pdftotext -layout`.

## Audit role

Modern Lie-group source for compact groups, matrix groups, the compact matrix-group coefficient
Stone–Weierstrass argument, and the SL(2,C)/proper-Lorentz relationship.

## Ingestion and locator status

The PDF was supplied by the user in the 2026-07-19 literature bundle, signature-checked, copied
without byte changes, hash-manifested, and text-extracted. Ingestion does not by itself make every
statement load-bearing: exact printed-page/equation/theorem locators and any OCR-sensitive formulas
must be visually checked and entered in `docs/SUPPLIED_SOURCE_INGESTION_AUDIT.md` and
`docs/SOURCE_MAP.md` before supporting a canonical physical declaration. Hashes verify identity of
the retained bytes, not interpretation.

## Load-bearing compact matrix-group density locator

Printed pp. 355–356, proof of Theorem 12.18; PDF artifact pp. 362–363; extracted text lines
16345–16367:

- `A` is the space of continuous functions expressible as finite linear combinations of matrix
  entries of finite-dimensional representations of the compact matrix group `K`;
- products of entries are entries of tensor-product representations, which decompose into
  irreducibles;
- the trivial representation supplies nonzero constants;
- complex conjugates of entries are entries of dual representations;
- because `K` is a matrix Lie group, a faithful finite-dimensional representation exists by the
  convention used there, and its entries separate points;
- the complex Stone–Weierstrass theorem then makes `A` uniformly dense in the continuous functions.

PDF artifact pp. 362–363 were visually inspected against the extracted text. The source explicitly uses
the matrix-group hypothesis at this step and later notes that Appendix D sketches a route not
assuming it in advance. The present formalization therefore keeps a continuous faithful finite
complex matrix representation as explicit data and does not generalize this argument silently to
all compact Hausdorff groups. Exact representation-equivalence transport further places every
bundled irreducible-unitary coefficient into the finite synthesis range of the selected representative
of its quotient-dual class; an explicit one-dimensional trivial class supplies constants. Thus the
same conditional uniform-density result holds for the selected coordinate-dual synthesis itself.
Regularity of normalized compact Haar measure and Mathlib's density of continuous functions in
finite-measure `L²` derive conditional normalized-Haar `L²` coefficient completeness.
The selected synthesis range is also proved exactly equal to the earlier all-presentation finite
coefficient span, and its density is named as the reusable general continuous Peter–Weyl target.
Normalized-Haar regularity gives a general implication from that target to `L²` completeness. These
bridges are formal consequences, not separate quotations from Hall. Dense-range
Hilbert-space arguments further give arbitrarily accurate finite-support `L²` coefficient
approximants and uniqueness from all finite-support coefficient inner-product tests. These results
do not assert countability, a selected approximating sequence, or infinite Fourier inversion.

## Artifact chain

- `FETCH_TIMESTAMP.txt` records repository ingestion time.
- `SHA256SUMS.txt` covers the retained PDF and extraction.
