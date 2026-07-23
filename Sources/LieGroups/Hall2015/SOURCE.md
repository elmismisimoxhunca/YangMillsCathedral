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

## Load-bearing compact-group normalization and density locators

Printed p. 352, Theorem 12.15; PDF artifact p. 359; extracted text lines 16159–16169:

- `dx` is explicitly the normalized left-invariant volume form on the compact group `K`.

PDF artifact p. 359 was visually inspected against the extracted normalization statement.

Printed pp. 355–356, proof of Theorem 12.18; PDF artifact pp. 362–363; extracted text lines
16345–16394:

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

The second half of printed p. 356 centralizes an approximant by
`h(x)=∫_K g(yxy⁻¹)dy`; because the target `f` is central, averaging preserves the uniform error.
Writing `g` as finite matrix blocks and applying Lemma 12.20 makes the averaged coefficient
matrices scalar, hence turns `h` into a finite character combination. The Lean structure
`CompactGroupCharacterCentralizationData` isolates the exact reusable content still needed from
this step: a continuous linear centralization map, identity on central functions, and an exact map
from every finite selected-dual coefficient synthesis to some finite selected-character synthesis.
The actual probability-Haar conjugation average is now constructed under explicit second
countability, proved continuous by Mathlib's compact parametric-integral theorem, central by right
Haar invariance, identity on central functions, norm-nonincreasing, surjective, and idempotent. This
constructs the first two fields of the bridge datum. The remaining calculation is now also proved:
`matrixCoefficientSynthesis ρ A = tr(ρ Aᵀ)` forces a transpose; conjugation averaging leaves the
existing Schur average of `Aᵀ`; normalized Schur trace evaluates it as
`dim(ρ)⁻¹ tr(A) I`. Direct-sum induction converts every finite selected coefficient synthesis to a
finite selected-character synthesis, constructing the full bridge datum. Therefore, under explicit
second countability, full continuous density implies central uniform and central `L²` completeness;
faithful finite matrix coordinates supply full density. From central density, a noncanonical
finite-support character approximant is selected at tolerance `1/(n+1)`; these approximants are
proved to converge uniformly and in normalized-Haar `L²`, matching Hall's stated sequence-level
conclusion. The finite character pairing is also transported to the actual `L²` carrier: every
selected character vector and analysis functional has norm one, analysis recovers finite synthesis
coordinates, and continuity proves that each approximant coordinate converges to the exact integral
`∫ conj(χ_q)f`. The whole selected character family is proved orthonormal in the actual `L²`
carrier; finite and unconditional Bessel bounds, square summability, vectorwise countable coefficient
support, and exact finite-range Parseval identities follow. Every finite selected-class set now also
has its genuine bounded orthogonal Fourier projection, with exact coordinate truncation,
idempotence, finite-support inversion, residual orthogonality, Pythagorean remainder, norm
contraction, and exact operator norm one when nonempty. This remains conditional only where
density/approximation is invoked and is not a Fourier partial-sum construction: it does not prove the
general compact-group Peter–Weyl theorem, global dual countability, an infinite synthesis/inversion
identity, or convergence of a canonically ordered Fourier series.

## Artifact chain

- `FETCH_TIMESTAMP.txt` records repository ingestion time.
- `SHA256SUMS.txt` covers the retained PDF and extraction.
