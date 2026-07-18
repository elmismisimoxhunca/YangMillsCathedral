# Clay/Jaffe–Witten source pin

## Identity

- Arthur Jaffe and Edward Witten, **Quantum Yang–Mills Theory**.
- Clay Mathematics Institute Millennium Prize problem description.
- Canonical artifact URL:
  <https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf>
- Independently retrieved from that URL at the UTC time in `FETCH_TIMESTAMP.txt`.
- Retrieval command: `curl --proto '=https' --tlsv1.2 -fL --retry 3`.
- The downloaded bytes were compared with the archaeological legacy copy before the legacy working
  tree was treated only as external evidence; both had the pinned PDF hash below.

## Retained artifacts

- `yangmills_official.pdf`: source of record; SHA-256
  `3558403ca14c11e382f73a09e548222708540bfdf478cf96aa11c52d43e23e09`.
- `yangmills_official.txt`: searchable extraction produced by
  `pdftotext -layout yangmills_official.pdf yangmills_official.txt`; SHA-256
  `da5105c9a42aeaadedcdb59274b74f432d21083cd50fe0912a6294f7bb4f4df7`.
- `SHA256SUMS.txt`: machine-readable manifest for both artifacts.

The extraction was reproduced byte-for-byte with Poppler `pdftotext` 25.03.0 during standalone
initialization. The PDF was independently downloaded from the canonical URL and compared
byte-for-byte with the pinned copy. A legacy HTML artifact was deliberately not imported after
review showed that it was a 404 response rather than source content.

## Load-bearing locators

Printed and PDF page locators below refer to the source-of-record artifact.

- PDF p. 2, equation (1), text lines 46–65: classical curvature, Yang–Mills equations, and
  Lagrangian `1/(4g²) ∫ Tr F ∧ ∗F`, with `Tr` identified as an invariant quadratic form on the
  Lie algebra of `G`.
- PDF p. 5, §3: Wightman framework, Poincaré representation, self-adjoint translation generators,
  vacuum, positive energy, covariance and locality.
- PDF p. 6, §4, text lines 263–271: local fields corresponding to gauge-invariant local
  polynomials in curvature and covariant derivatives; short-distance agreement with asymptotic
  freedom and perturbative renormalization; stress tensor; operator-product expansion; prescribed
  local singularities.
- PDF p. 6, §4, text lines 272–276: vacuum energy, nonnegative Hamiltonian spectrum, the open
  interval `(0, Δ)`, and finite supremal mass.
- PDF p. 6, §4, text lines 277–280: universal statement “for any compact simple gauge group G” and
  axiomatic properties at least as strong as references [45, 35].
- PDF p. 6, footnote 1, text lines 298–304: renormalization obstructs a natural one-to-one
  correspondence between classical differential polynomials and quantum fields. The future
  observable interface must therefore not claim a canonical syntactic bijection.

The exact searchable quotation begins near lines 262–280 of `yangmills_official.txt`. Text line
numbers are convenience locators; the PDF page is authoritative.

## Provenance limitations

The headline sentence is not the complete acceptance surface: the preceding §4 requirements and
its footnote are load-bearing. The Clay document also intentionally does not provide a formal
definition of every term, including the precise global-form convention for “compact simple gauge
group.” In equation (1), it says only that `Tr` is an invariant quadratic form; continuity, a
symmetric bilinear presentation, and positive definiteness are additional project formalization
requirements, with compact-representation evidence supplied separately by Hall Proposition 5.17.
Such choices must be recorded as formalization decisions supported by additional primary or
authoritative sources. They must not be silently attributed verbatim to Clay.

The current classical layer uses the conventional `1/2 * sum_ij` contraction in Mathlib's chosen
orthonormal basis for an explicitly supplied smooth Riemannian metric. A reusable canonical-tensor
theorem now proves basis independence for arbitrary bilinear maps and explicit bilinear codomain
pairings. The exact adjoint-fiber pairing is now packaged bilinearly; the degree-two dependent
adjoint-valued curvature adapter and identification with a general manifold Hodge star remain
pending. The current action
retains the outer coefficient `(4 * g^2)⁻¹`, requires strictly positive `g`, and integrates only when
the exact curvature scalar is integrable against an explicitly designated Borel measure. That
measure is not called Riemannian volume without a future compatibility theorem.
