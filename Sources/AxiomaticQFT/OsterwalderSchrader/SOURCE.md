# Osterwalder–Schrader reconstruction source record

## Status

**Primary article scans acquired, signature-checked, text-extracted, and visually verified at the
load-bearing pages.**

The user supplied the scans under `/projects/`. Each retained `.pdf` begins with `%PDF-`, is
unencrypted, has the correct title, printed page range, journal header, and complete article text,
and was successfully processed by `pdfinfo`, `pdftotext`, and page rendering. Their byte identity
with a particular publisher download was not independently established, so they are described as
primary article scans rather than publisher-download bytes.

The earlier Jina Reader Markdown transformations remain retained as separately labelled search aids.
They are not primary artifacts and are not used for visual formula verification.

Direct unauthenticated requests to current Project Euclid `full.pdf` endpoints returned variable
roughly one-kilobyte HTML access-control pages. Those bytes were rejected rather than saved as PDFs.

## OS-I identity

- Konrad Osterwalder and Robert Schrader, **Axioms for Euclidean Green's Functions**.
- *Communications in Mathematical Physics* **31** (1973), 83–112.
- DOI: <https://doi.org/10.1007/BF01645738>.
- Project Euclid identity: `euclid.cmp/1103858969`.
- Article record:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/10.1007/BF01645738.full>.
- Retained primary scan: `os1_primary_scan.pdf` — 30 PDF pages.
- Reproducible text extraction: `os1_primary_scan.txt`, produced by `pdftotext -layout`.
- Retained transformed search aid: `os1_projecteuclid_reader.md`.

## OS-II correcting-source identity

- Konrad Osterwalder and Robert Schrader, **Axioms for Euclidean Green's Functions II**.
- *Communications in Mathematical Physics* **42** (1975), 281–305.
- DOI: <https://doi.org/10.1007/BF01608978>.
- Project Euclid identity: `euclid.cmp/1103899050`.
- Article record:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II/10.1007/BF01608978.full>.
- Retained primary scan: `os2_primary_scan.pdf` — 25 PDF pages.
- Reproducible text extraction: `os2_primary_scan.txt`, produced by `pdftotext -layout`.
- Retained transformed search aid: `os2_projecteuclid_reader.md`.

## Load-bearing verified locators

Printed journal pages are authoritative. Text line numbers below refer to the retained
`*_primary_scan.txt` files.

### OS-I

- Printed p. 86; `os1_primary_scan.txt` lines 151–190: the coincidence-flat space, the closed
  derivative-vanishing ordered spaces `S_{s,t}`, the positive ordered space `S₊ = S_{0,∞}`, their
  induced Schwartz topologies, and the distinct completed positive-half-space tensor product are
  defined. The formulas and topology distinctions were visually checked on PDF page 4. The current
  Lean Fréchet candidate models only `S₊`. It is internally equivalent to ordered tuples of the
  exact point/coordinate basis and, in four dimensions, to one canonical natural-valued multi-index
  presentation after proved multiplicity enumeration and permutation independence. The canonical
  repeated-coordinate derivative is now the formal interpretation of the printed `D^α` convention;
  exact positive-arity source membership is proved equivalent to the Fréchet presentation and
  closed in the induced Schwartz topology. OS-I's separately declared scalar zero-point sequence
  component is not identified with this subtype; a following algebraic source-sequence carrier keeps
  that scalar separate while combining finitely many exact positive-arity components. The
  componentwise map from the earlier strict-support sequence is exact; proper enlargement and
  sufficiency/density/completion remain open. Exact finite-stage products and their raw final
  topology are now constructed for the source sequence. A separately named Hausdorff locally convex
  final topology has compatible complex-module operations, exact continuous-linear finite-stage maps,
  and the finite-stage universal property for linear maps into real-locally-convex topological
  complex modules. Printed p. 87, `os1_primary_scan.txt` lines 200–210, states the direct-sum
  topology through continuity on each natural coordinate injection. The separate scalar injection
  and every positive-arity injection are now constructed, every finite stage is proved to be their
  exact finite sum, and the individual-injection continuity criterion is proved equivalent to
  continuity from the Hausdorff locally convex final topology. That topology is therefore the
  source-facing locally convex direct-sum topology. The raw topological final topology remains
  separately named and is not identified with it. A general completed projective tensor-product
  acceptance interface now records Hausdorff local convexity of both factors, additive-uniform
  completeness of the carrier, joint pure-tensor continuity, dense span, noncollapse, and
  same-universe extension with uniqueness derived from density. The exact negative-half-line
  Schwartz submodule is now proved closed, its membership is equivalent to nonpositive topological
  support, and the genuine Hausdorff real-locally-convex topological complex-module quotient
  `𝒮(ℝ₊)` has an explicit nonzero positive class.
  The neutral spatial `ℝ³` selected by four-dimensional spacetime and source-facing scalar-functional
  tensor candidate data for the factors `𝒮(ℝ₊)` and `𝒮(ℝ³)` are now defined; explicit nonzero
  factors force a nonzero pure tensor in any supplied candidate. The stronger arbitrary-target
  projective interface remains separate pending authoritative sourcing. A zero-based fixed-left-
  associated supplied family records analogous scalar-functional candidates at every intended
  finite positive power, with density-derived uniqueness and a recursively nonzero pure tensor.
  Scalar-valued lifts do not characterize the completed projective tensor topology. Quotient
  completeness, the printed seminorm presentation, Lean representation of the source's nuclearity
  statement, actual completed carriers/topologies, associativity/permutation equivalences, and
  product-Schwartz or OS-test identifications remain open; these candidate topologies remain
  separate by definition.
- Printed pp. 84–85: the original proposal lists `(E0)` temperedness, `(E1)` Euclidean covariance,
  `(E2)` positivity, `(E3)` symmetry, and `(E4)` cluster property.
- Printed pp. 87–88; `os1_primary_scan.txt` lines 237–277: the axioms and original `E → R` / `R → E`
  theorem claims are stated. The formulas and headings were visually checked on PDF pages 5–6.
- These sufficiency claims are **not** accepted uncorrected because OS-II explicitly reports the
  failure of OS-I Lemma 8.8.

### OS-II correction and replacement

- Printed p. 282; `os2_primary_scan.txt` lines 56–95: the authors state that OS-I Lemma 8.8 is wrong,
  that it is open whether OS-I `(E0)–(E4)` suffice for a Wightman theory, and give the separate-
  versus-joint-temperedness counterexample. This page was visually checked on PDF page 2.
- Printed p. 287, §IV.1; `os2_primary_scan.txt` lines 297–324: the paper defines factorial growth,
  the linear-growth condition `(E0′)` in equation (4.1), the stronger `(E0″)` in equation (4.2), and
  states the corrected reconstruction theorem. The formulas were visually checked on PDF page 7.
- The visually verified `(E0′)` condition requires `S₀ = 1`, each `Sₙ` in the indicated distribution
  space, a fixed order `s ∈ ℤ₊`, and a factorial-growth sequence `{σₙ}` such that
  `|Sₙ(f)| ≤ σₙ |f|ₙ,ₛ` for all positive `n` and coincidence-flat tests
  `f ∈ 𝒮₀(ℝ⁴ⁿ)`.
- The corrected theorem states that `(E0′)` (or `(E0″)`) together with `(E1)–(E4)` gives the Euclidean
  Green's functions of a uniquely determined Wightman quantum field theory satisfying `R0–R5` and
  an additional Wightman linear-growth condition `(R0′)`.

## Formalization decision

OS-II has correcting priority over OS-I. The checker must keep Euclidean/Schwinger data and
Minkowski/Wightman data as separate carriers connected by an explicit reconstruction bridge.
Reflection positivity, Euclidean covariance, symmetry, clustering, regularity/growth, Wightman
axioms, and reconstruction coherence must remain separately visible obligations. Algebraic `(E2)`
is now stated on finite sequences over the exact four-dimensional derivative-vanishing source
components: the source sequence is forgotten componentwise into the unrestricted Schwartz algebra
before evaluating `(Θ f*) × f`. Completed positive-half-space tensors, nuclearity, OS-II growth,
and reconstruction remain distinct obligations and are not prerequisites for this algebraic `(E2)`.
Exact source-carrier `(E4)` is likewise stated for every pair of source sequences and every normalized
nonzero spatial direction, using the printed reflected first factor, translated second factor, and
connected subtraction term. Printed p. 88 writes `a ∈ ℝ³`; excluding zero and normalizing its norm
is the project's explicit spatial-infinity/reparameterization convention, not verbatim source syntax.
This is a supplied requirement, not an exhibited clustering family.

The original OS-I sufficiency theorem must never be encoded using only ordinary temperedness. A
canonical reconstruction requirement must incorporate the OS-II-strength linear-growth condition
or another later authoritative theorem with every hypothesis explicit.

The scans now support `OSIICarrierExactLinearGrowthData`: equation (2.1)'s exact flattened
coordinate-square weighted multi-index control is specified by its least-upper-bound universal
property, and equation (4.1) is imposed on complex-linear functionals over the exact coincidence-flat
`𝒮₀` submodules using one positive order and factorial-growth sequence. A separate
`OSIIAmbientExtensionLinearGrowthData` retains extra full-Schwartz tempered extensions and restricts
canonically to carrier-exact data; no converse extension is claimed. Both remain separate from the
Mathlib-seminorm candidate. The scans do not
themselves provide a Yang–Mills model, prove existence, or justify identifying Euclidean and
Minkowski data definitionally.

## Artifact chain

- Acquisition/verification time: `FETCH_TIMESTAMP.txt`.
- `SHA256SUMS.txt` verifies both primary scans, their reproducible text extractions, and the two
  transformed reader artifacts.
- Duplicate `/projects/osterwalder1973 (1).pdf` was byte-identical to
  `/projects/osterwalder1973.pdf` and was not retained twice.
- Primary-scan SHA-256 values:
  - OS-I: `40c81d85a832452dde05bee6b601982488697aedf1a7be2fa2128279fd3c6182`.
  - OS-II: `36413586b83b491c8e0ef318e98d6e882619019826e62dc24daf898dc7f486ec`.
- Jina Reader inputs retained only as provenance for the transformed search aids:
  - <https://r.jina.ai/https://projecteuclid.org/download/pdf_1/euclid.cmp/1103858969>
  - <https://r.jina.ai/https://projecteuclid.org/download/pdf_1/euclid.cmp/1103899050>
