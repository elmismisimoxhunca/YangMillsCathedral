# Osterwalder–Schrader reconstruction source record

## Status

**Provisional transformed full-text evidence; primary PDF bytes are not yet pinned.**

The two retained artifacts are full Markdown text extractions produced by Jina Reader from Project
Euclid's legacy PDF-download endpoints. They expose all printed pages and are useful for searchable
source review, but they are not the publisher PDF bytes and must not be described as primary PDFs.
No canonical Osterwalder–Schrader Lean declaration may rely on this directory alone. Direct PDF
acquisition, `%PDF-` signature checking, visual inspection, and byte hashing remain required.

Direct unauthenticated requests to the current Project Euclid `full.pdf` endpoints returned a
roughly one-kilobyte HTML access-control page in this environment; the response body can vary
between requests. Those bytes were inspected as HTML and
were deliberately not retained under a `.pdf` name. Springer PDF endpoints redirected through an
identity-provider flow and likewise yielded no verified PDF artifact.

## OS-I identity

- Konrad Osterwalder and Robert Schrader, **Axioms for Euclidean Green's Functions**.
- *Communications in Mathematical Physics* **31** (1973), 83–112.
- DOI: <https://doi.org/10.1007/BF01645738>.
- Project Euclid identity: `euclid.cmp/1103858969`.
- Current article record:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/10.1007/BF01645738.full>.
- Preferred primary PDF endpoint, not successfully retrieved here:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/10.1007/BF01645738.full.pdf>.
- Legacy endpoint used as the Jina Reader input:
  <https://projecteuclid.org/download/pdf_1/euclid.cmp/1103858969>.
- Retained transformed extraction: `os1_projecteuclid_reader.md`.

## OS-II correcting-source identity

- Konrad Osterwalder and Robert Schrader, **Axioms for Euclidean Green's Functions II**.
- *Communications in Mathematical Physics* **42** (1975), 281–305.
- DOI: <https://doi.org/10.1007/BF01608978>.
- Project Euclid identity: `euclid.cmp/1103899050`.
- Current article record:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II/10.1007/BF01608978.full>.
- Preferred primary PDF endpoint, not successfully retrieved here:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II/10.1007/BF01608978.full.pdf>.
- Legacy endpoint used as the Jina Reader input:
  <https://projecteuclid.org/download/pdf_1/euclid.cmp/1103899050>.
- Retained transformed extraction: `os2_projecteuclid_reader.md`.

## Load-bearing searchable locators

Line numbers below refer only to the retained transformed artifacts. Printed journal pages remain
the authoritative locators.

### OS-I

- Printed pp. 84–85; extraction lines 28–35: the original proposal lists `(E0)` temperedness,
  `(E1)` Euclidean covariance, `(E2)` positivity, `(E3)` symmetry, and `(E4)` cluster property.
- Printed pp. 87–88; extraction lines 119–143: the axioms and the original `E → R` / `R → E`
  theorem claims are stated.
- These sufficiency claims are **not** accepted uncorrected because OS-II explicitly reports the
  failure of OS-I Lemma 8.8.

### OS-II correction and replacement

- Printed p. 282; extraction lines 34–50: the authors state that OS-I Lemma 8.8 is wrong, that it is
  open whether OS-I `(E0)–(E4)` suffice for a Wightman theory, and that stronger sufficient
  conditions are introduced.
- Printed p. 282; extraction lines 48–50: the counterexample and distinction from the preliminary
  Erice condition are discussed.
- Printed p. 287, §IV.1; extraction lines 209–229: the paper introduces the linear-growth condition
  `(E0′)` and the slightly stronger `(E0″)`. The mathematical formula is OCR-degraded in the
  transformed artifact and must be transcribed only after visual verification of primary PDF bytes.
- Printed p. 287; extraction lines 231–239: the corrected reconstruction theorem states that
  `(E0′)` (or `(E0″)`) together with `(E1)–(E4)` yields a uniquely determined Wightman theory whose
  Wightman distributions satisfy `R0–R5` plus a linear-growth condition.

## Formalization decision

OS-II has correcting priority over OS-I. The checker must keep Euclidean/Schwinger data and
Minkowski/Wightman data as separate carriers connected by an explicit reconstruction bridge.
Reflection positivity, Euclidean covariance, symmetry, clustering, regularity/growth, Wightman
axioms, and reconstruction coherence must remain separately visible obligations.

The original OS-I sufficiency theorem must never be encoded using only ordinary temperedness. A
canonical reconstruction requirement must incorporate a visually verified OS-II-strength growth
condition or another later authoritative theorem with all hypotheses explicit.

No OS, Wightman, Euclidean-theory, or reconstruction declaration is introduced by this source-only
stone. Primary PDF acquisition and exact formula verification remain hard gates.

## Artifact chain

- Retrieval time: `FETCH_TIMESTAMP.txt`.
- `SHA256SUMS.txt` verifies the retained transformed Markdown bytes.
- Jina Reader URLs used:
  - <https://r.jina.ai/https://projecteuclid.org/download/pdf_1/euclid.cmp/1103858969>
  - <https://r.jina.ai/https://projecteuclid.org/download/pdf_1/euclid.cmp/1103899050>
- Transformation caveat: Jina Reader performed PDF-to-Markdown extraction. OCR errors are visible,
  including degraded mathematical symbols. The artifacts are search aids and correction evidence,
  not substitutes for the primary scans.
