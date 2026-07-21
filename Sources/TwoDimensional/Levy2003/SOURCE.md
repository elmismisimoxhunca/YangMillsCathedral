# Source record

## Identity

- **Yang–Mills Measure on Compact Surfaces**.
- Author(s): Thierry Lévy.
- Publication: Memoirs of the AMS 166, no. 790 (2003); arXiv:math/0101239.
- Identifier: 10.1090/memo/0790.
- Retained PDF: `yang_mills_measure_compact_surfaces.pdf` (113 PDF pages).
- Exact native extraction: `yang_mills_measure_compact_surfaces.txt`, produced with `pdftotext -layout`.

## Audit role

Unified discrete/continuum construction, random holonomy, subdivision and area-preserving invariance, and surface-surgery Markov behavior.

## Ingestion and locator status

The PDF was supplied by the user in the 2026-07-19 literature bundle, signature-checked, copied
without byte changes, hash-manifested, and text-extracted. Ingestion does not by itself make every
statement load-bearing: exact printed-page/equation/theorem locators and any OCR-sensitive formulas
must be visually checked and entered in `docs/SUPPLIED_SOURCE_INGESTION_AUDIT.md` and
`docs/SOURCE_MAP.md` before supporting a canonical physical declaration. Hashes verify identity of
the retained bytes, not interpretation.

PDF pp. 24–27 / printed pp. 10–13 were independently inspected on 2026-07-21 for §1.6,
Theorem 1.6.1, Lemmas 1.6.2/1.6.3, and the beginning of the proof. The pages visibly define the
fine-to-coarse configuration map by coarse-edge holonomy along fine paths, state its surjectivity and
exact measure pushforward, decompose refinements into vertex insertion and edge addition, and state
strict composition `f₁₃ = f₁₂ ∘ f₂₃`. The proof visibly attributes composition to group
associativity and subdivision invariance to Haar invariance and the heat-kernel convolution
semigroup. The Lean layer constructs the word map and composition algebra, requires nonempty edge
carriers, endpoint coherence, literal equality of each coarse ambient path with its concatenated fine
word, and surjectivity; ambient-holonomy coherence is derived. Exact weighted-measure pushforward,
eligible-observable/ambient-observable coherence, and finite word-family equality in law are packaged
as uninhabited source-facing law data and consequences.

## Artifact chain

- `FETCH_TIMESTAMP.txt` records repository ingestion time.
- `SHA256SUMS.txt` covers the retained PDF and extraction.
