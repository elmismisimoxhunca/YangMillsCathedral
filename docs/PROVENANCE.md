# Provenance policy

## Authority order

1. Primary problem statement or original paper.
2. Correcting primary paper or authoritative erratum.
3. Authoritative monograph or review for conventions absent from the primary source.
4. Existing formalization or legacy code as non-authoritative implementation evidence.

A later correction takes precedence over an earlier superseded statement. In particular, any use
of Osterwalder–Schrader I reconstruction conditions must account for Osterwalder–Schrader II,
*Communications in Mathematical Physics* 42 (1975), 281–305,
<https://doi.org/10.1007/BF01608978>: p. 282 reports the failure of OS-I Lemma 8.8 and p. 287
states the strengthened linear-growth condition. Primary article scans, exact text extractions, and
earlier transformed Project Euclid reader artifacts now live under
`Sources/AxiomaticQFT/OsterwalderSchrader/`. The primary scans were signature-checked and the
load-bearing printed pp. 282 and 287 were visually verified. OS-II therefore has correcting priority
for every future reconstruction declaration.

## Required source record

Every source-critical declaration must have a ledger row containing:

- Lean declaration name;
- mathematical claim or definition;
- source identity and stable URL/DOI;
- exact page, section, theorem or equation locator;
- verbatim quotation only when visually verified;
- classification: definition, model requirement, derived theorem, bridge, or open debt;
- formalization decision and any strengthening/weakening;
- confidence and unresolved ambiguity;
- hostile probe that would fail if the requirement were removed or disconnected.

## Artifact chain

Pinned artifacts live under `Sources/`. Each directory contains an identity record, retrieval time
when known, hashes, and an honest status. HTML challenge pages or OCR extracts are never mislabeled
as primary PDFs. A secondary fallback remains labelled secondary.

`python3 scripts/verify_sources.py` verifies bytes, not interpretation. Human and mathematical
review remains required for source-to-declaration fidelity.

## Legacy integration ledger

A future `docs/LEGACY_INTEGRATION.md` records each accepted or rejected legacy declaration. Nothing
is accepted merely because it compiles. The initial legacy target and probes are untracked working
material in the old repository and therefore require explicit content hashes when first imported.

Initial archaeological hashes:

- `ClayStatement.lean`:
  `e10ac614a0742a4bf8533dab26ef225a7af99e06078699ea6238de01323851f6`
- `ClayStatementProbes.lean`:
  `82d5a9b784adcb645bf8f52c258e2a3728fb8881af77c189e68a15578a57c4fd`

These hashes identify the quarry snapshot; they do not certify correctness.
