# Verified status

This file records evidence for the current checkout. It is not a roadmap and does not infer
physical adequacy from compilation.

## 2026-07-15 — standalone initialization

Verified:

- Repository initialized independently on branch `cathedral`.
- Lean toolchain pinned to `leanprover/lean4:v4.31.0`.
- Mathlib input pinned to `v4.31.0`; `lake-manifest.json` resolves it to
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `lake build` completed successfully for the root library.
- The Clay PDF was independently downloaded from its canonical URL and matched the pinned bytes;
  Poppler 25.03.0 reproduced the searchable extraction byte-for-byte.
- Clay source manifest verified the PDF and text extraction. A legacy 404 HTML response was
  deliberately excluded.
- Conservative source audit found no proof placeholder or axiom-like project declaration.
- The root build ran `Lean.collectAxioms` over every loaded `YangMills` declaration and found no
  transitive `sorryAx` or project-defined axiom.
- Mutation checks confirmed rejection of source corruption, unmanifested artifacts, unsafe/control
  manifest paths, symlinks, proof placeholders, elaborated `sorryAx` dependencies and project
  axioms.
- The retired `LeanMillenniumPrizeProblems` clone is absent and is not a dependency.

## 2026-07-15 — first mathematical stone: dimensions

Verified:

- `EuclideanDimension` admits exactly natural dimensions one through four.
- The four named dimensions have spatial arithmetic `0`, `1`, `2`, and `3` respectively, without
  asserting reconstruction.
- Mathlib Euclidean spacetime carriers have the declared real finrank.
- Hostile probes reject zero, values above four, equality of dimensions two and four, and a linear
  equivalence between their spacetime carriers.
- The complete build imports the production module and probes before running the kernel axiom
  audit.

Not yet achieved:

- No signature, gauge-geometry, quantum-theory, acceptance, existence, or mass-gap declaration
  exists.
- No Yang–Mills acceptance declaration exists.
- No standalone Git remote exists or has been pushed. The tested candidate
  `git@github.com:elmismisimoxhunca/lean-yangmills-adaly.git` does not exist, and the available SSH
  credential was scoped to the retired repository. Local commits can proceed; remote publication
  remains an explicit infrastructure blocker.
- Only the Clay source is pinned in the new repository. All additional sources remain to be
  independently acquired and verified.

The absence of an acceptance declaration is intentional at initialization: no placeholder theorem
or arbitrary structure is introduced merely to make the project appear advanced.
