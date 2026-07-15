# Binding project instructions

Read `README.md`, `docs/ARCHITECTURE.md`, and `docs/PROVENANCE.md` completely before editing.

This repository formalizes the Yang–Mills acceptance contract, never a solution. Do not introduce
`axiom` declarations or `sorry` in Lean source. Do not import proposed solution machinery from the
legacy Adaly repository. Do not depend on or preserve compatibility with
`LeanMillenniumPrizeProblems`.

Every physical field or predicate must be entered in the declaration-level source map before it is
made canonical. Missing general mathematics must be isolated as reusable infrastructure rather
than encoded as an arbitrary `Prop` or hidden assumption. Add hostile probes with every major
interface. Run the targeted Lean build, the complete build, the source verifier, the source-level
axiom/sorry audit, and `git diff --check` before committing.
