# Bounded checker completion audit

Audit date: 2026-07-25  
Branch: `cathedral`

> **Repository split note (2026-07-26).** This document records the pre-split audit, so its
> `checker/` paths are historical locators in Cathedral commit `3306ec3`. That exact tree now forms
> the separate `YangMills3DTruthTeller` repository and is tagged `truth-teller-import-3306ec3` there.

## Objective restated as concrete deliverables

1. Finish a bounded proof-carrying plug-in checker for a future 3D SU(2) construction without
   constructing or claiming continuum existence or a mass gap.
2. Expose exact dependent tiers, one authoritative strongest proposition, exact component
   decomposition, stable `PASS` / `INCOMPLETE` / `DIMENSION MISMATCH` diagnostics, hostile probes,
   and a conditional future-candidate guide/template.
3. Put every project module required by that checker into an independently buildable `checker/`
   package, with pinned Mathlib, exact reachable closure, source provenance, source/axiom audits,
   and no imports from frozen 2D, 4D, lattice, renormalization, or unrestricted Fourier tracks.
4. Use several Luna-backed scouts to compare the remaining general mathematics against pinned
   Mathlib and publish a conservative, dependency-ordered A/B/C extraction report.
5. Leave the strongest acceptance proposition explicitly uninhabited and report publication state
   honestly.

## Prompt-to-artifact checklist

| Requirement | Artifact / evidence | Coverage verdict |
|---|---|---|
| Exact literal SU(2) gauge target | `ThreeDimensionalSU2GaugeGroupData`, `SpecialUnitaryTwo`, continuous multiplicative equivalence, and gauge-group probes | Covered |
| Continuum rather than lattice/cutoff existence | `ThreeDimensionalSU2ContinuumExistenceData`; plug-in obligation `continuumWightmanExistence`; lattice-only incomplete probe | Covered as a supplied witness obligation; no existence theorem claimed |
| Identifying gauge-invariant Yang--Mills observables | Same covariant observable family, exact nonunit/nonzero curvature-squared interpretation, and hostile probes | Covered |
| Explicit Euclidean/Minkowski same-theory requirement | `ThreeDimensionalSU2SameTheoryData` stores the continuum tier, exact full correlators, relative analytic correlators, and strict Wick witness; disconnected-theory incomplete probe | Covered at the documented current strict-domain supplied-witness strength; no universal OS theorem claimed |
| Physical gap on reconstructed theory's same joint PVM | `physicalMassGap` is indexed by `sameTheory.continuum.wightmanSurface`; positivity and exact same-PVM projections | Covered |
| Nonvacuum spectral nonvacuity | `nonvacuum_spectrum_nonempty`; nonzero bounded positive-energy projection; vacuous-gap incomplete probe | Covered |
| Tiered obligations | Three dependent records plus seven named `ThreeDimensionalSU2PluginObligation` cases | Covered |
| One authoritative strongest gate | `ThreeDimensionalSU2ExistenceMassGapAcceptance := Nonempty (...)` | Covered and uninhabited |
| Exact component decomposition | `threeDimensionalSU2Acceptance_nonempty_iff_components` and probe `exact_component_decomposition` | Covered with one unchanged dependent same-theory witness |
| Proof-carrying success | `ThreeDimensionalSU2PluginReport.pass` requires strongest data; `acceptanceData?` returns data only in that case | Covered |
| Stable diagnostics | `.status` returns exactly `PASS`, `INCOMPLETE`, or `DIMENSION MISMATCH`; status probes compile | Covered; incomplete means not established, not false |
| Strict 2D/4D separation | exact index inequalities, 2D/4D mismatch reports, and no 3D-to-4D real-linear equivalence probe | Covered |
| Hostile anti-vacuity | SU(2) determinant/subgroup/quotient/topology probes; nontrivial field/`F²`; nonpositive and different-PVM gap probes; lattice/disconnected/vacuous/dimension plug-in probes | Covered |
| Future plug-in guide | `docs/THREE_DIMENSIONAL_SU2_PLUGIN_GUIDE.md`; standalone copy; `checker/CandidateTemplate.lean` | Covered; template is conditional on an explicit data parameter |
| Standalone directory | `checker/` with independent `lakefile.toml`, toolchain, manifest, root module, source closure, docs and scripts | Covered |
| Exact dependency closure | `checker/CHECKER_FILES.txt`; `checker/scripts/verify_checker.py` checks exact files, import resolution, root reachability and frozen-track exclusion | PASS: 114 project modules / 15,043 Lean lines |
| Byte-identical extraction snapshot | `scripts/verify_checker_snapshot.py` | PASS: all 114 modules match monorepo sources |
| Independence from legacy tree | `scripts/test_checker_independence.sh` temporarily hides root `YangMills/` and builds inside `checker/` | PASS: 3,271 jobs with legacy tree hidden |
| Standalone source provenance | `checker/docs/SOURCE_AUDIT.md`, retained primary artifacts, `checker/scripts/verify_sources.py` | PASS: 17 source manifests |
| Standalone source/axiom policy | closure verifier source scan plus `YangMills.Audit.audit_yang_mills_axioms` in `YangMillsChecker.lean` | PASS: no placeholders/project axiom declarations; 2,326 kernel-audited declarations |
| Frozen research tracks | closure verifier rejects 2D, 4D, lattice, renormalization paths/imports; unrestricted Fourier is absent from closure | Covered |
| Several Luna Mathlib scouts | Seven partitioned/global Luna reports under `docs/mathlib-audit/01`--`07`, then Luna final review `08` | Covered: eight Luna-backed review runs total |
| Concrete Mathlib report | `docs/MATHLIB_EXTRACTION_AUDIT.md` | Covered: pinned revision, A/B/C ranking, semantic duplicate correction, explicit nonproposals and PR sequence |
| No upstream overclaim | Audit states no PR was opened and maintainer approval/novelty is not established | Covered |
| Full monorepo compatibility | `lake build YangMills` after foundation refactor | PASS: 4,678 jobs; 16,723 kernel-audited declarations |
| Repository source policy | `python3 scripts/audit_lean.py` after adding extracted audit-module exception | PASS: 1,217 audited Lean files |
| Root source and bibliography integrity | `verify_sources.py`; `verify_audit_bibliography.py` | PASS: 39 source manifests; 36 DOI records |
| Diff hygiene | `git diff --check` | PASS |
| Publication state | `git remote -v` prints no remote; no PR has been opened; branch remains local `cathedral` | Explicitly unpublished |

## Verifier-coverage audit

The green signals have distinct scopes and are not treated as interchangeable:

- `verify_checker.py` proves syntactic source closure, reachability, frozen-track exclusion, and
  placeholder/project-axiom-declaration absence. It does not prove inhabitance or source adequacy.
- the standalone Lean build proves elaboration and runs the transitive kernel axiom audit. It does
  not construct any structure value.
- `verify_sources.py` verifies retained bytes and manifest completeness. It does not validate the
  mathematical interpretation of every citation; `SOURCE_AUDIT.md` records that interpretation and
  its limitations.
- hostile probes verify that selected invalid substitutions cannot pass the encoded types. They do
  not establish that every conceivable invalid scientific claim is decidable automatically.
- the Luna audit is an advisory pinned-tree comparison. It is not Mathlib maintainer review or PR
  acceptance.

## Non-inhabitation inspection

A repository-wide search for
`ThreeDimensionalSU2ExistenceMassGapAcceptance(Data)` finds only:

- the structure and proposition definitions;
- conditional projection/probe theorems whose strongest datum is an explicit parameter;
- the plug-in `pass` constructor and conditional `ofData` adapter;
- `CandidateTemplate`, where `candidateData` is explicitly a function parameter.

No declaration defines a closed `candidateData`, a closed strongest-tier value, or an unconditional
proof of the authoritative proposition. The checker and its documentation repeatedly state this
boundary.

## Residual limitations, accurately classified

- The strict Euclidean candidate plus explicit Wick witness is not a formalized universal corrected
  Osterwalder--Schrader reconstruction theorem.
- No accepted end-to-end 3D SU(2) continuum-existence-plus-gap theorem was located in the retained
  literature audit.
- The geometric carrier and all quantum/spectral witnesses remain future candidate obligations.
- No Mathlib submission has been prepared or accepted; the extraction report is a plan.

These are not omitted deliverables under the revised bounded objective. They are exactly the
mathematics that the uninhabited checker requires from a future construction.

## Completion conclusion

Every revised bounded deliverable is represented by a concrete artifact and directly checked by an
appropriate build, closure, source, kernel, bridge, dimension, or publication-state inspection. No
proxy signal is being used as evidence of existence or a mass gap. The bounded checker/extraction/
Mathlib-scout objective is complete, while the underlying 3D Yang--Mills construction remains
explicitly absent.
