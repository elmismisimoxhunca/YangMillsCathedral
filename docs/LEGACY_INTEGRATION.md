# Legacy integration ledger

The legacy Adaly target is archaeological input, not an implementation dependency or authority.
This ledger tracks every declaration considered for integration. A status of “pending” means no
new canonical declaration has been accepted.

## Quarry snapshot

External source location at project initialization:

```text
../legacy/formal/AdalyFormal/AdalyFormal/Target/ClayStatement.lean
../legacy/formal/AdalyFormal/AdalyFormal/Target/ClayStatementProbes.lean
```

The files were untracked in the legacy Git repository; content hashes therefore identify the exact
reviewed snapshot:

| File | SHA-256 |
|---|---|
| `ClayStatement.lean` | `e10ac614a0742a4bf8533dab26ef225a7af99e06078699ea6238de01323851f6` |
| `ClayStatementProbes.lean` | `82d5a9b784adcb645bf8f52c258e2a3728fb8881af77c189e68a15578a57c4fd` |

No new repository build depends on these paths.

## Initial disposition

| Legacy family | Initial finding | Status |
|---|---|---|
| `Spacetime4`, Euclidean/Minkowski forms | Useful explicit coordinate archaeology; fixed dimension and full Lorentz-isometry choices require replacement. | Pending independent rebuild |
| `PoincareRepresentation` | Stronger than the discarded prior-art implementation; full physical group/topology and translation semantics remain deficient. | Pending independent rebuild |
| `OperatorValuedDistribution` | Common dense domain, continuity and closability are valuable shapes. | Candidate after Wightman source pin |
| `SpectrumCondition`, `MassGap` | Bounded coordinate-generator and Hamiltonian surrogates are not canonical physical semantics. | Reject as canonical; retain as negative evidence |
| `SchwingerMoment`, `OSAxioms` | Tempered distributions, primary finite-sequence positivity and clustering are useful; exact OS-II topology and reconstruction need repair. | Candidate after OS source pin |
| `CompactSimpleGaugeGroupData` | Encodes compact nontrivial topological-group data but not compact-simple Lie-group semantics. | Reject |
| Wilson lattice structures | Valuable distinction between finite regulator and continuum bridge, but dimension and caller-supplied semantics require reconstruction. | Pending optional layer |
| `YangMillsContent` and curvature correlators | Attempts shared semantics but leaves several connections as witness fields. | Reject as canonical; mine probe ideas |
| `ClayYangMillsFor`, `ClayYangMills` | Correct universal direction but inherits every deficient brick. | Reject; final proposition rebuilt from new layers |
| `ClayStatementProbes` | Extensive anti-vacuity quarry. Each probe must be ported only with its repaired declaration and source rationale. | Candidate probe-by-probe |
| Legacy `M1`, cluster-expansion, Bessel and compute modules | Proposed solution machinery, not definition infrastructure. | Permanently out of scope |

## Rebuilt stone: compact-simple gauge-group semantics

| Item | Evidence |
|---|---|
| Legacy declaration | `CompactSimpleGaugeGroupData`, `ClayStatement.lean:850–859`, quarry hash `e10ac614a0742a4bf8533dab26ef225a7af99e06078699ea6238de01323851f6` |
| Legacy probe | `subsingleton_latticeGaugeGroup_blocked`, `ClayStatementProbes.lean:656–663`, quarry hash `82d5a9b784adcb645bf8f52c258e2a3728fb8881af77c189e68a15578a57c4fd` |
| Authoritative evidence | Clay p. 6 §4, text 277–280; Hall printed pp. 15, 16, 21 and 115; Aharony–Seiberg–Tachikawa printed pp. 1–2; exact locators are in `SOURCE_MAP.md` and the source identity records |
| Defect found | Legacy data proves only compact carrier, continuous multiplication/inversion, and `Nontrivial G`. It allows finite disconnected groups, compact abelian groups, non-Lie groups, and non-Hausdorff topologies; it does not certify finite-dimensional smooth structure or Lie-algebra simplicity. |
| New declaration | `YangMills.Geometry.CompactSimpleGaugeGroupData G E` in `YangMills/Geometry/LieGroup.lean` |
| Repair / shape change | Rebuilt rather than ported. The new type requires a Hausdorff second-countable finite-dimensional real `C∞` Lie group; fields require compactness, connectedness, carrier anti-vacuity, and simplicity of Mathlib's tangent `GroupLieAlgebra`. The global carrier `G` remains explicit, and neither abstract-group simplicity nor simple connectedness is imposed. This strictly strengthens and semantically changes the legacy record. |
| Hostile evidence | `noncompact_gaugeGroup_blocked`, `disconnected_gaugeGroup_blocked`, `subsingleton_gaugeGroup_blocked`, `abelian_groupLieAlgebra_blocked`, and `proper_nonzero_groupLieIdeal_blocked` isolate the repaired obligations. |
| Validation | Focused production/probe builds, complete `lake build`, all three source manifests, conservative Lean audit, kernel audit over 130 declarations, and `git diff --check` passed. Two independent read-only reviews reported no blockers. |
| Implementation commit | `beb6cbb` (`Define compact-simple gauge-group semantics`) |
| Residual debt | No concrete positive inhabitant is supplied; the missing `SU(n)` manifold/compactness/connectedness/tangent-simplicity chain remains reusable infrastructure work. The explicit `Nontrivial G` field remains until a reusable tangent-to-carrier theorem is available. |

The legacy declaration remains rejected as canonical. Only its universal-any-`G` direction and
anti-triviality intent were mined; no legacy code is imported.

## Required row format for accepted stones

Every future integration row must record:

1. legacy declaration and hash/line locator;
2. primary-source locator;
3. defect or ambiguity found;
4. new declaration and mathematical interpretation;
5. whether the new form strengthens, weakens or changes the legacy shape;
6. hostile probe and mutation it blocks;
7. build and axiom-audit evidence;
8. commit hash.
