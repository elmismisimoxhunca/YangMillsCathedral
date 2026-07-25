# Three-dimensional SU(2) plug-in checker

## Purpose

The checker validates evidence supplied by a future construction. It does **not** construct
three-dimensional SU(2) Yang--Mills and does **not** prove a mass gap. A failed or incomplete
submission means only **not established by that submission**, never mathematical falsity.

The authoritative proposition is
`YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptance`. A successful report must carry
one value of `ThreeDimensionalSU2ExistenceMassGapAcceptanceData`; there is no evidence-free `PASS`.

## Submission order

A candidate should construct witnesses in this order.

1. **Exact SU(2) gauge geometry**
   - Supply `ThreeDimensionalSU2GaugeGroupData`.
   - The carrier must have the required compact-simple Lie geometry and an explicit continuous
     multiplicative equivalence with literal
     `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
2. **Three-dimensional continuum and Yang--Mills identification**
   - Supply `ThreeDimensionalSU2ContinuumExistenceData` on the canonical coordinate carrier `ℝ³`.
   - Supply the classical connection, curvature certificate, action, and coordinate Lebesgue
     measure identity.
   - Supply a nontrivial Wightman field, full tempered correlators, and one coherent covariant local
     observable family.
   - Interpret the exact classical curvature-squared observable as a distinct nonzero scalar label
     in that same family.
   - A finite lattice, finite cutoff, or merely nonempty field carrier does not satisfy this tier.
3. **Euclidean-to-Minkowski same-theory witness**
   - Supply `ThreeDimensionalSU2SameTheoryData` containing the preceding continuum witness.
   - Supply the three-dimensional Schwinger family, strict Euclidean candidate, relative analytic
     correlators, and strict ordered Wick-continuation witness indexed by the same full correlators.
   - This is the checker's explicit current-strength reconstruction obligation. It does not pretend
     that the repository proves the universal corrected Osterwalder--Schrader theorem.
4. **Physical same-PVM mass gap**
   - Supply `ThreeDimensionalSU2ExistenceMassGapAcceptanceData`.
   - `physicalMassGap` is indexed by the Wightman surface already stored in the same-theory tier.
   - It requires a positive threshold, the exact vacuum projection at zero, subgap spectral
     exclusion, and a nonzero bounded positive-energy excitation projection on that unchanged joint
     translation PVM.
5. **Submit**
   - Call `ThreeDimensionalSU2PluginReport.ofData data`.
   - Its status is definitionally `"PASS"`, and `acceptanceData?` returns `some data`.

## Diagnostic outcomes

`ThreeDimensionalSU2PluginReport` has three proof-relevant cases:

- `pass data`: all strongest-tier witnesses are present;
- `incomplete missing nonempty`: named obligations are absent or not yet connected;
- `dimensionMismatch candidateDimension mismatch`: the supplied endpoint is not dimension three.

The stable labels are `PASS`, `INCOMPLETE`, and `DIMENSION MISMATCH`. `incomplete` is a diagnostic
report and is not a proof that the missing mathematics is impossible.

The named obligations are:

- `exactSU2GaugeGeometry`;
- `classicalThreeDimensionalYangMills`;
- `continuumWightmanExistence`;
- `gaugeInvariantObservableIdentification`;
- `euclideanMinkowskiSameTheory`;
- `sameJointPVMMassGap`;
- `nonvacuumSpectralSector`.

## Minimal adapter shape

A candidate adapter should remain conditional on its construction's actual witnesses:

```lean
import YangMills.Dimensions.ThreeDimensionalSU2PluginChecker

open YangMills.Dimensions

-- All carrier, bundle, field, and spectrum parameters and instances occur here.
variable (candidateData : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
  (fieldData := fieldData) (inner := inner) (connection := connection)
  (exterior := exterior) (curvatureCertificate := curvatureCertificate))

def candidateReport : ThreeDimensionalSU2PluginReport
    (fieldData := fieldData) (inner := inner) (connection := connection)
    (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  ThreeDimensionalSU2PluginReport.ofData candidateData
```

The checker repository intentionally contains no definition of `candidateData`.

## Hostile substitutions

The probe modules verify that the contract does not silently accept:

- a generic compact-simple group without literal SU(2) identification;
- determinant failure, a proper subgroup, a quotient kernel, or a discontinuous identification;
- a lattice-only or cutoff-only construction as continuum existence;
- a trivial Wightman field or unit-labelled curvature-squared observable;
- unrelated Euclidean and Minkowski correlator families;
- a nonpositive threshold;
- a gap on a different PVM;
- an empty nonvacuum spectral sector;
- a two- or four-dimensional endpoint;
- a linear identification of the 3D base with the 4D Clay carrier.

## Interpretation boundary

A green Lean build proves that the supplied dependent witnesses typecheck and that the audited
projections and hostile probes elaborate. It does not prove that any candidate exists, that the
literature establishes all witnesses, or that the contract is inhabited. Repository publication
must continue to state that the authoritative proposition is uninhabited.
